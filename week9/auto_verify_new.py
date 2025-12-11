from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
from typing import Dict, List, Optional

ROOT = pathlib.Path(__file__).resolve().parent.parent

sys.path.append(str(ROOT / "week5"))
sys.path.append(str(ROOT / "week6"))
sys.path.append(str(ROOT / "week9"))

try:
    import parser as week5_parser  
except ImportError:
    week5_parser = None

try:
    import bool_linear_invariants as linv  
except ImportError:
    try:
        import linear_invariants as linv  
    except ImportError:
        sys.stderr.write(
            "[auto_verify_new] ERROR: Could not import 'bool_linear_invariants' or 'linear_invariants'.\n"
        )
        sys.exit(1)


def _normalize_summary(raw: Dict) -> Dict:
    if hasattr(linv, "adapt_method_summary"):
        try:
            return linv.adapt_method_summary(raw)  
        except Exception:
            return raw
    return raw


def load_method_summary(src_path: pathlib.Path, summary_path: Optional[pathlib.Path]) -> Dict:
    if summary_path is not None:
        try:
            raw = json.loads(summary_path.read_text(encoding="utf-8"))
            return _normalize_summary(raw)
        except Exception:
            return {}

    if week5_parser is not None:
        try:
            raw = week5_parser.run_parser(str(src_path))  # type: ignore
            return _normalize_summary(raw)
        except Exception:
            return {}

    return {}


def load_invariants(src: str, method_summary: Dict, use_boolean: bool = True) -> List[str]:
    pre = method_summary.get("synthesized_invariants")
    if isinstance(pre, list) and all(isinstance(s, str) for s in pre):
        return pre

    if use_boolean and hasattr(linv, "synthesize_boolean_dnf_invariant_for_loop"):
        invs = linv.synthesize_boolean_dnf_invariant_for_loop(src, method_summary)  # type: ignore
        if invs:
            return invs

    if hasattr(linv, "synthesize_linear_invariants_for_loop"):
        invs = linv.synthesize_linear_invariants_for_loop(src, method_summary)  # type: ignore
        if invs:
            return invs

    return []


# add support: while (cond) { ... }  OR  while cond { ... }
WHILE_RE = re.compile(
    r"while\s*"
    r"(?:\((?P<cond_paren>[^)]*)\)|(?P<cond_noparen>[^{]*?))"
    r"\s*(?P<brace>\{)",
    re.DOTALL,
)


def _cond_text_from_match(m: re.Match) -> str:
    return (m.group("cond_paren") or m.group("cond_noparen") or "").strip()


def find_loop_for_insertion(src: str, method_summary: Dict) -> Optional[re.Match]:
    code = src
    loops = method_summary.get("loops", [])

    # Try to match by condition from summary if available
    if loops:
        cond = (loops[0].get("condition") or "").strip()
        if cond:
            for m in WHILE_RE.finditer(code):
                if _cond_text_from_match(m) == cond:
                    return m

    # Fallback
    return WHILE_RE.search(code)


def insert_invariants_into_loop(
    src: str,
    method_summary: Dict,
    invariants: List[str],
) -> str:
    if not invariants:
        return src

    m = find_loop_for_insertion(src, method_summary)
    if not m:
        return src

    brace_pos = m.start("brace")

    line_start = src.rfind("\n", 0, m.start())
    if line_start == -1:
        line_start = 0
    else:
        line_start += 1
    while_indent = src[line_start:m.start()]
    inv_indent = while_indent + "  "

    inv_block = ""
    for inv in invariants:
        inv = inv.strip()
        if not inv:
            continue
        if "||" in inv and not (inv.startswith("(") and inv.endswith(")")):
            inv = f"({inv})"
        inv_block += f"\n{inv_indent}invariant {inv}"

    return src[:brace_pos] + inv_block + src[brace_pos:]


def run_dafny_verify(dafny_cmd: str, file_path: pathlib.Path) -> Dict[str, object]:
    cmd = [dafny_cmd, str(file_path)]
    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        return {
            "command": cmd,
            "returncode": result.returncode,
            "output": result.stdout,
        }
    except FileNotFoundError:
        return {
            "command": cmd,
            "returncode": 1,
            "output": f"ERROR: Dafny command not found: {dafny_cmd}",
        }


def main():
    ap = argparse.ArgumentParser(
        description=(
            "Week 9 auto-verify: synthesize Boolean (DNF) and/or linear invariants, "
            "inject into Dafny while-loops, optionally run Dafny, and output JSON."
        )
    )
    ap.add_argument("file", help="Input Dafny (.dfy) file")
    ap.add_argument(
        "--summary",
        help="Optional Week 5 JSON summary file (if omitted, tries to run parser).",
    )
    ap.add_argument(
        "--out",
        help="Write instrumented Dafny to this file. If omitted, file is not written.",
    )
    ap.add_argument(
        "--bool",
        action="store_true",
        help="Force Boolean DNF synthesis (if available).",
    )
    ap.add_argument(
        "--no-bool",
        action="store_true",
        help="Disable Boolean DNF; use only linear invariants.",
    )
    ap.add_argument(
        "--run-dafny",
        action="store_true",
        help="After inserting invariants, run Dafny on the output file (or original if no --out).",
    )
    ap.add_argument(
        "--dafny",
        default="dafny",
        help="Dafny executable/command to use with --run-dafny.",
    )

    args = ap.parse_args()

    src_path = pathlib.Path(args.file)
    src = src_path.read_text(encoding="utf-8")

    summary_path = pathlib.Path(args.summary) if args.summary else None
    method_summary = load_method_summary(src_path, summary_path)

    use_boolean = True
    if args.no_bool:
        use_boolean = False
    if args.bool:
        use_boolean = True

    invariants = load_invariants(src, method_summary, use_boolean=use_boolean)

    if invariants:
        instrumented = insert_invariants_into_loop(src, method_summary, invariants)
    else:
        instrumented = src

    out_file_path: Optional[pathlib.Path] = None
    if args.out:
        out_file_path = pathlib.Path(args.out)
        out_file_path.write_text(instrumented, encoding="utf-8")

    dafny_result: Optional[Dict[str, object]] = None
    if args.run_dafny:
        target = out_file_path if out_file_path is not None else src_path
        dafny_result = run_dafny_verify(args.dafny, target)

    result_json = {
        "file": str(src_path),
        "used_boolean": use_boolean,
        "invariants": invariants,
        "out_file": str(out_file_path) if out_file_path is not None else None,
        "ran_dafny": args.run_dafny,
        "dafny": dafny_result,
    }
    print(json.dumps(result_json, indent=2))


if __name__ == "__main__":
    main()
