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
    import parser as week5_parser  # type: ignore
except ImportError:
    week5_parser = None

try:
    import week9.bool_linear_invariants as linv  
except ImportError:
    try:
        import linear_invariants as linv  
    except ImportError:
        print(
            "[auto_verify_new] ERROR: Could not import 'linear_invariants_new' or 'linear_invariants'.\n"
            "Make sure one of these files exists and is in week9/ or week6/."
        )
        sys.exit(1)



# Load method summary


def _normalize_summary(raw: Dict) -> Dict:
    """Normalize Week 5 outputs into the single-method shape linv expects."""
    if hasattr(linv, "adapt_method_summary"):
        try:
            return linv.adapt_method_summary(raw)  # type: ignore[attr-defined]
        except Exception:
            return raw
    return raw


def load_method_summary(src_path: pathlib.Path, summary_path: Optional[pathlib.Path]) -> Dict:
    """
    Load JSON summary from Week 5, or run parser if available.
    If both fail, return {} and let the synthesizer fall back
    to syntactic loop detection.
    """
    if summary_path is not None:
        try:
            raw = json.loads(summary_path.read_text(encoding="utf-8"))
            return _normalize_summary(raw)
        except Exception:
            print("[auto_verify_new] Warning: failed to read summary JSON, continuing without it.")
            return {}

    if week5_parser is not None:
        try:
            raw = week5_parser.run_parser(str(src_path))  
            return _normalize_summary(raw)
        except Exception as e:
            print(f"[auto_verify_new] Warning: Week 5 parser failed: {e}")
            return {}

    return {}



# invariant loading 


def load_invariants(src: str, method_summary: Dict, use_boolean: bool = True) -> List[str]:
    # 1 Use precomputed, if any.
    pre = method_summary.get("synthesized_invariants")
    if isinstance(pre, list) and all(isinstance(s, str) for s in pre):
        return pre

    # 2 Week 9 Boolean DNF 
    if use_boolean and hasattr(linv, "synthesize_boolean_dnf_invariant_for_loop"):
        invs = linv.synthesize_boolean_dnf_invariant_for_loop(src, method_summary)
        if invs:
            return invs

    # 3 Fallback: Week 6 linear invariants
    if hasattr(linv, "synthesize_linear_invariants_for_loop"):
        invs = linv.synthesize_linear_invariants_for_loop(src, method_summary)
        if invs:
            return invs

    return []



# Insert invariants into Dafny loop

WHILE_RE = re.compile(
    r"while\s*\((?P<cond>.*?)\)\s*(?P<brace>\{)",
    re.DOTALL,
)

def find_loop_for_insertion(src: str, method_summary: Dict) -> Optional[re.Match]:

    code = src
    loops = method_summary.get("loops", [])

    if loops:
        cond = (loops[0].get("condition") or "").strip()
        if cond:
            for m in WHILE_RE.finditer(code):
                c = m.group("cond").strip()
                if c == cond:
                    return m

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
        print("[auto_verify_new] Warning: No while-loop found to attach invariants.")
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
        if inv:
            if "||" in inv and not (inv.startswith("(") and inv.endswith(")")):
                inv = f"({inv})"
            inv_block += f"\n{inv_indent}invariant {inv}"

    return src[:brace_pos] + inv_block + src[brace_pos:]


#dafny runner

def run_dafny_verify(dafny_cmd: str, file_path: pathlib.Path) -> int:

    cmd = [dafny_cmd, str(file_path)]
    print(f"[auto_verify_new] Running: {' '.join(cmd)}")
    try:
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        print(result.stdout)
        return result.returncode
    except FileNotFoundError:
        print(f"[auto_verify_new] ERROR: Dafny command not found: {dafny_cmd}")
        return 1

# CLI
def main():
    ap = argparse.ArgumentParser(
        description=(
            "Week 9 auto-verify: synthesize Boolean (DNF) and/or linear invariants, "
            "inject into Dafny while-loops, optionally run Dafny."
        )
    )
    ap.add_argument("file", help="Input Dafny (.dfy) file")
    ap.add_argument(
        "--summary",
        help="Optional Week 5 JSON summary file (if omitted, tries to run parser).",
    )
    ap.add_argument(
        "--out",
        help="Write instrumented Dafny to this file. If omitted, print to stdout.",
    )
    ap.add_argument(
        "--no-bool",
        action="store_true",
        help="Disable Boolean DNF synthesis; use only linear invariants.",
    )
    ap.add_argument(
        "--run-dafny",
        action="store_true",
        help="After inserting invariants, run Dafny on the output.",
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

    # 1) synthesize invariants
    invariants = load_invariants(src, method_summary, use_boolean=not args.no_bool)

    if invariants:
        print("[auto_verify_new] Synthesized invariants:")
        for inv in invariants:
            print("   ", inv)
        new_src = insert_invariants_into_loop(src, method_summary, invariants)
    else:
        print("[auto_verify_new] No invariants synthesized; leaving file unchanged.")
        new_src = src

    # 2) output
    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.write_text(new_src, encoding="utf-8")
        print(f"[auto_verify_new] Wrote instrumented file to {out_path}")
        target = out_path
    else:
        print(new_src)
        target = src_path  # if they also asked to run Dafny, it's on original

    # 3)run dafny (optional)
    if args.run_dafny:
        if args.out:
            run_dafny_verify(args.dafny, target)
        else:
            print(
                "[auto_verify_new] Note: running Dafny on original file since no --out was given. "
                "To verify the file with inserted invariants, use --out."
            )
            run_dafny_verify(args.dafny, target)


if __name__ == "__main__":
    main()
