from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
from typing import Dict, List, Optional, Tuple

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "week5"))
sys.path.append(str(ROOT / "week9"))

try:
    import parser as week5_parser  # type: ignore
except ImportError:
    week5_parser = None

try:
    import disjunctive_invariants as dinv
except ImportError:
    dinv = None

try:
    import week9.bool_linear_invariants as linv  # fallback for synthesis if needed
except ImportError:
    linv = None


# Summary loading

def _normalize_summary(raw: Dict) -> Dict:
    if dinv and hasattr(dinv, "adapt_method_summary"):
        try:
            return dinv.adapt_method_summary(raw)  # type: ignore[attr-defined]
        except Exception:
            return raw or {}
    return raw or {}


def load_method_summary(src_path: pathlib.Path, summary_path: Optional[pathlib.Path]) -> Dict:
    if summary_path is not None:
        try:
            raw = json.loads(summary_path.read_text(encoding="utf-8"))
            return _normalize_summary(raw)
        except Exception:
            print("[week10 auto-verify] Warning: failed to read summary JSON, continuing without it.")
            return {}

    if week5_parser is not None:
        try:
            raw = week5_parser.run_parser(str(src_path))  # type: ignore[attr-defined]
            return _normalize_summary(raw)
        except Exception as e:
            print(f"[week10 auto-verify] Warning: Week 5 parser failed: {e}")
            return {}

    return {}


# Invariant synthesis

def synthesize_invariants(
    src: str,
    method_summary: Dict,
    use_boolean: bool = True,
) -> Tuple[List[str], Dict]:
    """Produce DNF strings for the first loop."""
    if dinv is None:
        return [], method_summary

    result = dinv.synthesize_disjunctive_invariants_for_method(
        src,
        method_summary,
        use_boolean=use_boolean,
    )

    loops = result.get("loops", [])
    invariants: List[str] = []
    if loops:
        inv_sets = loops[0].get("disjunctive_invariants", [])
        for entry in inv_sets:
            dnf = entry.get("dnf")
            if isinstance(dnf, str):
                invariants.append(dnf)

    if invariants:
        return invariants, result

    # fallback: try week 9 directly if nothing found
    if linv is not None:
        try:
            if use_boolean and hasattr(linv, "synthesize_boolean_dnf_invariant_for_loop"):
                fallback = linv.synthesize_boolean_dnf_invariant_for_loop(src, method_summary)
            else:
                fallback = linv.synthesize_linear_invariants_for_loop(src, method_summary)
            return fallback or [], result
        except Exception:
            pass

    return [], result


# Loop insertion

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
        print("[week10 auto-verify] Warning: No while-loop found to attach invariants.")
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


# Dafny runner

def run_dafny_verify(dafny_cmd: str, file_path: pathlib.Path) -> int:
    cmd = [dafny_cmd, str(file_path)]
    print(f"[week10 auto-verify] Running: {' '.join(cmd)}")
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
        print(f"[week10 auto-verify] ERROR: Dafny command not found: {dafny_cmd}")
        return 1


# CLI

def main():
    ap = argparse.ArgumentParser(
        description=(
            "Week 10 auto-verify: synthesize disjunctive (DNF) invariants, "
            "inject them into Dafny while-loops, optionally run Dafny."
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
        "--linear",
        action="store_true",
        help="Use linear invariants only (skip Boolean DNF search).",
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

    invariants, method_info = synthesize_invariants(
        src,
        method_summary,
        use_boolean=(not args.linear),
    )

    if invariants:
        print("[week10 auto-verify] Synthesized invariants:")
        for inv in invariants:
            print("   ", inv)
        new_src = insert_invariants_into_loop(src, method_info, invariants)
    else:
        print("[week10 auto-verify] No invariants synthesized; leaving file unchanged.")
        new_src = src

    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.write_text(new_src, encoding="utf-8")
        print(f"[week10 auto-verify] Wrote instrumented file to {out_path}")
        target = out_path
    else:
        print(new_src)
        target = src_path

    if args.run_dafny:
        if args.out:
            run_dafny_verify(args.dafny, target)
        else:
            print(
                "[week10 auto-verify] Note: running Dafny on original file since no --out was given. "
                "To verify the file with inserted invariants, use --out."
            )
            run_dafny_verify(args.dafny, target)


if __name__ == "__main__":
    main()
