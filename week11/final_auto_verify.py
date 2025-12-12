from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
from typing import Dict, List, Optional

ROOT = pathlib.Path(__file__).resolve().parent.parent

# put week9/10/11 on the path so we can import their modules directly
sys.path.append(str(ROOT / "week9"))
sys.path.append(str(ROOT / "week10"))
sys.path.append(str(ROOT / "week11"))

# week 9: boolean + linear invariants
try:
    import bool_linear_invariants as linv  # type: ignore
except ImportError:
    linv = None

# week 10: qisjunctive invariants
try:
    import disjunctive_invariants as dinv  # type: ignore
except ImportError:
    dinv = None

# week 11: quadratic invariants
try:
    import quadratic_invariants as qinv  # type: ignore
except ImportError:
    qinv = None


DEFAULT_STRATEGIES = [
    "quadratic",
    "disjunctive-linear",
    "boolean",
    "linear",
]

#  loop finding & insertion
WHILE_RE = re.compile(
    r"while\s*"
    r"(?:\((?P<cond_paren>[^)]*)\)|(?P<cond_noparen>[^{]*?))"
    r"\s*(?P<brace>\{)",
    re.DOTALL,
)


def find_first_while(src: str) -> Optional[re.Match]:
    """Return the first while-loop match in the source."""
    return WHILE_RE.search(src)


def insert_invariants_into_first_loop(src: str, invariants: List[str]) -> str:
    """Insert invariant before the first loop body brace."""
    clean_invs: List[str] = []
    seen = set()
    for inv in invariants:
        inv = (inv or "").strip()
        if not inv:
            continue
        if inv in seen:
            continue
        seen.add(inv)
        if "||" in inv and not (inv.startswith("(") and inv.endswith(")")):
            inv = f"({inv})"
        clean_invs.append(inv)

    if not clean_invs:
        return src

    m = find_first_while(src)
    if not m:
        return src

    brace_pos = m.start("brace")

    # indentation of the while line
    line_start = src.rfind("\n", 0, m.start())
    if line_start == -1:
        line_start = 0
    else:
        line_start += 1
    while_indent = src[line_start:m.start()]
    inv_indent = while_indent + "  "

    inv_block = "".join(f"\n{inv_indent}invariant {inv}" for inv in clean_invs)
    return src[:brace_pos] + inv_block + src[brace_pos:]


# strategy implementation

def synthesize_with_strategy(
    strategy: str,
    src: str,
    src_path: pathlib.Path,
    args,
):
    """Synthesize invariants for src using the given strategy."""
    name = strategy.lower()

    # ----- quadratic -----
    if name == "quadratic" and qinv is not None:
        coeff_range = getattr(qinv, "COEFF_RANGE", range(-2, 3))
        const_range = getattr(qinv, "CONST_RANGE", range(-6, 7))
        if getattr(args, "quad_coeff_range", None):
            lo, hi = args.quad_coeff_range
            coeff_range = range(lo, hi + 1)
        if getattr(args, "quad_const_range", None):
            lo, hi = args.quad_const_range
            const_range = range(lo, hi + 1)

        q_kwargs = {
            "coeff_range": coeff_range,
            "const_range": const_range,
            "max_invariants": args.max_quadratic,
            "max_terms": args.max_terms,
            "max_candidates": args.max_candidates,
        }

        q_res = qinv.synthesize_quadratic_invariants_for_file(
            src_path,
            summary_json=None,
            **q_kwargs,
        )
        methods = q_res.get("methods") or []
        invs: List[str] = []
        if methods:
            m0 = methods[0]
            loops = m0.get("loops") or []
            if loops:
                invs = [
                    s.strip()
                    for s in loops[0].get("quadratic_invariants", [])
                    if isinstance(s, str) and s.strip()
                ]
        return invs, {"engine": "quadratic", "raw": q_res}

    # disjunctive linear 
    if name == "disjunctive-linear" and dinv is not None:
        d_res = dinv.synthesize_disjunctive_invariants_for_file(
            src_path,
            summary_json=None,
            use_boolean=False,
        )
        methods = d_res.get("methods") or []
        invs: List[str] = []
        if methods:
            m0 = methods[0]
            loops = m0.get("loops") or []
            if loops:
                for entry in loops[0].get("disjunctive_invariants", []):
                    dnf = entry.get("dnf")
                    if isinstance(dnf, str) and dnf.strip():
                        invs.append(dnf.strip())
        return invs, {"engine": "disjunctive-linear", "raw": d_res}

    # boolean (Week 9) 
    if name == "boolean" and linv is not None:
        invs = linv.synthesize_boolean_dnf_invariant_for_loop(src, {})  # type: ignore
        return invs or [], {"engine": "boolean"}

    # linear (Week 6)
    if name == "linear" and linv is not None:
        invs = linv.synthesize_linear_invariants_for_loop(src, {})  # type: ignore
        return invs or [], {"engine": "linear"}

    # strategy unavailable
    return [], {"engine": name, "error": "strategy unavailable"}


# dafny runner

def run_dafny(dafny_cmd: str, target: pathlib.Path) -> Dict[str, object]:
    cmd = [dafny_cmd, str(target)]
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


# per-file processing

def process_file(
    src_path: pathlib.Path,
    strategies: List[str],
    args,
) -> Dict[str, object]:
    src = src_path.read_text(encoding="utf-8")

    variants: List[Dict[str, object]] = []

    for strat in strategies:
        invs, details = synthesize_with_strategy(
            strat,
            src,
            src_path,
            args,
        )
        if not invs:
            continue

        instrumented = insert_invariants_into_first_loop(src, invs)

        target_dir = pathlib.Path(args.out_dir) / src_path.stem
        target_dir.mkdir(parents=True, exist_ok=True)
        out_file = target_dir / f"{src_path.stem}__{strat}.dfy"
        out_file.write_text(instrumented, encoding="utf-8")

        dafny_result = None
        if not args.skip_dafny:
            dafny_result = run_dafny(args.dafny, out_file)

        variants.append(
            {
                "strategy": strat,
                "invariants": invs,
                "out_file": str(out_file),
                "dafny": dafny_result,
                "details": details,
            }
        )

    return {
        "file": str(src_path),
        "variants": variants,
    }


# CLI 

def collect_inputs(args) -> List[pathlib.Path]:
    paths: List[pathlib.Path] = []
    if args.files:
        for item in args.files:
            p = pathlib.Path(item)
            if p.is_dir():
                paths.extend(sorted(p.glob("*.dfy")))
            else:
                paths.append(p)
    else:
        base = pathlib.Path(args.input_dir)
        paths.extend(sorted(base.glob("*.dfy")))
    return paths


def parse_strategy_list(raw: Optional[str]) -> List[str]:
    if not raw:
        return DEFAULT_STRATEGIES
    return [s.strip() for s in raw.split(",") if s.strip()]


def main():
    ap = argparse.ArgumentParser(
        description="Final auto-verify: synthesize (quadratic / disjunctive-linear / boolean / linear) invariants, inject, and optionally run Dafny.",
    )
    ap.add_argument("--input-dir", default="week3", help="Directory of .dfy files to process (default: week3)")
    ap.add_argument("files", nargs="*", help="Explicit .dfy files or directories to process")
    ap.add_argument("--out-dir", default="final_outputs", help="Where to write instrumented Dafny files and reports")
    ap.add_argument("--dafny", default="dafny", help="Dafny command to run when --skip-dafny is not set")
    ap.add_argument("--skip-dafny", action="store_true", help="Do not run Dafny on generated files")
    ap.add_argument("--strategies", help="Comma-separated strategy order (default: quadratic,disjunctive-linear,boolean,linear)")

    # quadratic tuning 
    ap.add_argument("--max-quadratic", type=int, default=6, help="Max quadratic invariants to emit (default: 6)")
    ap.add_argument("--max-terms", type=int, default=3, help="Max non-zero terms in quadratic search (default: 3)")
    ap.add_argument("--max-candidates", type=int, default=20000, help="Quadratic candidate cap (default: 20000)")
    ap.add_argument("--quad-coeff-range", nargs=2, type=int, metavar=("LOW", "HIGH"),
                    help="Inclusive quadratic coefficient range for a..e (default: -2 2)")
    ap.add_argument("--quad-const-range", nargs=2, type=int, metavar=("LOW", "HIGH"),
                    help="Inclusive quadratic constant term range (default: -6 6)")

    args = ap.parse_args()

    strategies = parse_strategy_list(args.strategies)
    inputs = collect_inputs(args)

    out_root = pathlib.Path(args.out_dir)
    out_root.mkdir(parents=True, exist_ok=True)

    report_path = out_root / "report.json"
    report: List[Dict[str, object]] = []

    for path in inputs:
        if not path.exists():
            report.append({"file": str(path), "error": "not found"})
            continue
        if path.is_dir():
            for sub in sorted(path.glob("*.dfy")):
                report.append(process_file(sub, strategies, args))
        else:
            report.append(process_file(path, strategies, args))

    report_path.write_text(json.dumps(report, indent=2), encoding="utf-8")
    print(f"[final auto-verify] wrote report to {report_path}")


if __name__ == "__main__":
    main()
