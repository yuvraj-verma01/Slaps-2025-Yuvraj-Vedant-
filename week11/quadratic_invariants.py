from __future__ import annotations

import argparse
import itertools
import json
import pathlib
import sys
from typing import Dict, List, Optional, Sequence, Tuple

from z3 import Int, Not, Solver, sat

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT))
sys.path.append(str(ROOT / "week5"))
sys.path.append(str(ROOT / "week9"))

try:
    import parser as week5_parser  # type: ignore
except ImportError:
    week5_parser = None

try:
    import week9.bool_linear_invariants as linv  
except ImportError:
    linv = None


COEFF_RANGE = range(-2, 3)
CONST_RANGE = range(-6, 7)
DEFAULT_MAX_INVARIANTS = 6
DEFAULT_MAX_TERMS = 3
DEFAULT_MAX_CANDIDATES = 20000


def _pick_loop_and_vars(src: str, method_summary: Dict) -> Tuple[Optional[object], List[str], str]:
    """Reuse week9 helpers to locate the target loop and variables."""
    if linv is None:
        return None, [], ""

    ms = linv.adapt_method_summary(method_summary) if hasattr(linv, "adapt_method_summary") else (method_summary or {})
    loops = ms.get("loops", [])

    loop_spec = None
    vars_list: List[str] = []
    cond = ""

    if loops:
        loop_info = next((L for L in loops if L.get("type") == "while"), loops[0])
        cond = (loop_info.get("condition") or "").strip()
        vars_list = list(loop_info.get("variables") or [])
        if cond and hasattr(linv, "extract_loop_by_condition"):
            loop_spec = linv.extract_loop_by_condition(src, cond, vars_list)

    if loop_spec is None and hasattr(linv, "find_first_loop_fallback"):
        loop_spec = linv.find_first_loop_fallback(src)

    if loop_spec is None:
        return None, [], ""
    if not cond and hasattr(loop_spec, "condition"):
        cond = getattr(loop_spec, "condition") or ""

    if not vars_list and hasattr(loop_spec, "variables"):
        vars_list = list(getattr(loop_spec, "variables") or [])
    if not vars_list and hasattr(linv, "parse_assignments"):
        vars_list = sorted({lhs for lhs, _ in linv.parse_assignments(getattr(loop_spec, "body", ""))})

    return loop_spec, vars_list, cond


def _quadratic_expr(coeffs: Sequence[int], x, y=None):
    a, b, c, d, e, f = coeffs
    expr = a * x * x + d * x + f
    if y is not None:
        expr += b * y * y + c * x * y + e * y
    return expr


def _quadratic_value_no_const(coeffs5: Sequence[int], x_val: int, y_val: Optional[int] = None) -> int:
    a, b, c, d, e = coeffs5
    total = a * x_val * x_val + d * x_val
    if y_val is not None:
        total += b * y_val * y_val + c * x_val * y_val + e * y_val
    return total


def _format_quadratic(coeffs: Sequence[int], vars_pair: List[str]) -> Optional[str]:
    if not vars_pair:
        return None

    x = vars_pair[0]
    y = vars_pair[1] if len(vars_pair) > 1 else None
    a, b, c, d, e, f = coeffs

    terms: List[str] = []
    if a:
        terms.append(f"{a}*{x}*{x}")
    if y and b:
        terms.append(f"{b}*{y}*{y}")
    if y and c:
        terms.append(f"{c}*{x}*{y}")
    if d:
        terms.append(f"{d}*{x}")
    if y and e:
        terms.append(f"{e}*{y}")
    if f:
        terms.append(str(f))

    if not terms:
        return None

    expr = " + ".join(terms).replace("+ -", "- ")
    return f"{expr} <= 0"


def _check_quadratic_invariant(
    vars_pair: List[str],
    all_vars: List[str],
    coeffs: Sequence[int],
    guard_expr,
    trans_constraints,
    initial_vals: Dict[str, int],
) -> bool:
    if not vars_pair:
        return False
    if trans_constraints is None:
        return False

    v_before = {v: Int(v) for v in all_vars}
    v_after = {v: Int(v + "_next") for v in all_vars}

    x = v_before[vars_pair[0]]
    x_next = v_after[vars_pair[0]]
    y = v_before[vars_pair[1]] if len(vars_pair) > 1 else None
    y_next = v_after[vars_pair[1]] if len(vars_pair) > 1 else None

    inv = _quadratic_expr(coeffs, x, y) <= 0
    inv_next = _quadratic_expr(coeffs, x_next, y_next) <= 0

    # satisfiable  invariant
    s_sat = Solver()
    s_sat.add(inv)
    if s_sat.check() != sat:
        return False

    # skip tautologies 
    s_trivial = Solver()
    s_trivial.add(Not(inv))
    if s_trivial.check() == sat:
        pass
    else:
        return False

    # initialization holds
    if initial_vals:
        s_init = Solver()
        for v, val in initial_vals.items():
            if v in v_before:
                s_init.add(v_before[v] == val)
        s_init.add(Not(inv))
        if s_init.check() == sat:
            return False

    # inductive step: I /\ guard /\ T => I'
    s_ind = Solver()
    s_ind.add(inv)
    if guard_expr is not None:
        s_ind.add(guard_expr)
    s_ind.add(trans_constraints)
    s_ind.add(Not(inv_next))
    if s_ind.check() == sat:
        return False

    return True


def synthesize_quadratic_invariants_for_loop(
    src: str,
    method_summary: Dict,
    coeff_range=COEFF_RANGE,
    const_range=CONST_RANGE,
    max_invariants: int = DEFAULT_MAX_INVARIANTS,
    max_terms: int = DEFAULT_MAX_TERMS,
    max_candidates: int = DEFAULT_MAX_CANDIDATES,
) -> List[str]:
    if linv is None:
        return []

    loop_spec, vars_list, cond = _pick_loop_and_vars(src, method_summary)
    if loop_spec is None:
        return []

    assigns = linv.parse_assignments(getattr(loop_spec, "body", "")) if hasattr(linv, "parse_assignments") else []
    if not vars_list:
        vars_list = sorted({lhs for lhs, _ in assigns})
    if not vars_list:
        return []

    all_vars = vars_list
    if len(all_vars) > 2:
        all_vars = list(all_vars)
    vars_pair = all_vars[:2]

    v_before = {v: Int(v) for v in all_vars}
    v_after = {v: Int(v + "_next") for v in all_vars}

    guard_z3 = linv.parse_guard(cond, v_before) if hasattr(linv, "parse_guard") else None
    trans_cs = linv.build_transition_constraints(assigns, v_before, v_after) if hasattr(linv, "build_transition_constraints") else None
    initial_vals = linv.extract_initial_values_from_prefix(getattr(loop_spec, "prefix", ""), all_vars) if hasattr(linv, "extract_initial_values_from_prefix") else {}

    found: List[Tuple[Tuple[int, ...], str]] = []
    seen = set()

    coeff_vals = [v for v in coeff_range if v != 0]
    coeff_vals = sorted(coeff_vals, key=lambda x: (abs(x), x))
    const_vals = sorted(const_range, key=lambda x: (abs(x), x))
    positions = [0, 1, 2, 3, 4]
    quadratic_positions = {0, 1, 2}

    attempts = 0
    stop = False
    early_stop = max_invariants * 3  # keep a small buffer so we still sort/score a few options

    for k in range(1, max_terms + 1):
        combos = list(itertools.combinations(positions, k))
        combo_buckets = [
            [c for c in combos if any(p in quadratic_positions for p in c)],
            [c for c in combos if all(p not in quadratic_positions for p in c)],
        ]
        for combo_list in combo_buckets:
            if stop:
                break
            for idx_combo in combo_list:
                if stop:
                    break
                for vals in itertools.product(coeff_vals, repeat=k):
                    cand_list = [0, 0, 0, 0, 0]
                    for pos, val in zip(idx_combo, vals):
                        cand_list[pos] = val
                    const_candidates: List[int] = []
                    if initial_vals:
                        x0 = initial_vals.get(vars_pair[0])
                        y0 = initial_vals.get(vars_pair[1]) if len(vars_pair) > 1 else None
                        if x0 is not None and (len(vars_pair) == 1 or y0 is not None):
                            base_val = _quadratic_value_no_const(cand_list, x0, y0)
                            const_needed = -base_val
                            if abs(const_needed) <= 100:
                                const_candidates.append(const_needed)
                    const_candidates.extend(const_vals)

                    uniq_consts = []
                    const_seen = set()
                    for c in const_candidates:
                        if c not in const_seen:
                            const_seen.add(c)
                            uniq_consts.append(c)

                    for const in uniq_consts:
                        if attempts >= max_candidates:
                            stop = True
                            break
                        attempts += 1
                        cand = tuple(cand_list + [const])
                        if cand in seen:
                            continue
                        if _check_quadratic_invariant(vars_pair, all_vars, cand, guard_z3, trans_cs, initial_vals):
                            s = _format_quadratic(cand, vars_pair)
                            if s:
                                found.append((cand, s))
                                seen.add(cand)
                                if len(found) >= early_stop:
                                    stop = True
                                    break
                if stop:
                    break
        if stop:
            break
    def inv_score(cand: Tuple[int, ...]) -> Tuple[int, int, int]:
        quad_terms = sum(1 for i in (0, 1, 2) if cand[i] != 0)
        lin_terms = sum(1 for i in (3, 4) if cand[i] != 0)
        magnitude = sum(abs(x) for x in cand)
        return (-quad_terms, lin_terms, magnitude)

    found.sort(key=lambda item: inv_score(item[0]))
    unique_strings: List[str] = []
    for _, s in found:
        if s not in unique_strings:
            unique_strings.append(s)
        if len(unique_strings) >= max_invariants:
            break

    return unique_strings


def synthesize_quadratic_invariants_for_method(
    src: str,
    method_summary: Dict,
    coeff_range=COEFF_RANGE,
    const_range=CONST_RANGE,
    max_invariants: int = DEFAULT_MAX_INVARIANTS,
    max_terms: int = DEFAULT_MAX_TERMS,
    max_candidates: int = DEFAULT_MAX_CANDIDATES,
) -> Dict[str, object]:
    invs = synthesize_quadratic_invariants_for_loop(
        src,
        method_summary,
        coeff_range=coeff_range,
        const_range=const_range,
        max_invariants=max_invariants,
        max_terms=max_terms,
        max_candidates=max_candidates,
    )

    ms = linv.adapt_method_summary(method_summary) if linv and hasattr(linv, "adapt_method_summary") else (method_summary or {})
    loops = ms.get("loops", []) or [{}]
    loop_info = loops[0] if loops else {}

    return {
        "method_name": ms.get("method_name", ""),
        "preconditions": ms.get("preconditions", []),
        "postconditions": ms.get("postconditions", []),
        "parameters": ms.get("parameters", []),
        "returns": ms.get("returns", []),
        "loops": [
            {
                "condition": loop_info.get("condition"),
                "variables": loop_info.get("variables", []) or [],
                "template_variables": ms.get("loops", [{}])[0].get("variables", [])[:2] if ms.get("loops") else [],
                "quadratic_invariants": invs,
                "template": "a*x^2 + b*y^2 + c*x*y + d*x + e*y + f <= 0",
            }
        ],
    }


def synthesize_quadratic_invariants_for_file(
    src_path: pathlib.Path,
    summary_json: Optional[pathlib.Path] = None,
    coeff_range=COEFF_RANGE,
    const_range=CONST_RANGE,
    max_invariants: int = DEFAULT_MAX_INVARIANTS,
    max_terms: int = DEFAULT_MAX_TERMS,
    max_candidates: int = DEFAULT_MAX_CANDIDATES,
) -> Dict[str, object]:
    src = src_path.read_text(encoding="utf-8")

    if summary_json is not None:
        try:
            raw_summary = json.loads(summary_json.read_text(encoding="utf-8"))
        except Exception:
            raw_summary = {}
    elif week5_parser is not None:
        try:
            raw_summary = week5_parser.run_parser(str(src_path))  # type: ignore
        except Exception:
            raw_summary = {}
    else:
        raw_summary = {}

    methods_raw = raw_summary.get("methods", [])
    methods_out: List[Dict[str, object]] = []

    if methods_raw:
        for m_raw in methods_raw:
            m_out = synthesize_quadratic_invariants_for_method(
                src,
                m_raw,
                coeff_range=coeff_range,
                const_range=const_range,
                max_invariants=max_invariants,
                max_terms=max_terms,
                max_candidates=max_candidates,
            )
            methods_out.append(m_out)
    else:
        m_out = synthesize_quadratic_invariants_for_method(
            src,
            raw_summary,
            coeff_range=coeff_range,
            const_range=const_range,
            max_invariants=max_invariants,
            max_terms=max_terms,
            max_candidates=max_candidates,
        )
        methods_out.append(m_out)

    return {
        "file": str(src_path),
        "methods": methods_out,
    }


def main():
    ap = argparse.ArgumentParser(
        description="Week 11: Quadratic invariant synthesis (ax^2 + by^2 + cxy + dx + ey + f <= 0)."
    )
    ap.add_argument("file", help="Input Dafny (.dfy) file")
    ap.add_argument(
        "--summary",
        help="Optional JSON summary produced by week5/parser.py",
    )
    ap.add_argument(
        "--coeff-range",
        nargs=2,
        type=int,
        metavar=("LOW", "HIGH"),
        help="Inclusive range for coefficients a..e (default: -2 2).",
    )
    ap.add_argument(
        "--const-range",
        nargs=2,
        type=int,
        metavar=("LOW", "HIGH"),
        help="Inclusive range for constant term f (default: -6 6).",
    )
    ap.add_argument(
        "--max",
        type=int,
        default=DEFAULT_MAX_INVARIANTS,
        help="Maximum number of invariants to emit (default: 6).",
    )
    ap.add_argument(
        "--max-terms",
        type=int,
        default=DEFAULT_MAX_TERMS,
        help="Maximum non-zero coefficient terms to consider (default: 3).",
    )
    ap.add_argument(
        "--max-candidates",
        type=int,
        default=DEFAULT_MAX_CANDIDATES,
        help="Maximum candidate coefficients to check before stopping (default: 20000).",
    )
    ap.add_argument(
        "--out",
        help="Write JSON result to this path (prints to stdout if omitted).",
    )

    args = ap.parse_args()

    coeff_range = COEFF_RANGE
    const_range = CONST_RANGE

    if args.coeff_range:
        lo, hi = args.coeff_range
        coeff_range = range(lo, hi + 1)
    if args.const_range:
        lo, hi = args.const_range
        const_range = range(lo, hi + 1)

    src_path = pathlib.Path(args.file)
    summary_path = pathlib.Path(args.summary) if args.summary else None

    result = synthesize_quadratic_invariants_for_file(
        src_path,
        summary_json=summary_path,
        coeff_range=coeff_range,
        const_range=const_range,
        max_invariants=args.max,
        max_terms=args.max_terms,
        max_candidates=args.max_candidates,
    )

    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
