from __future__ import annotations

import itertools
import json
import pathlib
import re
import sys
from typing import Dict, List, Optional, Any, Set

from z3 import And, BoolRef, BoolVal, Not, Or, Solver, substitute, sat

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "week5"))
sys.path.append(str(ROOT / "week9"))

try:
    import parser as week5_parser  # type: ignore
except ImportError:
    week5_parser = None

try:
    import bool_linear_invariants as week9  # type: ignore
except ImportError:
    week9 = None


def adapt_method_summary(raw: Dict[str, Any]) -> Dict[str, Any]:
    if not raw:
        return {
            "method_name": "",
            "loops": [],
            "preconditions": [],
            "postconditions": [],
            "parameters": [],
            "returns": [],
        }

    if "methods" in raw and isinstance(raw["methods"], list) and raw["methods"]:
        m0 = raw["methods"][0]
        return {
            "method_name": m0.get("method_name", m0.get("name", "")),
            "loops": m0.get("loops", []),
            "preconditions": m0.get("preconditions", m0.get("requires", [])),
            "postconditions": m0.get("postconditions", m0.get("ensures", [])),
            "parameters": m0.get("parameters", []),
            "returns": m0.get("returns", []),
        }

    return {
        "method_name": raw.get("method_name", ""),
        "loops": raw.get("loops", []),
        "preconditions": raw.get("preconditions", []),
        "postconditions": raw.get("postconditions", []),
        "parameters": raw.get("parameters", []),
        "returns": raw.get("returns", []),
    }


def _strip_parens(s: str) -> str:
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, c in enumerate(s):
            if c == "(":
                depth += 1
            elif c == ")":
                depth -= 1
                if depth == 0 and i != len(s) - 1:
                    break
        else:
            return s[1:-1].strip()
    return s


def split_dnf_string(dnf: str) -> List[List[str]]:
    dnf = dnf.strip()
    if not dnf:
        return []
    raw_clauses = [c.strip() for c in dnf.split("||") if c.strip()]
    cases: List[List[str]] = []

    for clause in raw_clauses:
        inner = _strip_parens(clause)
        parts = [p.strip() for p in re.split(r"\s+&&\s+", inner) if p.strip()]
        cases.append(parts)

    return cases


def _collect_atoms(base_invs: List[str]) -> List[str]:
    atoms: List[str] = []
    seen: Set[str] = set()
    for inv in base_invs:
        inner = _strip_parens(inv)
        parts = [p.strip() for p in re.split(r"\s+&&\s+", inner) if p.strip()]
        for p in parts:
            if p not in seen:
                seen.add(p)
                atoms.append(p)
    return atoms


def _atom_to_z3(atom: str, env: Dict[str, Any]) -> Optional[BoolRef]:
    expr = _strip_parens(atom)
    if not expr:
        return None
    try:
        res = eval(expr, {"__builtins__": {}}, env)  # noqa: S307 (controlled env)
    except Exception:
        return None
    if isinstance(res, bool):
        return BoolVal(res)
    if isinstance(res, BoolRef):
        return res
    return None


def try_build_two_branch_dnf(
    src: str,
    method_summary: Dict[str, Any],
    loop_id: int,
    base_invs: List[str],
    max_atoms_per_branch: int = 2,
    max_pairs: int = 80,
) -> Optional[str]:
    if week9 is None:
        return None

    try:
        z3_vars, init_subst, guard_z3, updates_z3 = week9.get_loop_semantics(
            src, method_summary, loop_id=loop_id
        )
    except Exception:
        return None

    if not z3_vars or not updates_z3:
        return None

    atoms = _collect_atoms(base_invs)
    if not atoms:
        return None

    atom_pool = []
    for atom in atoms:
        z = _atom_to_z3(atom, z3_vars)
        if z is None:
            continue
        s_guard = Solver()
        if guard_z3 is not None:
            s_guard.add(guard_z3)
        s_guard.add(z)
        if s_guard.check() != sat:
            continue
        atom_pool.append((atom, z))

    if not atom_pool:
        return None

    def branch_expr(z_items: List[BoolRef]) -> BoolRef:
        if len(z_items) == 1:
            return z_items[0]
        return And(z_items)

    branch_candidates = []
    seen_branches: Set[str] = set()
    for r in range(1, max_atoms_per_branch + 1):
        for combo in itertools.combinations(atom_pool, r):
            atoms_str = [a for a, _ in combo]
            key = "&&".join(sorted(atoms_str))
            if key in seen_branches:
                continue
            z_items = [z for _, z in combo]
            b_expr = branch_expr(z_items)
            s_sat = Solver()
            if guard_z3 is not None:
                s_sat.add(guard_z3)
            s_sat.add(b_expr)
            if s_sat.check() != sat:
                continue
            branch_candidates.append((atoms_str, b_expr))
            seen_branches.add(key)

    if len(branch_candidates) < 2:
        return None

    substitutions = [(z3_vars[name], updates_z3[name]) for name in z3_vars if name in updates_z3]
    if not substitutions:
        return None

    def implies(a: BoolRef, b: BoolRef) -> bool:
        s = Solver()
        if guard_z3 is not None:
            s.add(guard_z3)
        s.add(a)
        s.add(Not(b))
        return s.check() != sat

    def format_branch(atoms_str: List[str]) -> str:
        if len(atoms_str) == 1:
            return atoms_str[0]
        return f"({' && '.join(atoms_str)})"

    def verify_candidate(b1_expr: BoolRef, b2_expr: BoolRef) -> bool:
        disj = Or(b1_expr, b2_expr)
        s_sat = Solver()
        s_sat.add(disj)
        if s_sat.check() != sat:
            return False

        if init_subst:
            s_init = Solver()
            for v, val in init_subst.items():
                if v in z3_vars:
                    s_init.add(z3_vars[v] == val)
            s_init.add(Not(disj))
            if s_init.check() == sat:
                return False

        b1_prime = substitute(b1_expr, *substitutions)
        b2_prime = substitute(b2_expr, *substitutions)
        disj_prime = Or(b1_prime, b2_prime)

        s_ind = Solver()
        s_ind.add(disj)
        if guard_z3 is not None:
            s_ind.add(guard_z3)
        s_ind.add(Not(disj_prime))
        if s_ind.check() == sat:
            return False

        return True

    checked = 0
    for b1, b2 in itertools.combinations(branch_candidates, 2):
        if checked >= max_pairs:
            break
        checked += 1
        b1_atoms, b1_expr = b1
        b2_atoms, b2_expr = b2
        if implies(b1_expr, b2_expr) or implies(b2_expr, b1_expr):
            continue
        if verify_candidate(b1_expr, b2_expr):
            left = format_branch(b1_atoms)
            right = format_branch(b2_atoms)
            return f"{left} || {right}"

    return None


def synthesize_disjunctive_invariants_for_method(
    src: str,
    method_summary: Dict[str, Any],
    use_boolean: bool = True,
) -> Dict[str, Any]:
    ms = adapt_method_summary(method_summary)
    loops = ms.get("loops", []) or []
    loops_for_iteration = loops if loops else [None]

    loop_entries: List[Dict[str, Any]] = []

    for loop_id, loop_info in enumerate(loops_for_iteration):
        loop_info = loop_info or {}

        precomputed: List[str] = []
        if isinstance(loop_info.get("synthesized_invariants"), list):
            precomputed = [s for s in loop_info["synthesized_invariants"] if isinstance(s, str)]
        elif isinstance(ms.get("synthesized_invariants"), list):
            precomputed = [s for s in ms["synthesized_invariants"] if isinstance(s, str)]

        if precomputed:
            invs = precomputed
        elif week9 is None:
            invs = []
        else:
            if use_boolean:
                invs = week9.synthesize_boolean_dnf_invariant_for_loop(src, ms)
            else:
                invs = week9.synthesize_linear_invariants_for_loop(src, ms)

        # verified 2-branch DNF (semantic split), fallback to base invariants
        if invs and all("||" not in s for s in invs):
            candidate_dnf = try_build_two_branch_dnf(src, ms, loop_id, invs)
            if candidate_dnf:
                invs = [candidate_dnf]

        disjunctive_cases: List[Dict[str, Any]] = []
        for inv_str in invs:
            cases = split_dnf_string(inv_str)
            disjunctive_cases.append(
                {
                    "dnf": inv_str,
                    "cases": cases,
                }
            )

        loop_entries.append(
            {
                "loop_id": loop_id,
                "type": loop_info.get("type"),
                "condition": loop_info.get("condition"),
                "variables": loop_info.get("variables", []),
                "existing_invariants": loop_info.get("invariants", []),
                "disjunctive_invariants": disjunctive_cases,
            }
        )

    return {
        "method_name": ms.get("method_name"),
        "preconditions": ms.get("preconditions", []),
        "postconditions": ms.get("postconditions", []),
        "parameters": ms.get("parameters", []),
        "returns": ms.get("returns", []),
        "loops": loop_entries,
    }


def synthesize_disjunctive_invariants_for_file(
    src_path: pathlib.Path,
    summary_json: Optional[pathlib.Path] = None,
    use_boolean: bool = True,
) -> Dict[str, Any]:
    src = src_path.read_text(encoding="utf-8")

    if summary_json is not None:
        raw_summary = json.loads(summary_json.read_text(encoding="utf-8"))
    elif week5_parser is not None:
        try:
            raw_summary = week5_parser.run_parser(str(src_path))
        except Exception:
            raw_summary = {}
    else:
        raw_summary = {}

    methods_raw = raw_summary.get("methods", [])
    methods_out: List[Dict[str, Any]] = []

    if methods_raw:
        for m_raw in methods_raw:
            m_out = synthesize_disjunctive_invariants_for_method(
                src,
                m_raw,
                use_boolean=use_boolean,
            )
            methods_out.append(m_out)
    else:
        m_out = synthesize_disjunctive_invariants_for_method(
            src,
            raw_summary,
            use_boolean=use_boolean,
        )
        methods_out.append(m_out)

    return {
        "file": str(src_path),
        "methods": methods_out,
    }


def main():
    import argparse

    ap = argparse.ArgumentParser(
        description="Week 10: Disjunctive Invariant Synthesis."
    )
    ap.add_argument("file", help="Input Dafny (.dfy) file")
    ap.add_argument(
        "--summary",
        help="Optional JSON summary produced by week5/parser.py",
    )
    ap.add_argument(
        "--bool",
        action="store_true",
        help="Force Boolean DNF invariants (default if available).",
    )
    ap.add_argument(
        "--no-bool",
        action="store_true",
        help="Disable Boolean DNF; use only linear invariants.",
    )
    ap.add_argument(
        "--out",
        help="Write JSON result with disjunctive invariants to this path.",
    )

    args = ap.parse_args()

    src_path = pathlib.Path(args.file)
    summary_path = pathlib.Path(args.summary) if args.summary else None

    use_boolean = True
    if args.no_bool:
        use_boolean = False
    if args.bool:
        use_boolean = True

    result = synthesize_disjunctive_invariants_for_file(
        src_path,
        summary_json=summary_path,
        use_boolean=use_boolean,
    )

    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
