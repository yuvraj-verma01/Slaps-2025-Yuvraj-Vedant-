from __future__ import annotations

import itertools
import json
import pathlib
import re
import sys
from dataclasses import dataclass
from math import gcd as math_gcd
from typing import Dict, List, Optional, Tuple

from z3 import And, Int, Not, Or, Solver, sat

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "week5"))

try:
    import parser as week5_parser  # type: ignore
except ImportError:
    week5_parser = None

@dataclass
class LoopSpec:
    condition: str          
    variables: List[str]    
    body: str               
    prefix: str             


# regex fallbacks for loop parsing
# Allow optional invariant/decreases lines between the guard and the loop body.
# The old pattern expected '{' immediately after the condition, which broke on
# verified Dafny samples that list invariants first.
WHILE_RE = re.compile(
    r"while\s*"
    r"(?:\((?P<cond_paren>[^)]*)\)|(?P<cond_noparen>[^{\n]*))"
    r"(?:\s*(?:invariant|decreases)[^\n]*\n)*"
    r"\s*(?P<brace>\{)",
    re.MULTILINE,
)

def _clean_cond_text(raw: str) -> str:
    if not raw:
        return ""
    line = raw.splitlines()[0]
    if "decreases" in line:
        line = line.split("decreases", 1)[0]
    return line.strip()


FOR_HEADER_RE = re.compile(
    r"for\s*\(\s*(?P<var>[A-Za-z_][A-Za-z0-9_]*)\s*:=\s*(?P<start>[^;]*);\s*"
    r"(?P<cond>[^;]*);\s*(?P<update>[^)]*)\)\s*(?P<brace>\{)",
    re.DOTALL,
)

ASSIGN_RE = re.compile(
    r"(?P<lhs>[A-Za-z_][A-Za-z0-9_]*)\s*:=\s*(?P<rhs>[^;]+);"
)

#helper functions

def strip_comments(src: str) -> str:
    lines = []
    for line in src.splitlines():
        if "//" in line:
            line = line.split("//", 1)[0]
        lines.append(line)
    return "\n".join(lines)


def find_matching_brace(code: str, start: int) -> int:
    assert code[start] == "{"
    depth = 0
    for i in range(start, len(code)):
        c = code[i]
        if c == "{":
            depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                return i
    raise ValueError(f"Unmatched '{{' at index {start}")


def parse_assignments(code: str) -> List[Tuple[str, str]]:
    assigns: List[Tuple[str, str]] = []
    for m in ASSIGN_RE.finditer(code):
        lhs = m.group("lhs").strip()
        rhs = m.group("rhs").strip()
        assigns.append((lhs, rhs))
    return assigns


#integrate week 5 parser outputs

def adapt_method_summary(raw: Dict) -> Dict:
    if not raw:
        return {}

    if "method_name" in raw:
        return raw

    if "methods" in raw and raw["methods"]:
        m0 = raw["methods"][0]
        return {
            "method_name": m0.get("name", ""),
            "loops": m0.get("loops", []),
            "preconditions": m0.get("requires", m0.get("preconditions", [])),
            "postconditions": m0.get("ensures", m0.get("postconditions", [])),
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


def extract_loop_by_condition(
    src: str,
    cond: str,
    vars_from_summary: List[str],
) -> Optional[LoopSpec]:
    code = strip_comments(src)
    want = cond.strip()

    for m in WHILE_RE.finditer(code):
        c_raw = (m.group("cond_paren") or m.group("cond_noparen") or "")
        c = _clean_cond_text(c_raw)
        if c != want:
            continue

        brace_pos = m.start("brace")
        body_end = find_matching_brace(code, brace_pos)
        body = code[brace_pos + 1: body_end]
        prefix = code[:m.start()]

        vars_list = vars_from_summary or sorted({lhs for lhs, _ in parse_assignments(body)})
        return LoopSpec(condition=c, variables=vars_list, body=body, prefix=prefix)

    return None


def find_first_loop_fallback(src: str) -> Optional[LoopSpec]:
    code = strip_comments(src)

    m = WHILE_RE.search(code)
    if m:
        c_raw = (m.group("cond_paren") or m.group("cond_noparen") or "")
        cond = _clean_cond_text(c_raw)
        brace_pos = m.start("brace")
        body_end = find_matching_brace(code, brace_pos)
        body = code[brace_pos + 1: body_end]
        prefix = code[:m.start()]
        vars_list = sorted({lhs for lhs, _ in parse_assignments(body)})
        return LoopSpec(condition=cond, variables=vars_list, body=body, prefix=prefix)


    m = FOR_HEADER_RE.search(code)
    if m:
        cond_text = m.group("cond").strip()
        brace_pos = m.start("brace")
        body_end = find_matching_brace(code, brace_pos)
        body = code[brace_pos + 1: body_end]
        prefix = code[:m.start()]
        vars_list = sorted({lhs for lhs, _ in parse_assignments(body)})
        return LoopSpec(condition=cond_text, variables=vars_list, body=body, prefix=prefix)

    return None

# Tiny linear arithmetic parser (supports k*x)


def parse_term(tok: str, var_map: Dict[str, Int]):
    """
    Parse a single term:
      c
      x
      k*x
    """
    tok = tok.strip()
    if not tok:
        return None

    # integer constant
    if re.fullmatch(r"-?\d+", tok):
        return int(tok)

    # k*x
    m = re.match(r"^([+-]?\d+)\s*\*\s*([A-Za-z_][A-Za-z0-9_]*)$", tok)
    if m:
        coef = int(m.group(1))
        var = m.group(2)
        if var in var_map:
            return coef * var_map[var]
        return None

    # plain variable
    if tok in var_map:
        return var_map[tok]

    return None


def parse_linear_expr(expr: str, var_map: Dict[str, Int]):
    """
    Parse a very small linear expression
    """
    expr = expr.strip()
    if not expr:
        return None

    tokens = []
    i = 0
    sign = 1

    while i < len(expr):
        c = expr[i]
        if c in "+-":
            sign = 1 if c == "+" else -1
            i += 1
        elif c.isspace():
            i += 1
        else:
            j = i
            while j < len(expr) and expr[j] not in "+-":
                j += 1
            tok = expr[i:j].strip()
            if tok:
                tokens.append((sign, tok))
            i = j

    if not tokens:
        return None

    z3_terms = []
    for sgn, tok in tokens:
        t = parse_term(tok, var_map)
        if t is None:
            return None
        z3_terms.append(sgn * t)

    if not z3_terms:
        return None

    acc = z3_terms[0]
    for t in z3_terms[1:]:
        acc = acc + t
    return acc


def parse_guard(cond: str, var_map: Dict[str, Int]):
    """
    Parse guards like:
      e1 <= e2, e1 < e2, e1 >= e2, e1 > e2, e1 == e2
    """
    if not cond:
        return None

    cond = cond.strip()
    if not cond:
        return None

    parts = [p.strip() for p in re.split(r"&&|\band\b", cond) if p.strip()]
    if not parts:
        parts = [cond]

    atoms = []
    for atom_s in parts:
        parsed = None
        for op in ["<=", ">=", "==", "<", ">"]:
            pieces = atom_s.split(op)
            if len(pieces) == 2:
                lhs_s, rhs_s = pieces[0].strip(), pieces[1].strip()
                lhs = parse_linear_expr(lhs_s, var_map)
                rhs = parse_linear_expr(rhs_s, var_map)
                if lhs is None or rhs is None:
                    parsed = None
                    break
                if op == "<=":
                    parsed = lhs <= rhs
                elif op == "<":
                    parsed = lhs < rhs
                elif op == ">=":
                    parsed = lhs >= rhs
                elif op == ">":
                    parsed = lhs > rhs
                elif op == "==":
                    parsed = lhs == rhs
                break
        if parsed is not None:
            atoms.append(parsed)

    if not atoms:
        return None
    if len(atoms) == 1:
        return atoms[0]
    return And(atoms)



# transition relation from assignments

def build_transition_constraints(
    assigns: List[Tuple[str, str]],
    v_before: Dict[str, Int],
    v_after: Dict[str, Int],
):

    updates: Dict[str, List] = {}
    assigned_vars = set()

    for lhs, rhs in assigns:
        if lhs not in v_before or lhs not in v_after:
            continue
        assigned_vars.add(lhs)
        rhs_z3 = parse_linear_expr(rhs, v_before)
        if rhs_z3 is None:
            continue
        updates.setdefault(lhs, []).append(rhs_z3)

    for v in v_before:
        if v not in assigned_vars:
            updates.setdefault(v, []).append(v_before[v])

    if not updates:
        return None

    cs = []
    for lhs, rhss in updates.items():
        if len(rhss) == 1:
            cs.append(v_after[lhs] == rhss[0])
        else:
            cs.append(Or(*[v_after[lhs] == r for r in rhss]))

    return And(cs) if cs else None


def extract_initial_values_from_prefix(
    prefix: str,
    vars_list: List[str],
) -> Dict[str, int]:
    init: Dict[str, int] = {}
    for m in ASSIGN_RE.finditer(prefix):
        lhs = m.group("lhs").strip()
        rhs = m.group("rhs").strip()
        if lhs not in vars_list:
            continue
        if re.fullmatch(r"-?\d+", rhs):
            init[lhs] = int(rhs)
    return init



# template configuration


COEFF_RANGE = range(-3, 4)
C_RANGE = range(-10, 11)
COEFF_RANGE_BOOL = range(-2, 3)
C_RANGE_BOOL = range(-5, 6)


def candidate_linear_templates(
    vars_list: List[str],
    coeff_range=COEFF_RANGE,
    c_range=C_RANGE,
):
    n = len(vars_list)
    for coeffs in itertools.product(coeff_range, repeat=n):
        if all(a == 0 for a in coeffs):
            continue
        for c in c_range:
            yield coeffs, c


def normalize_constraint(coeffs: Tuple[int, ...], c: int) -> Tuple[Tuple[int, ...], int]:
    g = 0
    for a in coeffs:
        g = math_gcd(g, abs(a))
    if c != 0:
        g = math_gcd(g, abs(c)) if g != 0 else abs(c)
    if g > 1:
        coeffs = tuple(a // g for a in coeffs)
        c //= g

    for a in coeffs:
        if a < 0:
            coeffs = tuple(-x for x in coeffs)
            c = -c
            break
        if a > 0:
            break

    return coeffs, c


def normalize_atom_signed(coeffs: Tuple[int, ...], c: int) -> Tuple[Tuple[int, ...], int]:
    g = 0
    for a in coeffs:
        g = math_gcd(g, abs(a))
    if c != 0:
        g = math_gcd(g, abs(c)) if g != 0 else abs(c)
    if g > 1:
        coeffs = tuple(a // g for a in coeffs)
        c //= g
    return coeffs, c


def prune_implied(invariants: Dict[Tuple[int, ...], int]) -> Dict[Tuple[int, ...], int]:
    pruned: Dict[Tuple[int, ...], int] = {}
    for coeffs, c in invariants.items():
        if coeffs in pruned:
            pruned[coeffs] = min(pruned[coeffs], c)
        else:
            pruned[coeffs] = c
    return pruned


def pretty_print_linear(
    vars_list: List[str],
    coeffs: Tuple[int, ...],
    c: int,
) -> Optional[str]:
    terms = []
    for a, v in zip(coeffs, vars_list):
        if a == 0:
            continue
        if a == 1:
            terms.append(v)
        elif a == -1:
            terms.append(f"-{v}")
        else:
            terms.append(f"{a}*{v}")
    if not terms:
        return None
    lhs = " + ".join(terms).replace("+ -", "- ")
    return f"{lhs} <= {c}"



# Inductiveness checks 


def check_linear_invariant(
    vars_list: List[str],
    coeffs: Tuple[int, ...],
    c: int,
    guard_expr,
    trans_constraints,
    initial_vals: Dict[str, int],
) -> bool:
    """
    Check:
      1. SAT:      I is satisfiable
      2. Init:     Init |= I
      3. Inductive: I & guard & T |= I'
    using standard ∀-via-UNSAT encoding.
    """
    v_before = {v: Int(v) for v in vars_list}
    v_after = {v: Int(v + "_next") for v in vars_list}

    lhs = sum(coeffs[i] * v_before[vars_list[i]] for i in range(len(vars_list)))
    lhs_next = sum(coeffs[i] * v_after[vars_list[i]] for i in range(len(vars_list)))
    inv = lhs <= c
    inv_next = lhs_next <= c

    # (1) Non-trivial
    s = Solver()
    s.add(inv)
    if s.check() != sat:
        return False

    # (2) Initialization
    if initial_vals:
        s_init = Solver()
        for v, val in initial_vals.items():
            if v in v_before:
                s_init.add(v_before[v] == val)
        s_init.add(Not(inv))
        if s_init.check() == sat:
            return False

    # (3) Inductiveness
    if trans_constraints is not None:
        s_ind = Solver()
        s_ind.add(inv)
        if guard_expr is not None:
            s_ind.add(guard_expr)
        s_ind.add(trans_constraints)
        s_ind.add(Not(inv_next))
        if s_ind.check() == sat:
            return False

    return True



def synthesize_linear_invariants_for_loop(
    src: str,
    method_summary: Dict,
    coeff_range=COEFF_RANGE,
    c_range=C_RANGE,
    max_invariants: int = 5,
) -> List[str]:
    ms = adapt_method_summary(method_summary)
    loops = ms.get("loops", [])

    loop_spec: Optional[LoopSpec] = None
    vars_list: List[str] = []
    cond: str = ""

    if loops:
        loop_info = next((L for L in loops if L.get("type") == "while"), loops[0])
        cond = (loop_info.get("condition") or "").strip()
        vars_list = list(loop_info.get("variables") or [])
        if cond:
            loop_spec = extract_loop_by_condition(src, cond, vars_list)

    if loop_spec is None:
        loop_spec = find_first_loop_fallback(src)
    if loop_spec is None:
        return []

    if not vars_list:
        vars_list = loop_spec.variables or sorted({lhs for lhs, _ in parse_assignments(loop_spec.body)})
    if not vars_list:
        return []

    cond = loop_spec.condition
    assigns = parse_assignments(loop_spec.body)
    initial_vals = extract_initial_values_from_prefix(loop_spec.prefix, vars_list)

    v_before = {v: Int(v) for v in vars_list}
    v_after = {v: Int(v + "_next") for v in vars_list}

    trans_cs = build_transition_constraints(assigns, v_before, v_after)
    guard_z3 = parse_guard(cond, v_before)

    if trans_cs is None:
        return []

    invariant_map: Dict[Tuple[int, ...], int] = {}

    for coeffs, c in candidate_linear_templates(vars_list, coeff_range, c_range):
        norm_coeffs, norm_c = normalize_constraint(coeffs, c)

        if norm_coeffs in invariant_map and invariant_map[norm_coeffs] <= norm_c:
            continue

        if check_linear_invariant(vars_list, norm_coeffs, norm_c, guard_z3, trans_cs, initial_vals):
            if norm_coeffs in invariant_map:
                invariant_map[norm_coeffs] = min(invariant_map[norm_coeffs], norm_c)
            else:
                invariant_map[norm_coeffs] = norm_c

        if len(invariant_map) >= max_invariants:
            break

    invariant_map = prune_implied(invariant_map)

    invariants: List[str] = []
    for coeffs, c in sorted(invariant_map.items()):
        s = pretty_print_linear(vars_list, coeffs, c)
        if s:
            invariants.append(s)

    return invariants


@dataclass(frozen=True)
class BoolAtom:
    coeffs: Tuple[int, ...]
    c: int

    def to_z3(self, vars_list: List[str], vmap: Dict[str, Int]):
        return sum(
            self.coeffs[i] * vmap[vars_list[i]] for i in range(len(vars_list))
        ) <= self.c

    def to_str(self, vars_list: List[str]) -> str:
        return pretty_print_linear(vars_list, self.coeffs, self.c) or "0 <= 0"


def dnf_to_z3(
    clauses: List[List[BoolAtom]],
    vars_list: List[str],
    vmap: Dict[str, Int],
):
    disj = []
    for clause in clauses:
        if not clause:
            continue
        conj = [atom.to_z3(vars_list, vmap) for atom in clause]
        disj.append(And(conj))
    if not disj:
        return None
    if len(disj) == 1:
        return disj[0]
    return Or(disj)


def format_dnf(
    clauses: List[List[BoolAtom]],
    vars_list: List[str],
) -> str:
    parts = []
    for clause in clauses:
        if not clause:
            continue
        if len(clause) == 1:
            parts.append(clause[0].to_str(vars_list))
        else:
            inner = " && ".join(a.to_str(vars_list) for a in clause)
            parts.append(f"({inner})")
    if not parts:
        return "false"
    if len(parts) == 1:
        return parts[0]
    return " || ".join(parts)


def collect_candidate_atoms(
    vars_list: List[str],
    guard_expr,
    v_before: Dict[str, Int],
    coeff_range=COEFF_RANGE_BOOL,
    c_range=C_RANGE_BOOL,
    max_atoms: int = 12,
) -> List[BoolAtom]:
    pool: List[BoolAtom] = []
    seen = set()

    for coeffs, c in candidate_linear_templates(vars_list, coeff_range, c_range):
        norm_coeffs, norm_c = normalize_atom_signed(coeffs, c)
        key = (norm_coeffs, norm_c)
        if key in seen:
            continue

        atom = BoolAtom(norm_coeffs, norm_c)

        s = Solver()
        if guard_expr is not None:
            s.add(guard_expr)
        s.add(atom.to_z3(vars_list, v_before))
        if s.check() != sat:
            continue

        pool.append(atom)
        seen.add(key)

    def atom_score(a: BoolAtom) -> int:
        return sum(abs(x) for x in a.coeffs) + abs(a.c)

    pool.sort(key=atom_score)
    return pool[:max_atoms]


def check_dnf_invariant(
    vars_list: List[str],
    clauses: List[List[BoolAtom]],
    guard_expr,
    trans_constraints,
    initial_vals: Dict[str, int],
) -> bool:

    if not clauses:
        return False

    v_before = {v: Int(v) for v in vars_list}
    v_after = {v: Int(v + "_next") for v in vars_list}

    I = dnf_to_z3(clauses, vars_list, v_before)
    I_prime = dnf_to_z3(clauses, vars_list, v_after)
    if I is None or I_prime is None:
        return False

    # SAT
    s_sat = Solver()
    s_sat.add(I)
    if s_sat.check() != sat:
        return False

    # Init
    if initial_vals:
        s_init = Solver()
        for v, val in initial_vals.items():
            if v in v_before:
                s_init.add(v_before[v] == val)
        s_init.add(Not(I))
        if s_init.check() == sat:
            return False

    if trans_constraints is None:
        return False

    # Inductive
    s_ind = Solver()
    s_ind.add(I)
    if guard_expr is not None:
        s_ind.add(guard_expr)
    s_ind.add(trans_constraints)
    s_ind.add(Not(I_prime))
    if s_ind.check() == sat:
        return False

    return True


def synthesize_boolean_dnf_invariant_for_loop(
    src: str,
    method_summary: Dict,
    max_clauses: int = 2,
    max_atoms_per_clause: int = 3,
    max_clause_candidates: int = 30,
    coeff_range=COEFF_RANGE_BOOL,
    c_range=C_RANGE_BOOL,
) -> List[str]:
    ms = adapt_method_summary(method_summary)
    loops = ms.get("loops", [])

    loop_spec: Optional[LoopSpec] = None
    vars_list: List[str] = []
    cond: str = ""

    if loops:
        loop_info = next((L for L in loops if L.get("type") == "while"), loops[0])
        cond = (loop_info.get("condition") or "").strip()
        vars_list = list(loop_info.get("variables") or [])
        if cond:
            loop_spec = extract_loop_by_condition(src, cond, vars_list)

    if loop_spec is None:
        loop_spec = find_first_loop_fallback(src)
    if loop_spec is None:
        return []

    if not vars_list:
        vars_list = loop_spec.variables or sorted({lhs for lhs, _ in parse_assignments(loop_spec.body)})
    if not vars_list:
        return []

    cond = loop_spec.condition
    assigns = parse_assignments(loop_spec.body)
    initial_vals = extract_initial_values_from_prefix(loop_spec.prefix, vars_list)

    v_before = {v: Int(v) for v in vars_list}
    v_after = {v: Int(v + "_next") for v in vars_list}

    trans_cs = build_transition_constraints(assigns, v_before, v_after)
    guard_z3 = parse_guard(cond, v_before)

    if trans_cs is None:
        return synthesize_linear_invariants_for_loop(src, ms, coeff_range, c_range)

    atoms = collect_candidate_atoms(
        vars_list,
        guard_expr=guard_z3,
        v_before=v_before,
        coeff_range=coeff_range,
        c_range=c_range,
        max_atoms=12,
    )

    if not atoms:
        return synthesize_linear_invariants_for_loop(src, ms, coeff_range, c_range)

    # Build candidate conjunctions (clauses)
    clauses_pool: List[List[BoolAtom]] = []
    seen_clause = set()

    per_size_cap = max(2, max_clause_candidates // max_atoms_per_clause) or 2

    for r in range(1, max_atoms_per_clause + 1):
        added_this_size = 0
        for subset in itertools.combinations(atoms, r):
            uniq = []
            seen_atoms = set()
            for a in subset:
                key = (a.coeffs, a.c)
                if key not in seen_atoms:
                    seen_atoms.add(key)
                    uniq.append(a)
            if not uniq:
                continue
            key_clause = tuple(sorted((a.coeffs, a.c) for a in uniq))
            if key_clause in seen_clause:
                continue
            seen_clause.add(key_clause)
            clauses_pool.append(uniq)
            added_this_size += 1
            if added_this_size >= per_size_cap or len(clauses_pool) >= max_clause_candidates:
                break
        if len(clauses_pool) >= max_clause_candidates:
            break

    def clause_score(clause: List[BoolAtom]) -> int:
        return -len(clause), sum(sum(abs(x) for x in a.coeffs) + abs(a.c) for a in clause)

    clauses_pool.sort(key=clause_score)

    # Try small DNFs
    for k in range(1, max_clauses + 1):
        for chosen in itertools.combinations(clauses_pool, k):
            clauses = list(chosen)
            if check_dnf_invariant(vars_list, clauses, guard_z3, trans_cs, initial_vals):
                return [format_dnf(clauses, vars_list)]

    return synthesize_linear_invariants_for_loop(src, ms, coeff_range, c_range)



# CLI 


def main():
    import argparse

    ap = argparse.ArgumentParser(
        description="Week 6/9: Synthesize linear and Boolean (DNF) invariants."
    )
    ap.add_argument("file", help="Input Dafny (.dfy) file")
    ap.add_argument(
        "--summary",
        help="JSON summary from week5/parser.py; if omitted and available, run it.",
    )
    ap.add_argument(
        "--bool",
        action="store_true",
        help="Use Week 9 Boolean (DNF) synthesis (with linear fallback).",
    )
    ap.add_argument(
        "--out",
        help="Write JSON result with synthesized invariants to this path.",
    )

    args = ap.parse_args()

    src_path = pathlib.Path(args.file)
    src = src_path.read_text(encoding="utf-8")


    if args.summary:
        raw_summary = json.loads(pathlib.Path(args.summary).read_text(encoding="utf-8"))
    elif week5_parser is not None:
        try:
            raw_summary = week5_parser.run_parser(str(src_path))
        except Exception:
            raw_summary = {}
    else:
        raw_summary = {}

    ms = adapt_method_summary(raw_summary)

    if args.bool:
        invs = synthesize_boolean_dnf_invariant_for_loop(src, ms)
    else:
        invs = synthesize_linear_invariants_for_loop(src, ms)

    loop_info = (ms.get("loops") or [{}])[0]

    result = {
        "file": str(src_path),
        "loop": loop_info,
        "synthesized_invariants": invs,
    }

    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
