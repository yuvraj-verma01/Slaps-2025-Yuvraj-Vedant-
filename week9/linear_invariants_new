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

# ============================================================
# Week 5 AST-based parser wiring
# ============================================================

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "week5"))

try:
    import parser as week5_parser  # type: ignore
except ImportError:
    week5_parser = None


# ============================================================
# Loop representation
# ============================================================

@dataclass
class LoopSpec:
    condition: str          # loop condition as text
    variables: List[str]    # candidate state variables
    body: str               # loop body text (inside { ... })
    prefix: str             # code before the loop (for init extraction)


# Fallback regexes (only used if AST info is missing / partial)
WHILE_RE = re.compile(
    r"while\s*"
    r"(?:\((?P<cond_paren>[^)]*)\)|(?P<cond_noparen>[^{]*))"
    r"\s*(?P<brace>\{)",
    re.DOTALL,
)

FOR_HEADER_RE = re.compile(
    r"for\s*\(\s*(?P<var>[A-Za-z_][A-Za-z0-9_]*)\s*:=\s*(?P<start>[^;]*);\s*"
    r"(?P<cond>[^;]*);\s*(?P<update>[^)]*)\)\s*(?P<brace>\{)",
    re.DOTALL,
)

ASSIGN_RE = re.compile(
    r"(?P<lhs>[A-Za-z_][A-Za-z0-9_]*)\s*:=\s*(?P<rhs>[^;]+);"
)


# ============================================================
# Small helpers
# ============================================================

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


# ============================================================
# Integrate Week 5 summary format(s)
# ============================================================

def adapt_method_summary(raw: Dict) -> Dict:
    """
    Normalize week5/parser.py outputs into a single-method summary:

    {
      "method_name": str,
      "loops": [ { "type": "while", "condition": ..., "variables": [...], ... }, ... ],
      "preconditions": [...],
      "postconditions": [...],
      "parameters": [...],
      "returns": [...]
    }

    Supports:
    - New style: already method_name + loops + ...
    - Old style: {"methods":[...], "loops":[...]}
    - Minimal loop-centric JSON.
    """
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
    """
    Given a loop condition from Week 5 summary, find matching while-loop in src.
    """
    code = strip_comments(src)
    want = cond.strip()

    for m in WHILE_RE.finditer(code):
        c = (m.group("cond_paren") or m.group("cond_noparen") or "").strip()
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
    """
    Fallback if we don't trust / don't have the summary:
    grab first while / for loop textually.
    """
    code = strip_comments(src)

    m = WHILE_RE.search(code)
    if m:
        cond = (m.group("cond_paren") or m.group("cond_noparen") or "").strip()
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


# ============================================================
# Tiny linear arithmetic parser (supports k*x)
# ============================================================

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
    Parse a very small linear expression:
      sum_i ( +/- term_i )
      where term_i is int, var, or k*var.
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
    into z3.
    If unsupported, return None (we just won't use that guard).
    """
    if not cond:
        return None

    cond = cond.strip()

    for op in ["<=", ">=", "==", "<", ">"]:
        parts = cond.split(op)
        if len(parts) == 2:
            lhs_s, rhs_s = parts[0].strip(), parts[1].strip()
            lhs = parse_linear_expr(lhs_s, var_map)
            rhs = parse_linear_expr(rhs_s, var_map)
            if lhs is None or rhs is None:
                return None
            if op == "<=":
                return lhs <= rhs
            if op == "<":
                return lhs < rhs
            if op == ">=":
                return lhs >= rhs
            if op == ">":
                return lhs > rhs
            if op == "==":
                return lhs == rhs

    return None


# ============================================================
# Transition relation from assignments
# ============================================================

def build_transition_constraints(
    assigns: List[Tuple[str, str]],
    v_before: Dict[str, Int],
    v_after: Dict[str, Int],
):
    """
    Encode one loop iteration as a sound over-approx:

      for each x:
        if we see x := rhs1; x := rhs2; ... (e.g. from different branches)
        encode:
          x' = rhs1  OR  x' = rhs2 OR ...

      rhs is evaluated in BEFORE-state vars only.

    If we can prove I is inductive for this over-approximation,
    it's inductive for the real loop (CAV-style sound abstraction).
    """
    updates: Dict[str, List] = {}

    for lhs, rhs in assigns:
        if lhs not in v_before or lhs not in v_after:
            continue
        rhs_z3 = parse_linear_expr(rhs, v_before)
        if rhs_z3 is None:
            continue
        updates.setdefault(lhs, []).append(rhs_z3)

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
    """
    Extract concrete initializations of the form `x := c;` for x in vars_list.
    Used to enforce Init |= I.
    """
    init: Dict[str, int] = {}
    for m in ASSIGN_RE.finditer(prefix):
        lhs = m.group("lhs").strip()
        rhs = m.group("rhs").strip()
        if lhs not in vars_list:
            continue
        if re.fullmatch(r"-?\d+", rhs):
            init[lhs] = int(rhs)
    return init


# ============================================================
# Template configuration
# ============================================================

COEFF_RANGE = range(-3, 4)
C_RANGE = range(-10, 11)


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
    """
    Normalize sum(a_i x_i) <= c:
      - divide by gcd
      - flip so leading non-zero coeff is positive
    """
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


def prune_implied(invariants: Dict[Tuple[int, ...], int]) -> Dict[Tuple[int, ...], int]:
    """
    Keep tightest c for each coefficient vector.
    """
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


# ============================================================
# Inductiveness checks (CAV-style)
# ============================================================

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


# ============================================================
# Week 6: linear invariant synthesis
# ============================================================

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


# ============================================================
# Week 9: Boolean DNF invariants
# ============================================================

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
    coeff_range=COEFF_RANGE,
    c_range=C_RANGE,
    max_atoms: int = 20,
) -> List[BoolAtom]:
    """
    Atoms are linear inequalities from the same template family,
    filtered to be satisfiable under the loop guard.
    """
    atoms: List[BoolAtom] = []
    seen = set()

    for coeffs, c in candidate_linear_templates(vars_list, coeff_range, c_range):
        norm_coeffs, norm_c = normalize_constraint(coeffs, c)
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

        atoms.append(atom)
        seen.add(key)
        if len(atoms) >= max_atoms:
            break

    return atoms


def check_dnf_invariant(
    vars_list: List[str],
    clauses: List[List[BoolAtom]],
    guard_expr,
    trans_constraints,
    initial_vals: Dict[str, int],
) -> bool:
    """
    Check DNF invariant I:

      1. SAT
      2. Init |= I
      3. I & guard & T |= I'
    """
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
    max_clauses: int = 3,
    max_atoms_per_clause: int = 3,
    coeff_range=COEFF_RANGE,
    c_range=C_RANGE,
) -> List[str]:
    """
    Search for DNF invariants of bounded size:

      OR_{k <= max_clauses} AND_{j <= max_atoms_per_clause} (a_ij · x <= c_ij)

    If none found, fall back to linear invariants.
    """
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
        # No usable transition; reuse linear search as best-effort
        return synthesize_linear_invariants_for_loop(src, ms, coeff_range, c_range)

    atoms = collect_candidate_atoms(
        vars_list,
        guard_expr=guard_z3,
        v_before=v_before,
        coeff_range=coeff_range,
        c_range=c_range,
        max_atoms=20,
    )

    if not atoms:
        return synthesize_linear_invariants_for_loop(src, ms, coeff_range, c_range)

    # Build candidate conjunctions (clauses)
    clauses_pool: List[List[BoolAtom]] = []
    seen_clause = set()

    for r in range(1, max_atoms_per_clause + 1):
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

    # Try small DNFs
    for k in range(1, max_clauses + 1):
        for chosen in itertools.combinations(clauses_pool, k):
            clauses = list(chosen)
            if check_dnf_invariant(vars_list, clauses, guard_z3, trans_cs, initial_vals):
                return [format_dnf(clauses, vars_list)]

    # Fallback: linear invariants
    return synthesize_linear_invariants_for_loop(src, ms, coeff_range, c_range)


# ============================================================
# CLI (for auto_verify / manual use)
# ============================================================

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

    # Load / compute summary
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
