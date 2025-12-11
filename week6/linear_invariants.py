from __future__ import annotations
import re
import json
from math import gcd as math_gcd
import itertools
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

from z3 import Int, Solver, And, Not, sat

import sys
import pathlib

sys.path.append(str(pathlib.Path(__file__).resolve().parent.parent / "week5"))
import parser as week5_parser  




@dataclass
class LoopSpec:
    condition: str
    variables: List[str]
    body: str      
    prefix: str    


# dafny helpers 

IDENT = r"[A-Za-z_][A-Za-z0-9_]*"

WHILE_RE = re.compile(r"\bwhile\s*\((?P<cond>[^)]*)\)")
FOR_RE = re.compile(
    r"\bfor\s+(?P<var>" + IDENT + r")\s*:=\s*(?P<start>[^\s]+)\s*to\s*(?P<end>[^\s{]+)"
)

ASSIGN_RE = re.compile(
    rf"\b(?P<lhs>{IDENT})\s*:=\s*(?P<rhs>[^;]+);"
)


def strip_comments(src: str) -> str:
    """Strip // and /* ... */ comments."""
    src = re.sub(r"/\*.*?\*/", "", src, flags=re.DOTALL)
    src = re.sub(r"//.*", "", src)
    return src

def summarize_methods_from_src(src_path: pathlib.Path) -> Dict:
    return week5_parser.run_parser(str(src_path))



def find_matching_brace(s: str, start: int) -> int:
    """return index of matching '}' for '{' at start."""
    assert s[start] == "{"
    depth = 0
    for i in range(start, len(s)):
        if s[i] == "{":
            depth += 1
        elif s[i] == "}":
            depth -= 1
            if depth == 0:
                return i
    raise ValueError(f"Unmatched '{{' at {start}")


def parse_assignments(code: str) -> List[Tuple[str, str]]:
    """Extract simple 'x := rhs;' assignments from code."""
    assigns: List[Tuple[str, str]] = []
    for m in ASSIGN_RE.finditer(code):
        lhs = m.group("lhs").strip()
        rhs = m.group("rhs").strip()
        assigns.append((lhs, rhs))
    return assigns


def extract_first_loop_with_body(src: str, loop_cond: str) -> Optional[LoopSpec]:
    """
    Given dafny source and a loop condition string from week 5,
    find the corresponding loop and return its body and the prefix before it.
    """
    code = strip_comments(src)
    want = loop_cond.strip()

    # while loops
    for m in WHILE_RE.finditer(code):
        cond = m.group("cond").strip()
        if cond != want:
            continue

        loop_start = m.start()
        brace_pos = code.find("{", m.end())
        if brace_pos == -1:
            continue

        body_end = find_matching_brace(code, brace_pos)
        body = code[brace_pos + 1: body_end]
        prefix = code[:loop_start]

        return LoopSpec(condition=cond, variables=[], body=body, prefix=prefix)

    # for loops 
    for m in FOR_RE.finditer(code):
        var = m.group("var").strip()
        start_v = m.group("start").strip()
        end_v = m.group("end").strip()
        cond_text = f"{var} from {start_v} to {end_v}"
        if cond_text != want:
            continue

        loop_start = m.start()
        brace_pos = code.find("{", m.end())
        if brace_pos == -1:
            continue

        body_end = find_matching_brace(code, brace_pos)
        body = code[brace_pos + 1: body_end]
        prefix = code[:loop_start]
        return LoopSpec(condition=cond_text, variables=[var], body=body, prefix=prefix)

    return None


def find_first_loop_fallback(src: str) -> Optional[LoopSpec]:
    """
     if Week 5 summary has no loops, syntactically grab the first while/for loop.
    """
    code = strip_comments(src)

    # while-loop 
    m = WHILE_RE.search(code)
    if m:
        cond = m.group("cond").strip()
        loop_start = m.start()
        brace_pos = code.find("{", m.end())
        if brace_pos != -1:
            body_end = find_matching_brace(code, brace_pos)
            body = code[brace_pos + 1: body_end]
            prefix = code[:loop_start]
            vars_in_body = sorted({lhs for (lhs, _) in parse_assignments(body)})
            return LoopSpec(condition=cond, variables=vars_in_body, body=body, prefix=prefix)

    # for loop
    m = FOR_RE.search(code)
    if m:
        var = m.group("var").strip()
        start_v = m.group("start").strip()
        end_v = m.group("end").strip()
        cond_text = f"{var} from {start_v} to {end_v}"
        loop_start = m.start()
        brace_pos = code.find("{", m.end())
        if brace_pos != -1:
            body_end = find_matching_brace(code, brace_pos)
            body = code[brace_pos + 1: body_end]
            prefix = code[:loop_start]
            vars_in_body = {lhs for (lhs, _) in parse_assignments(body)}
            vars_all = [var] + sorted(v for v in vars_in_body if v != var)
            return LoopSpec(condition=cond_text, variables=vars_all, body=body, prefix=prefix)

    return None
def parse_for_condition(cond_text: str) -> Optional[Tuple[str, str, str]]:
    """
    Parse a for-loop condition string of the form "i from start to end".
    Returns (var, start_expr, end_expr) or None if not a match.
    """
    m = re.match(r"^(?P<var>" + IDENT + r")\s+from\s+(?P<start>.+?)\s+to\s+(?P<end>.+)$", cond_text.strip())
    if not m:
        return None
    return m.group("var"), m.group("start"), m.group("end")

# Z3 helpers

def parse_linear_expr(expr: str, var_map: Dict[str, Int]):
    """
    parse a tiny fragment of linear integer expressions into a Z3 expr with integers, variables, '+' and '-' between them.
    return None if unsupported.
    """
    expr = expr.strip()
    if not expr:
        return None

    tokens = []
    i = 0
    while i < len(expr):
        c = expr[i]
        if c in "+-":
            tokens.append(c)
            i += 1
        elif c.isspace():
            i += 1
        else:
            j = i
            while j < len(expr) and not expr[j].isspace() and expr[j] not in "+-":
                j += 1
            tokens.append(expr[i:j])
            i = j

    if not tokens:
        return None

    def term_to_z3(tok: str):
        if tok in var_map:
            return var_map[tok]
        try:
            return int(tok)
        except ValueError:
            return None

    # Expect: term [op term]*
    if tokens[0] in ["+", "-"]:
        return None

    z = term_to_z3(tokens[0])
    if z is None:
        return None

    idx = 1
    while idx < len(tokens) - 1:
        op = tokens[idx]
        t_tok = tokens[idx + 1]
        t = term_to_z3(t_tok)
        if t is None:
            return None

        if op == "+":
            z = z + t
        elif op == "-":
            z = z - t
        else:
            return None

        idx += 2

    if idx != len(tokens):
        return None

    return z


def build_transition_constraints(
    assigns: List[Tuple[str, str]],
    vars_before: Dict[str, Int],
    vars_after: Dict[str, Int],
):
    """
    for each assignment 'x := rhs', build vars_after[x] = rhs(vars_before) if rhs is linear.
    for variables never assigned in the loop, enforce vars_after[x] = vars_before[x].
    for variables assigned with non-linear/unsupported rhs, leave vars_after[x] unconstrained.
    """
    constraints = []
    assigned = set()

    for lhs, rhs in assigns:
        if lhs not in vars_before:
            continue

        assigned.add(lhs)
        rhs_z3 = parse_linear_expr(rhs, vars_before)
        if rhs_z3 is None:
            continue

        constraints.append(vars_after[lhs] == rhs_z3)

    # Variables never assigned in the loop remain unchanged.
    for v in vars_before:
        if v not in assigned:
            constraints.append(vars_after[v] == vars_before[v])

    return constraints


def parse_guard(cond: str, vars_before: Dict[str, Int]):
    """
    Parse a very small fragment of guard: conjunction with &&, atoms like a <= b, a < b, a >= b, a > b, a == b, a must be a loop var; b is loop var or int
    """
    cond = cond.strip()
    if not cond:
        return None

    parts = [p.strip() for p in cond.split("&&") if p.strip()]
    zparts = []

    cmp_re = re.compile(
        rf"^(?P<a>{IDENT})\s*(?P<op><=|<|>=|>|==)\s*(?P<b>{IDENT}|-?\d+)$"
    )

    for p in parts:
        m = cmp_re.match(p)
        if not m:
            continue

        a = m.group("a")
        op = m.group("op")
        b = m.group("b")

        if a not in vars_before:
            continue

        a_z3 = vars_before[a]

        if b in vars_before:
            b_z3 = vars_before[b]
        else:
            try:
                b_z3 = int(b)
            except ValueError:
                continue

        if op == "<=":
            zparts.append(a_z3 <= b_z3)
        elif op == "<":
            zparts.append(a_z3 < b_z3)
        elif op == ">=":
            zparts.append(a_z3 >= b_z3)
        elif op == ">":
            zparts.append(a_z3 > b_z3)
        elif op == "==":
            zparts.append(a_z3 == b_z3)

    if not zparts:
        return None
    if len(zparts) == 1:
        return zparts[0]
    return And(*zparts)


# invariant synthesis 
def candidate_linear_templates(
    variables: List[str],
    coeff_range=range(-2, 3),
    c_range=range(-5, 6),
):
    """
    generate templates of form sum(ai * xi) <= c with small integer coeffs.
    """
    for coeffs in itertools.product(coeff_range, repeat=len(variables)):
        if all(a == 0 for a in coeffs):
            continue
        for c in c_range:
            yield coeffs, c


def extract_initial_values_from_prefix(
    prefix: str,
    loop_vars: List[str],
) -> Dict[str, int]:
    assigns = parse_assignments(prefix)
    init: Dict[str, int] = {}

    for lhs, rhs in assigns:
        if lhs not in loop_vars:
            continue
        try:
            val = int(rhs)
        except ValueError:
            continue
        init[lhs] = val

    return init


def check_template_is_invariant(
    vars_list: List[str],
    preconds: List[str],
    guard_expr,
    trans_constraints,
    v_before: Dict[str, Int],
    v_after: Dict[str, Int],
    coeffs,
    c,
    initial_vals: Dict[str, int],
) -> bool:
    """
    Check template sum(ai * xi) <= c is a valid loop invariant:
      1. Initialization: holds at approximated loop entry.
      2. Preservation: (I ∧ guard ∧ T) ⇒ I'.
      3. Termination: I is satisfiable.
    """
    inv_before = sum(coeffs[i] * v_before[v] for i, v in enumerate(vars_list)) <= c
    inv_after = sum(coeffs[i] * v_after[v] for i, v in enumerate(vars_list)) <= c

    # 1 initialization
    if initial_vals:
        s_init = Solver()
        for v, val in initial_vals.items():
            if v in v_before:
                s_init.add(v_before[v] == val)
        s_init.add(Not(inv_before))
        if s_init.check() == sat:
            return False

    # 3 termination
    s_sat = Solver()
    s_sat.add(inv_before)
    if s_sat.check() != sat:
        return False

    # 2 preservation
    s_pres = Solver()
    s_pres.add(trans_constraints)
    if guard_expr is not None:
        s_pres.add(guard_expr)
    s_pres.add(inv_before)
    s_pres.add(Not(inv_after))
    if s_pres.check() == sat:
        return False

    return True


def normalize_coeffs(coeffs: Tuple[int, ...], c: int) -> Tuple[Tuple[int, ...], int]:
    """
    Normalize (coeffs, c) by dividing by gcd of all coeffs and c.
    """
    g = 0
    for a in coeffs:
        g = math_gcd(g, abs(a))
    g = math_gcd(g, abs(c))
    if g > 1:
        coeffs = tuple(a // g for a in coeffs)
        c = c // g
    else:
        coeffs = tuple(coeffs)
    return coeffs, c


def invariant_implies(
    coeffs_strong: Tuple[int, ...],
    c_strong: int,
    coeffs_weak: Tuple[int, ...],
    c_weak: int,
) -> bool:
    assert len(coeffs_strong) == len(coeffs_weak)
    n = len(coeffs_strong)

    j = None
    for k in range(n):
        if coeffs_strong[k] != 0 or coeffs_weak[k] != 0:
            j = k
            break
    if j is None:
        return False

    a1 = coeffs_strong[j]
    a2 = coeffs_weak[j]
    if a1 == 0 or a2 == 0:
        return False

    if a1 * a2 <= 0:
        return False

    for k in range(n):
        b1 = coeffs_strong[k]
        b2 = coeffs_weak[k]
        if b1 == 0 and b2 == 0:
            continue
        if b1 == 0 or b2 == 0:
            return False
        if b2 * a1 != b1 * a2:
            return False

    ln = abs(a2)
    ld = abs(a1)
    return c_weak * ld >= c_strong * ln


def prune_implied(invariant_map: Dict[Tuple[int, ...], int]) -> Dict[Tuple[int, ...], int]:
    """
    drop invariants that are logically implied by another one
    """
    items = list(invariant_map.items())
    n = len(items)
    keep = [True] * n

    for j in range(n):
        if not keep[j]:
            continue
        coeffs_j, c_j = items[j]
        for i in range(n):
            if i == j or not keep[i]:
                continue
            coeffs_i, c_i = items[i]
            if invariant_implies(coeffs_i, c_i, coeffs_j, c_j):
                keep[j] = False
                break

    new_map: Dict[Tuple[int, ...], int] = {}
    for idx, ok in enumerate(keep):
        if ok:
            coeffs, c = items[idx]
            new_map[coeffs] = c
    return new_map


def synthesize_linear_invariants_for_loop(
    src: str,
    method_summary: Dict,
    loop_info: Optional[Dict] = None,
    coeff_range=range(-2, 3),
    c_range=range(-5, 6),
    max_invariants: int = 5,
) -> List[str]:
    """
    Main Week 6 routine:
      - week 5 summary to locate the loop.
      - fallback to simple syntactic detection if summary has no loops.
      - build linear transition system and synthesize inductive invariants.
    """
    loops = method_summary.get("loops", [])

    # Step 1: locate loop & variables & condition
    loop_spec: Optional[LoopSpec] = None
    cond: str = ""
    vars_list: List[str] = []

    if loop_info is None and loops:
        # Use first loop from week 5 summary
        loop_info = loops[0]
        if loop_info:
            cond = (loop_info.get("condition") or "").strip()
            vars_list = list(loop_info.get("variables") or [])
        if cond:
            loop_spec = extract_first_loop_with_body(src, cond)
    if loop_spec is None:
        # fallback: detect first loop syntactically
        loop_spec = find_first_loop_fallback(src)

    if loop_spec is None:
        return []

    # if vars_list empty or missing, infer from LoopSpec / assignments
    if not vars_list:
        body_assigns = parse_assignments(loop_spec.body)
        vars_list = sorted({lhs for (lhs, _) in body_assigns})

    if not vars_list:
        return []

    cond = loop_spec.condition
    guard_cond = cond

    # derive guard/initial value hints for for-loops using structured condition text
    if loop_info and loop_info.get("type") == "for":
        parsed = parse_for_condition(loop_info.get("condition", ""))
        if parsed:
            f_var, f_start, f_end = parsed
            guard_cond = f"{f_var} <= {f_end}"
            if f_var not in vars_list:
                vars_list = vars_list + [f_var]

    # step 2: build constraints
    assigns = parse_assignments(loop_spec.body)
    initial_vals = extract_initial_values_from_prefix(loop_spec.prefix, vars_list)
    if loop_info and loop_info.get("type") == "for":
        parsed = parse_for_condition(loop_info.get("condition", ""))
        if parsed:
            f_var, f_start, _ = parsed
            try:
                start_int = int(f_start)
            except ValueError:
                start_int = None
            if start_int is not None and f_var not in initial_vals:
                initial_vals[f_var] = start_int

    v_before = {v: Int(v) for v in vars_list}
    v_after = {v: Int(v + "_next") for v in vars_list}

    trans_cs = build_transition_constraints(assigns, v_before, v_after)
    if not trans_cs:
        return []

    guard_z3 = parse_guard(guard_cond, v_before)
    preconds = method_summary.get("preconditions", [])

    # step 3: enumerate templates and check invariants
    invariant_map: Dict[Tuple[int, ...], int] = {}

    for coeffs, c in candidate_linear_templates(vars_list, coeff_range, c_range):
        if check_template_is_invariant(
            vars_list=vars_list,
            preconds=preconds,
            guard_expr=guard_z3,
            trans_constraints=trans_cs,
            v_before=v_before,
            v_after=v_after,
            coeffs=coeffs,
            c=c,
            initial_vals=initial_vals,
        ):
            norm_coeffs, norm_c = normalize_coeffs(coeffs, c)
            if norm_coeffs in invariant_map:
                if norm_c < invariant_map[norm_coeffs]:
                    invariant_map[norm_coeffs] = norm_c
            else:
                invariant_map[norm_coeffs] = norm_c

    # step 4: prune implied invariants & pretty-print
    invariant_map = prune_implied(invariant_map)

    invariants: List[str] = []
    for coeffs, c in sorted(invariant_map.items()):
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
            continue
        lhs = " + ".join(terms).replace("+ -", "- ")
        inv_str = f"{lhs} <= {c}"
        invariants.append(inv_str)
        if len(invariants) >= max_invariants:
            break

    return invariants
def synthesize_linear_invariants_for_method(
    src: str,
    method_summary: Dict,
    coeff_range=range(-2, 3),
    c_range=range(-5, 6),
    max_invariants: int = 5,
) -> List[Dict]:
    """
    Synthesize invariants for every loop in a method summary.
    if a method has no loops we return an empty list.
    """
    results: List[Dict] = []
    for loop in method_summary.get("loops", []):
        invs = synthesize_linear_invariants_for_loop(
            src,
            method_summary,
            loop_info=loop,
            coeff_range=coeff_range,
            c_range=c_range,
            max_invariants=max_invariants,
        )
        results.append({"loop": loop, "synthesized_invariants": invs})
    return results


# CLI 

def main():
    import argparse

    ap = argparse.ArgumentParser(
        description=" Linear Invariant Synthesis Tool "
    )
    ap.add_argument("source", help="Path to a .dfy file")
    ap.add_argument(
        "--out",
        help="Optional JSON output path for synthesized invariants",
        default=None,
    )
    args = ap.parse_args()

    src_path = pathlib.Path(args.source)
    src = src_path.read_text(encoding="utf-8")

    summary = summarize_methods_from_src(src_path)
    method_summaries = summary.get("methods", [])

    methods_out: List[Dict] = []
    for m_summary in method_summaries:
        loop_results = synthesize_linear_invariants_for_method(
            src,
            m_summary,
        )

        loop_entries = []
        for item in loop_results:
            loop_copy = dict(item.get("loop", {}))
            loop_copy["synthesized_invariants"] = item.get(
                "synthesized_invariants", []
            )
            loop_entries.append(loop_copy)

        methods_out.append(
            {
                "method_name": m_summary.get("method_name"),
                "preconditions": m_summary.get("preconditions", []),
                "postconditions": m_summary.get("postconditions", []),
                "parameters": m_summary.get("parameters", []),
                "returns": m_summary.get("returns", []),
                "loops": loop_entries,
            }
        )

    result = {"methods": methods_out}
    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
        print(f"Saved synthesized invariants to {out_path}")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
