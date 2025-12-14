from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Tuple, Set, Any

from z3 import And, Or, Int, IntSort, Array, Select, Store, Solver, Not, sat

ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "week5"))

try:
    import parser as week5_parser  # type: ignore
except ImportError:
    week5_parser = None



@dataclass
class LoopSpec:
    condition: str
    body: str
    prefix: str
    variables: List[str]


# parsing helpers (adapted from week9 with array/list support)

WHILE_RE = re.compile(
    r"while\s*(?:\((?P<cond_paren>[^)]*)\)|(?P<cond_noparen>[^{\n]*))",
    re.MULTILINE,
)

ASSIGN_EXT_RE = re.compile(
    r"(?P<lhs>[A-Za-z_][A-Za-z0-9_]*(?:\[[^\]]+\])?)\s*:=\s*(?P<rhs>[^;]+);"
)

ID_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
ARRAY_ACCESS_RE = re.compile(r"^(?P<arr>[A-Za-z_][A-Za-z0-9_]*)\s*\[\s*(?P<idx>.+)\s*\]$")
LEN_RE = re.compile(r"^(?P<arr>[A-Za-z_][A-Za-z0-9_]*)\.Length$")


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


def parse_assignments_ext(code: str) -> List[Tuple[str, str]]:
    assigns: List[Tuple[str, str]] = []
    for m in ASSIGN_EXT_RE.finditer(code):
        lhs = m.group("lhs").strip()
        rhs = m.group("rhs").strip()
        assigns.append((lhs, rhs))
    return assigns


def remove_nested_loops(code: str) -> str:
    """Strip inner while-blocks so outer-loop transitions stay manageable."""
    text = strip_comments(code)
    out_parts: List[str] = []
    idx = 0
    while True:
        m = WHILE_RE.search(text, idx)
        if not m:
            out_parts.append(text[idx:])
            break
        brace_pos = text.find("{", m.end())
        if brace_pos == -1:
            out_parts.append(text[idx:])
            break
        try:
            end = find_matching_brace(text, brace_pos)
        except ValueError:
            out_parts.append(text[idx:])
            break
        out_parts.append(text[idx:m.start()])
        idx = end + 1
    return "".join(out_parts)


def _clean_cond_text(raw: str) -> str:
    if not raw:
        return ""
    line = raw.splitlines()[0]
    if "decreases" in line:
        line = line.split("decreases", 1)[0]
    return line.strip()


def find_all_loops(src: str) -> List[LoopSpec]:
    code = strip_comments(src)
    loops: List[LoopSpec] = []
    for m in WHILE_RE.finditer(code):
        c_raw = (m.group("cond_paren") or m.group("cond_noparen") or "")
        cond = _clean_cond_text(c_raw)
        brace_pos = code.find("{", m.end())
        if brace_pos == -1:
            continue
        try:
            body_end = find_matching_brace(code, brace_pos)
        except ValueError:
            continue
        body = code[brace_pos + 1 : body_end]
        prefix = code[: m.start()]
        vars_list = sorted({lhs for lhs, _ in parse_assignments_ext(body) if "[" not in lhs})
        loops.append(LoopSpec(condition=cond, body=body, prefix=prefix, variables=vars_list))
    return loops


# expression parsing with arrays/lists


def normalize_index(idx: str) -> str:
    return re.sub(r"\s+", "", idx.strip())


@dataclass
class VarEnv:
    scalars: Dict[str, Any]
    arrays: Dict[str, Any]
    lengths: Dict[str, Any]
    extra_terms: Dict[str, Any]
    array_index_texts: Dict[str, str]


def build_env(
    scalar_vars: Sequence[str],
    array_vars: Sequence[str],
    length_alias: Dict[str, str],
    suffix: str,
) -> VarEnv:
    scalars = {v: Int(f"{v}{suffix}") for v in scalar_vars}
    arrays = {a: Array(f"{a}{suffix}", IntSort(), IntSort()) for a in array_vars}
    lengths = {a: Int(f"len_{a}{suffix}") for a in array_vars if a in length_alias}
    return VarEnv(scalars=scalars, arrays=arrays, lengths=lengths, extra_terms={}, array_index_texts={})


def parse_term_ext(tok: str, env: VarEnv) -> Optional[Any]:
    tok = tok.strip()
    if not tok:
        return None

    # integer constant
    if re.fullmatch(r"-?\d+", tok):
        return int(tok)

    # len(arr) via .Length
    m_len = LEN_RE.match(tok)
    if m_len:
        arr = m_len.group("arr")
        if arr in env.lengths:
            return env.lengths[arr]

    # array access
    m_arr = ARRAY_ACCESS_RE.match(tok)
    if m_arr:
        arr = m_arr.group("arr")
        idx_raw = m_arr.group("idx")
        if arr in env.arrays:
            idx_expr = parse_linear_expr_ext(idx_raw, env)
            if idx_expr is None:
                return None
            key = f"{arr}[{normalize_index(idx_raw)}]"
            env.array_index_texts.setdefault(key, idx_raw)
            term = Select(env.arrays[arr], idx_expr)
            env.extra_terms.setdefault(key, term)
            return term

    # scaled array access: k * (arr[idx])
    m_scaled_arr = re.match(r"^([+-]?\d+)\s*\*\s*(.+)$", tok)
    if m_scaled_arr:
        coef = int(m_scaled_arr.group(1))
        inner = parse_term_ext(m_scaled_arr.group(2), env)
        if inner is not None:
            return coef * inner

    # k * x
    m_scaled = re.match(r"^([+-]?\d+)\s*\*\s*([A-Za-z_][A-Za-z0-9_]*)$", tok)
    if m_scaled:
        coef = int(m_scaled.group(1))
        var = m_scaled.group(2)
        if var in env.scalars:
            return coef * env.scalars[var]

    # plain variable
    if tok in env.scalars:
        return env.scalars[tok]

    return None


def parse_linear_expr_ext(expr: str, env: VarEnv) -> Optional[Any]:
    expr = expr.strip()
    if not expr:
        return None

    tokens = []
    sign = 1
    i = 0
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
        t = parse_term_ext(tok, env)
        if t is None:
            return None
        z3_terms.append(sgn * t)

    if not z3_terms:
        return None

    acc = z3_terms[0]
    for t in z3_terms[1:]:
        acc = acc + t
    return acc


def parse_guard_ext(cond: str, env: VarEnv):
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
                lhs = parse_linear_expr_ext(lhs_s, env)
                rhs = parse_linear_expr_ext(rhs_s, env)
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


def extract_initial_info_from_prefix(
    prefix: str,
    vars_list: List[str],
    env: VarEnv,
) -> Tuple[Dict[str, int], List[Any]]:
    """
    Collect initial assignments appearing before the loop.
    - Numeric constants go into init_vals.
    - Linear, parseable expressions become equality constraints.
    """
    init_vals: Dict[str, int] = {}
    init_constraints: List[Any] = []

    for m in ASSIGN_EXT_RE.finditer(prefix):
        lhs = m.group("lhs").strip()
        rhs = m.group("rhs").strip()
        if "[" in lhs:
            continue
        if lhs not in vars_list:
            continue
        # numeric literal
        if re.fullmatch(r"-?\d+", rhs):
            init_vals[lhs] = int(rhs)
            continue

        # symbolic/linear rhs we can parse
        rhs_expr = parse_linear_expr_ext(rhs, env)
        if rhs_expr is not None and lhs in env.scalars:
            init_constraints.append(env.scalars[lhs] == rhs_expr)

    return init_vals, init_constraints


def build_transition_constraints_ext(
    assigns: List[Tuple[str, str]],
    env_before: VarEnv,
    env_after: VarEnv,
) -> Tuple[Optional[Any], Set[str], Set[str]]:
    scalar_updates: Dict[str, List[Any]] = {}
    array_updates: Dict[str, List[Tuple[Any, Any]]] = {}
    havoc_scalars: Set[str] = set()
    updated_scalars: Set[str] = set()

    for lhs, rhs in assigns:
        rhs_z3 = parse_linear_expr_ext(rhs, env_before)
        if "[" in lhs:
            m = ARRAY_ACCESS_RE.match(lhs)
            if not m:
                continue
            arr = m.group("arr")
            idx_text = m.group("idx")
            idx_expr = parse_linear_expr_ext(idx_text, env_before)
            if arr not in env_before.arrays or rhs_z3 is None or idx_expr is None:
                continue
            key = f"{arr}[{normalize_index(idx_text)}]"
            env_before.array_index_texts.setdefault(key, idx_text)
            array_updates.setdefault(arr, []).append((idx_expr, rhs_z3))
        else:
            if lhs not in env_before.scalars:
                continue
            if rhs_z3 is None:
                havoc_scalars.add(lhs)
                continue
            scalar_updates.setdefault(lhs, []).append(rhs_z3)
            updated_scalars.add(lhs)

    constraints = []

    # scalars
    for v, rhss in scalar_updates.items():
        if len(rhss) == 1:
            constraints.append(env_after.scalars[v] == rhss[0])
        else:
            constraints.append(Or(*[env_after.scalars[v] == r for r in rhss]))

    for v in env_before.scalars:
        if v in scalar_updates or v in havoc_scalars:
            continue
        constraints.append(env_after.scalars[v] == env_before.scalars[v])

    # arrays (store chain)
    for arr, updates in array_updates.items():
        arr_expr = env_before.arrays[arr]
        for idx_expr, rhs_expr in updates:
            arr_expr = Store(arr_expr, idx_expr, rhs_expr)
        constraints.append(env_after.arrays[arr] == arr_expr)

    for arr in env_before.arrays:
        if arr in array_updates:
            continue
        constraints.append(env_after.arrays[arr] == env_before.arrays[arr])

    # lengths stay constant
    for arr, len_before in env_before.lengths.items():
        len_after = env_after.lengths.get(arr)
        if len_after is not None:
            constraints.append(len_after == len_before)

    if not constraints:
        return None, havoc_scalars, updated_scalars
    return And(constraints), havoc_scalars, updated_scalars


# template enumeration 


COEFF_RANGE = range(-2, 3)
C_RANGE = range(-6, 7)
MAX_TEMPLATE_VARS = 4


def candidate_linear_templates(
    vars_list: List[str],
    coeff_range=COEFF_RANGE,
    c_range=C_RANGE,
):
    n = len(vars_list)
    for coeffs in __import__("itertools").product(coeff_range, repeat=n):
        if all(a == 0 for a in coeffs):
            continue
        for c in c_range:
            yield coeffs, c


def normalize_constraint(coeffs: Tuple[int, ...], c: int) -> Tuple[Tuple[int, ...], int]:
    g = 0
    for a in coeffs:
        g = abs(a) if g == 0 else __import__("math").gcd(g, abs(a))
    g = __import__("math").gcd(g, abs(c)) if g != 0 else abs(c)
    if g and g > 1:
        coeffs = tuple(a // g for a in coeffs)
        c //= g
    # ensure leading coefficient non-negative for uniqueness
    for a in coeffs:
        if a < 0:
            coeffs = tuple(-x for x in coeffs)
            c = -c
            break
        if a > 0:
            break
    return coeffs, c


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


def check_linear_invariant_ext(
    vars_list: List[str],
    coeffs: Tuple[int, ...],
    c: int,
    guard_expr,
    trans_constraints,
    v_before: Dict[str, Any],
    v_after: Dict[str, Any],
    initial_vals: Dict[str, int],
    initial_constraints: List[Any],
) -> bool:
    length_nonneg = [v_before[name] >= 0 for name in v_before if name.startswith("len(")]
    length_nonneg_next = [v_after[name] >= 0 for name in v_after if name.startswith("len(")]

    lhs = sum(coeffs[i] * v_before[vars_list[i]] for i in range(len(vars_list)))
    lhs_next = sum(coeffs[i] * v_after[vars_list[i]] for i in range(len(vars_list)))
    inv = lhs <= c
    inv_next = lhs_next <= c

    # satisfiable (non-contradictory)
    s_sat = Solver()
    if length_nonneg:
        s_sat.add(*length_nonneg)
    s_sat.add(inv)
    if s_sat.check() != sat:
        return False

    # initialization
    s_init = Solver()
    if length_nonneg:
        s_init.add(*length_nonneg)
    for v, val in initial_vals.items():
        if v in v_before:
            s_init.add(v_before[v] == val)
    if initial_constraints:
        s_init.add(*initial_constraints)
    if guard_expr is not None:
        s_init.add(guard_expr)
    s_init.add(Not(inv))
    if s_init.check() == sat:
        return False

    # inductiveness
    if trans_constraints is not None:
        s_ind = Solver()
        if length_nonneg:
            s_ind.add(*length_nonneg)
        if length_nonneg_next:
            s_ind.add(*length_nonneg_next)
        s_ind.add(inv)
        if guard_expr is not None:
            s_ind.add(guard_expr)
        s_ind.add(trans_constraints)
        s_ind.add(Not(inv_next))
        if s_ind.check() == sat:
            return False

    return True


def normalize_var_name(token: str) -> str:
    token = token.strip()
    m_len = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\.Length$", token)
    if m_len:
        return f"len({m_len.group(1)})"
    m_arr = re.match(r"^([A-Za-z_][A-Za-z0-9_]*)\\[(.+)\\]$", token)
    if m_arr:
        return f"{m_arr.group(1)}[{normalize_index(m_arr.group(2))}]"
    return token


def guard_based_candidates(
    condition: str,
    var_names: List[str],
    guard_expr,
    trans_constraints,
    v_before: Dict[str, Any],
    v_after: Dict[str, Any],
    initial_vals: Dict[str, int],
    initial_constraints: List[Any],
) -> List[str]:
    candidates: List[str] = []
    seen = set()

    pattern = re.compile(
        r"(?P<lhs>[A-Za-z_][A-Za-z0-9_]*(?:\[[^\]]+\]|\.Length)?)\s*(?P<op><=|>=|<|>)\s*(?P<rhs>-?\d+|[A-Za-z_][A-Za-z0-9_]*(?:\[[^\]]+\]|\.Length)?)"
    )
    for m in pattern.finditer(condition or ""):
        lhs_tok = m.group("lhs")
        rhs_tok = m.group("rhs")
        op = m.group("op")
        lhs = normalize_var_name(lhs_tok)
        rhs_name = normalize_var_name(rhs_tok)

        if lhs not in var_names:
            continue

        coeffs = [0] * len(var_names)
        const = 0

        rhs_is_const = False
        try:
            rhs_const = int(rhs_name)
            rhs_is_const = True
        except ValueError:
            rhs_const = 0

        if not rhs_is_const and rhs_name not in var_names:
            continue

        if rhs_is_const:
            idx_l = var_names.index(lhs)
            coeffs[idx_l] = 1
            if op == "<":
                const = rhs_const - 1
            elif op == "<=":
                const = rhs_const
            elif op == ">":
                coeffs[idx_l] = -1
                const = -rhs_const - 1
            elif op == ">=":
                coeffs[idx_l] = -1
                const = -rhs_const
        else:
            idx_l = var_names.index(lhs)
            idx_r = var_names.index(rhs_name)
            coeffs[idx_l] = 1
            coeffs[idx_r] = -1
            if op == "<":
                const = -1
            elif op == "<=":
                const = 0
            elif op == ">":
                coeffs = [-c for c in coeffs]
                const = -1
            elif op == ">=":
                coeffs = [-c for c in coeffs]
                const = 0

        norm_coeffs, norm_c = normalize_constraint(tuple(coeffs), const)
        key = (norm_coeffs, norm_c)
        if key in seen:
            continue
        seen.add(key)
        if check_linear_invariant_ext(
            var_names,
            norm_coeffs,
            norm_c,
            guard_expr,
            trans_constraints,
            v_before,
            v_after,
            initial_vals,
            initial_constraints,
        ):
            s = pretty_print_linear(var_names, norm_coeffs, norm_c)
            if s:
                candidates.append(s)

    return candidates


# invariant synthesis 


def adapt_method_summary(raw: Dict[str, Any]) -> Dict[str, Any]:
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


def extract_identifiers(text: str) -> Set[str]:
    return set(ID_RE.findall(text or ""))


def synthesize_linear_invariants_for_loop(
    loop: LoopSpec,
    coeff_range=COEFF_RANGE,
    c_range=C_RANGE,
    max_invariants: int = 5,
    max_candidates: int = 25000,
) -> Tuple[List[str], Dict[str, Any]]:
    body_shallow = remove_nested_loops(loop.body)
    assigns = parse_assignments_ext(body_shallow)

    arrays: Set[str] = set()
    for txt in [loop.condition, body_shallow]:
        for m in re.finditer(r"([A-Za-z_][A-Za-z0-9_]*)\s*\[", txt or ""):
            arrays.add(m.group(1))
        for m in re.finditer(r"([A-Za-z_][A-Za-z0-9_]*)\.Length", txt or ""):
            arrays.add(m.group(1))

    scalar_vars: Set[str] = set(loop.variables or [])
    for lhs, rhs in assigns:
        if "[" in lhs:
            base = lhs.split("[", 1)[0].strip()
            if base not in arrays:
                arrays.add(base)
        else:
            scalar_vars.add(lhs)
        scalar_vars.update(extract_identifiers(rhs))
    scalar_vars.update(extract_identifiers(loop.condition))
    relevant_ids = extract_identifiers(body_shallow) | extract_identifiers(loop.condition)
    scalar_vars &= relevant_ids
    scalar_vars.discard("Length")
    scalar_vars -= arrays  # arrays handled separately

    length_alias = {a: f"len({a})" for a in arrays}

    env_before = build_env(sorted(scalar_vars), sorted(arrays), length_alias, suffix="")
    env_after = build_env(sorted(scalar_vars), sorted(arrays), length_alias, suffix="_next")

    guard_z3 = parse_guard_ext(loop.condition, env_before)
    trans_cs, havoc_scalars, updated_scalars = build_transition_constraints_ext(assigns, env_before, env_after)

    # ensure array terms created in both envs
    for key, idx_text in env_before.array_index_texts.items():
        if key not in env_after.extra_terms:
            if key in env_after.array_index_texts:
                idx_text = env_after.array_index_texts[key]
            parse_term_ext(f"{key}", env_after)  # triggers creation if parsable
            if key not in env_after.extra_terms:
                # fall back to manual creation using stored idx text
                m = ARRAY_ACCESS_RE.match(key)
                if m and m.group("arr") in env_after.arrays:
                    idx_expr = parse_linear_expr_ext(idx_text, env_after)
                    if idx_expr is not None:
                        env_after.extra_terms[key] = Select(env_after.arrays[m.group("arr")], idx_expr)

    # length vars are not explicit in expressions until parsed
    for arr in arrays:
        _ = env_before.lengths.get(arr)
        _ = env_after.lengths.get(arr)

    # collect variable names in deterministic order
    filtered_scalars = [v for v in scalar_vars if v not in havoc_scalars]
    priority_vars = extract_identifiers(loop.condition)
    priority_vars.discard("Length")
    priority_vars -= arrays
    priority_vars |= updated_scalars

    ordered_scalars: List[str] = []
    for v in sorted(priority_vars):
        if v in filtered_scalars and v not in ordered_scalars:
            ordered_scalars.append(v)
    for v in sorted(filtered_scalars):
        if v not in ordered_scalars:
            ordered_scalars.append(v)
    if len(ordered_scalars) > MAX_TEMPLATE_VARS:
        ordered_scalars = ordered_scalars[:MAX_TEMPLATE_VARS]

    var_names: List[str] = []
    var_names.extend(ordered_scalars)
    var_names.extend(sorted(length_alias.values()))
    var_names.extend(sorted(env_before.extra_terms.keys()))

    v_before_exprs: Dict[str, Any] = {}
    v_after_exprs: Dict[str, Any] = {}
    for v in ordered_scalars:
        v_before_exprs[v] = env_before.scalars[v]
        v_after_exprs[v] = env_after.scalars[v]
    for arr, alias in length_alias.items():
        if arr in env_before.lengths and arr in env_after.lengths:
            v_before_exprs[alias] = env_before.lengths[arr]
            v_after_exprs[alias] = env_after.lengths[arr]
    for key in env_before.extra_terms:
        if key in env_before.extra_terms:
            v_before_exprs[key] = env_before.extra_terms[key]
        if key in env_after.extra_terms:
            v_after_exprs[key] = env_after.extra_terms[key]

    initial_vals, initial_constraints = extract_initial_info_from_prefix(
        loop.prefix, list(ordered_scalars), env_before
    )

    found: List[Tuple[Tuple[int, ...], int, str]] = []
    seen = set()
    attempts = 0

    for coeffs, c in candidate_linear_templates(var_names, coeff_range, c_range):
        attempts += 1
        if attempts > max_candidates:
            break
        norm_coeffs, norm_c = normalize_constraint(tuple(coeffs), c)
        key = (norm_coeffs, norm_c)
        if key in seen:
            continue
        seen.add(key)
        if check_linear_invariant_ext(
            var_names,
            norm_coeffs,
            norm_c,
            guard_z3,
            trans_cs,
            v_before_exprs,
            v_after_exprs,
            initial_vals,
            initial_constraints,
        ):
            s = pretty_print_linear(var_names, norm_coeffs, norm_c)
            if s:
                found.append((norm_coeffs, norm_c, s))
                if len(found) >= max_invariants:
                    break

    invariants = [s for _, _, s in found]

    if not invariants:
        guard_fallback = guard_based_candidates(
            loop.condition,
            var_names,
            guard_z3,
            trans_cs,
            v_before_exprs,
            v_after_exprs,
            initial_vals,
            initial_constraints,
        )
        invariants.extend(guard_fallback)

    debug_info = {
        "variables": var_names,
        "arrays": sorted(arrays),
        "lengths": sorted(length_alias.values()),
        "array_accesses": sorted(env_before.extra_terms.keys()),
        "attempts": attempts,
    }

    return invariants, debug_info


def synthesize_invariants_for_file(
    src_path: pathlib.Path,
    summary_json: Optional[pathlib.Path] = None,
    coeff_range=COEFF_RANGE,
    c_range=C_RANGE,
    max_invariants: int = 5,
    max_candidates: int = 25000,
) -> Dict[str, Any]:
    src = src_path.read_text(encoding="utf-8")
    if summary_json is not None:
        try:
            raw_summary = json.loads(summary_json.read_text(encoding="utf-8"))
        except Exception:
            raw_summary = {}
    elif week5_parser is not None:
        try:
            raw_summary = week5_parser.run_parser(str(src_path))  # type: ignore[attr-defined]
        except Exception:
            raw_summary = {}
    else:
        raw_summary = {}

    ms = adapt_method_summary(raw_summary)

    loops = find_all_loops(src)
    results = []
    for idx, loop in enumerate(loops):
        invs, dbg = synthesize_linear_invariants_for_loop(
            loop,
            coeff_range=coeff_range,
            c_range=c_range,
            max_invariants=max_invariants,
            max_candidates=max_candidates,
        )
        results.append(
            {
                "loop_id": idx,
                "condition": loop.condition,
                "variables": loop.variables,
                "invariants": invs,
                "array_debug": dbg,
            }
        )

    return {
        "file": str(src_path),
        "method_name": ms.get("method_name", ""),
        "loops": results,
    }


# CLI 

def main():
    ap = argparse.ArgumentParser(
        description="Week 12: Array/list aware invariant synthesis (linear templates with array/length support)."
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
        help="Inclusive range for coefficients (default: -2 2).",
    )
    ap.add_argument(
        "--c-range",
        nargs=2,
        type=int,
        metavar=("LOW", "HIGH"),
        help="Inclusive range for constant term c (default: -6 6).",
    )
    ap.add_argument(
        "--max",
        type=int,
        default=5,
        help="Maximum number of invariants to emit per loop (default: 5).",
    )
    ap.add_argument(
        "--max-candidates",
        type=int,
        default=25000,
        help="Maximum candidate templates to check (default: 25000).",
    )
    ap.add_argument(
        "--out",
        help="Write JSON result to this path (prints to stdout if omitted).",
    )

    args = ap.parse_args()

    coeff_range = COEFF_RANGE
    c_range = C_RANGE

    if args.coeff_range:
        lo, hi = args.coeff_range
        coeff_range = range(lo, hi + 1)
    if args.c_range:
        lo, hi = args.c_range
        c_range = range(lo, hi + 1)

    src_path = pathlib.Path(args.file)
    summary_path = pathlib.Path(args.summary) if args.summary else None

    result = synthesize_invariants_for_file(
        src_path,
        summary_json=summary_path,
        coeff_range=coeff_range,
        c_range=c_range,
        max_invariants=args.max,
        max_candidates=args.max_candidates,
    )

    if args.out:
        out_path = pathlib.Path(args.out)
        out_path.write_text(json.dumps(result, indent=2), encoding="utf-8")
    else:
        print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
