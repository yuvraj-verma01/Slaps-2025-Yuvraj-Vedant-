from __future__ import annotations

import re
from typing import Dict, List, Optional, Set, Tuple

from .patch_schema import LoopPatch, Patch, RewritePatch


def _replace_placeholder_lines(text: str, keyword: str, values: List[str]) -> Tuple[str, List[str]]:
    warnings: List[str] = []
    pattern = re.compile(rf"^(?P<indent>\s*)//\s*@{keyword}_placeholder\s*$", re.MULTILINE)

    def repl(match: re.Match) -> str:
        indent = match.group("indent")
        if values:
            return "\n".join(f"{indent}{keyword} {v}" for v in values)
        return f"{indent}// {keyword} placeholder (empty)"

    new_text, count = pattern.subn(repl, text)
    if count == 0 and values:
        warnings.append(f"no placeholder found for {keyword}")
    return new_text, warnings


def _find_loop_placeholders(text: str) -> Set[int]:
    ids: Set[int] = set()
    for m in re.finditer(r"@loop_id:(\d+)", text):
        try:
            ids.add(int(m.group(1)))
        except Exception:
            continue
    return ids


def _replace_loop_placeholders(text: str, loop_patches: List[LoopPatch]) -> Tuple[str, List[str], List[str]]:
    warnings: List[str] = []
    errors: List[str] = []
    loop_map: Dict[int, LoopPatch] = {lp.loop_id: lp for lp in loop_patches}
    matched: set = set()

    def inv_repl(match: re.Match) -> str:
        indent = match.group("indent")
        loop_id = int(match.group("loop_id"))
        matched.add(loop_id)
        lp = loop_map.get(loop_id)
        if lp and lp.invariants:
            return "\n".join(f"{indent}invariant {inv}" for inv in lp.invariants)
        return match.group(0)

    def dec_repl(match: re.Match) -> str:
        indent = match.group("indent")
        loop_id = int(match.group("loop_id"))
        matched.add(loop_id)
        lp = loop_map.get(loop_id)
        if lp and lp.decreases:
            return f"{indent}decreases {lp.decreases};"
        return match.group(0)

    inv_pattern = re.compile(
        r"^(?P<indent>\s*)invariant\s+true\s*//\s*@inv_placeholder:(?P<loop_id>\d+)\s*$",
        re.MULTILINE,
    )
    dec_pattern = re.compile(
        r"^(?P<indent>\s*)decreases\s+\*\s*//\s*@dec_placeholder:(?P<loop_id>\d+);?\s*$",
        re.MULTILINE,
    )

    text, _ = inv_pattern.subn(inv_repl, text)
    text, _ = dec_pattern.subn(dec_repl, text)

    for lid in loop_map:
        if lid not in matched:
            warnings.append(f"loop placeholder not found for loop_id {lid}")
    return text, warnings, errors


def _apply_types(text: str, type_map: Dict[str, str]) -> Tuple[str, List[str]]:
    warnings: List[str] = []
    for name, new_type in type_map.items():
        replaced_any = False
        param_pattern = re.compile(rf"(\b{name}\s*:\s*)([A-Za-z0-9_<>\[\]]+)")
        text, n = param_pattern.subn(rf"\1{new_type}", text)
        if n:
            replaced_any = True
        local_pattern = re.compile(rf"(^\s*var\s+{name}\s*:\s*)([^;:=]+)", re.MULTILINE)
        text, n = local_pattern.subn(rf"\1{new_type}", text)
        if n:
            replaced_any = True
        if not replaced_any:
            warnings.append(f"type patch for '{name}' not applied (no match)")
    return text, warnings


def _apply_rewrites(text: str, rewrites: List[RewritePatch]) -> Tuple[str, List[str]]:
    warnings: List[str] = []
    for rw in rewrites:
        f = rw.from_text
        t = rw.to_text
        applied = False
        if f == "True" and t == "true":
            text = text.replace("True", "true")
            applied = True
        elif f == "False" and t == "false":
            text = text.replace("False", "false")
            applied = True
        else:
            m_from = re.fullmatch(r"len\(\s*([A-Za-z0-9_\.]+)\s*\)", f)
            m_to = re.fullmatch(r"\|\s*([A-Za-z0-9_\.]+)\s*\|", t)
            if m_from and m_to and m_from.group(1) == m_to.group(1):
                pattern = re.compile(re.escape(f))
                text, n = pattern.subn(t, text)
                applied = n > 0
            else:
                warnings.append(f"rewrite '{f}' -> '{t}' not in whitelist; skipped")
        if not applied and (f == "True" or f == "False" or "len(" in f):
            warnings.append(f"rewrite '{f}' not applied (no occurrences)")
    return text, warnings


def apply_patch(code: str, patch: Patch) -> Tuple[str, List[str], List[str]]:
    warnings: List[str] = []
    errors: List[str] = []

    code, w = _replace_placeholder_lines(code, "requires", patch.requires)
    warnings.extend(w)
    code, w = _replace_placeholder_lines(code, "ensures", patch.ensures)
    warnings.extend(w)

    code, w, e = _replace_loop_placeholders(code, patch.loops)
    warnings.extend(w)
    errors.extend(e)

    code, w = _apply_types(code, patch.types)
    warnings.extend(w)
    code, w = _apply_rewrites(code, patch.rewrites)
    warnings.extend(w)

    return code, warnings, errors


__all__ = ["apply_patch"]
