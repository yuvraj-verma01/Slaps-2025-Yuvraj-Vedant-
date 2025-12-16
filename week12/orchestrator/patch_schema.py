from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple


ALLOWED_KEYS = {"requires", "ensures", "types", "rewrites", "loops"}


@dataclass
class RewritePatch:
    from_text: str
    to_text: str


@dataclass
class LoopPatch:
    loop_id: int
    invariants: List[str] = field(default_factory=list)
    decreases: Optional[str] = None


@dataclass
class Patch:
    requires: List[str] = field(default_factory=list)
    ensures: List[str] = field(default_factory=list)
    types: Dict[str, str] = field(default_factory=dict)
    rewrites: List[RewritePatch] = field(default_factory=list)
    loops: List[LoopPatch] = field(default_factory=list)


def _coerce_str_list(val: Any) -> List[str]:
    if not isinstance(val, list):
        return []
    out: List[str] = []
    for item in val:
        if isinstance(item, str) and item.strip():
            out.append(item.strip())
    return out


def _coerce_types(val: Any) -> Dict[str, str]:
    if not isinstance(val, dict):
        return {}
    out: Dict[str, str] = {}
    for k, v in val.items():
        if isinstance(k, str) and isinstance(v, str) and k.strip() and v.strip():
            out[k.strip()] = v.strip()
    return out


def _coerce_rewrites(val: Any, warnings: List[str]) -> List[RewritePatch]:
    out: List[RewritePatch] = []
    if not isinstance(val, list):
        return out
    for entry in val:
        if not isinstance(entry, dict):
            warnings.append("rewrite entry not an object; skipped")
            continue
        f = entry.get("from")
        t = entry.get("to")
        if isinstance(f, str) and isinstance(t, str):
            out.append(RewritePatch(from_text=f, to_text=t))
        else:
            warnings.append("rewrite entry missing string from/to; skipped")
    return out


def _coerce_loops(val: Any, warnings: List[str]) -> List[LoopPatch]:
    out: List[LoopPatch] = []
    if not isinstance(val, list):
        return out
    for entry in val:
        if not isinstance(entry, dict):
            warnings.append("loop entry not an object; skipped")
            continue
        loop_id_raw = entry.get("loop_id")
        try:
            loop_id = int(loop_id_raw)
        except Exception:
            warnings.append(f"loop entry missing/invalid loop_id: {loop_id_raw}")
            continue
        invs = _coerce_str_list(entry.get("invariants"))
        dec_raw = entry.get("decreases")
        dec_val = dec_raw if isinstance(dec_raw, str) and dec_raw.strip() else None
        out.append(LoopPatch(loop_id=loop_id, invariants=invs, decreases=dec_val))
    return out


def validate_patch(obj: Any) -> Tuple[Patch, List[str]]:
    warnings: List[str] = []
    if not isinstance(obj, dict):
        warnings.append("patch root is not an object; using defaults")
        return Patch(), warnings
    extra = set(obj.keys()) - ALLOWED_KEYS
    if extra:
        warnings.append(f"unknown keys ignored: {', '.join(sorted(extra))}")

    requires = _coerce_str_list(obj.get("requires"))
    ensures = _coerce_str_list(obj.get("ensures"))
    types = _coerce_types(obj.get("types"))
    rewrites = _coerce_rewrites(obj.get("rewrites"), warnings)
    loops = _coerce_loops(obj.get("loops"), warnings)

    patch = Patch(
        requires=requires,
        ensures=ensures,
        types=types,
        rewrites=rewrites,
        loops=loops,
    )
    return patch, warnings


__all__ = ["Patch", "LoopPatch", "RewritePatch", "validate_patch"]
