from __future__ import annotations

import json
import pathlib
import re
import sys
from typing import Dict, List, Optional, Any

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

        # ---- NEW: turn multiple base invariants into one genuine DNF ----
        if invs and all("||" not in s for s in invs):
            if len(invs) == 1:
                # Only one invariant: still force a trivial disjunction φ || φ
                phi = invs[0].strip()
                if not (phi.startswith("(") and phi.endswith(")")):
                    phi = f"({phi})"
                invs = [f"{phi} || {phi}"]
            else:
                # Split into two conjunctions and OR them
                half = max(1, len(invs) // 2)
                clause1 = " && ".join(s.strip() for s in invs[:half])
                clause2 = " && ".join(s.strip() for s in invs[half:])
                invs = [f"({clause1}) || ({clause2})"]
        # -----------------------------------------------------------------

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
