from __future__ import annotations
import re
import json
import subprocess
import tempfile
import pathlib
import sys
from dataclasses import dataclass
from typing import List, Dict, Optional

# Assumes layout:
#   <root>/week5/parser.py
#   <root>/week6/linear_invariants.py
ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.append(str(ROOT / "week5"))
sys.path.append(str(ROOT / "week6"))

import parser as week5_parser  # type: ignore
import linear_invariants as week6_lin  # type: ignore


# ======================= Data structures =======================

@dataclass
class LoopMatch:
    kind: str              # "while" or "for"
    cond_text: str         # condition or for-range summary
    start_idx: int         # index of 'while' or 'for'
    header_end_idx: int    # end of the loop header (right after condition / for-range)
    indent: str            # indentation of the loop header line


# ======================= Parsing helpers =======================

IDENT = r"[A-Za-z_][A-Za-z0-9_]*"

WHILE_RE = re.compile(r"(?P<indent>[ \t]*)while\s*\((?P<cond>[^)]*)\)")
FOR_RE = re.compile(
    r"(?P<indent>[ \t]*)for\s+(?P<var>" + IDENT + r")\s*:=\s*(?P<start>[^\s]+)\s*to\s*(?P<end>[^\s{]+)"
)


def strip_comments(src: str) -> str:
    """Strip // and /* ... */ comments."""
    src = re.sub(r"/\*.*?\*/", "", src, flags=re.DOTALL)
    src = re.sub(r"//.*", "", src)
    return src


def find_loop_match_by_condition(src: str, cond: str) -> Optional[LoopMatch]:
    """
    Find first loop whose condition matches cond from Week 5 summary.
    Supports:
      while (cond)
      for i := start to end   encoded as "i in [start, end]".
    """
    code = src

    # while-loops
    for m in WHILE_RE.finditer(code):
        if m.group("cond").strip() == cond.strip():
            return LoopMatch(
                kind="while",
                cond_text=cond.strip(),
                start_idx=m.start(),
                header_end_idx=m.end(),
                indent=m.group("indent"),
            )

    # for-loops
    for m in FOR_RE.finditer(code):
        var = m.group("var").strip()
        start_v = m.group("start").strip()
        end_v = m.group("end").strip()
        cond_text = f"{var} in [{start_v}, {end_v}]"
        if cond_text == cond.strip():
            return LoopMatch(
                kind="for",
                cond_text=cond_text,
                start_idx=m.start(),
                header_end_idx=m.end(),
                indent=m.group("indent"),
            )

    return None


def find_first_loop_fallback(src: str) -> Optional[LoopMatch]:
    """
    Fallback: syntactically grab the first while/for loop if Week 5 summary
    can't be used (or has no loops).
    """
    code = src

    m = WHILE_RE.search(code)
    if m:
        cond = m.group("cond").strip()
        return LoopMatch(
            kind="while",
            cond_text=cond,
            start_idx=m.start(),
            header_end_idx=m.end(),
            indent=m.group("indent"),
        )

    m = FOR_RE.search(code)
    if m:
        var = m.group("var").strip()
        start_v = m.group("start").strip()
        end_v = m.group("end").strip()
        cond_text = f"{var} in [{start_v}, {end_v}]"
        return LoopMatch(
            kind="for",
            cond_text=cond_text,
            start_idx=m.start(),
            header_end_idx=m.end(),
            indent=m.group("indent"),
        )

    return None


# ======================= Invariant loading =======================

def load_invariants(inv_json_path: Optional[str], src: str, method_summary: Dict) -> List[str]:
    """
    Load invariants from JSON if provided, otherwise synthesize using Week 6.
    Accepts shapes:
      { "synthesized_invariants": [...] }
      { "invariants": [...] }
      { "loop": { "synthesized_invariants": [...] } }
    """
    if inv_json_path:
        data = json.loads(pathlib.Path(inv_json_path).read_text(encoding="utf-8"))

        if isinstance(data, dict):
            if "synthesized_invariants" in data:
                return list(data["synthesized_invariants"])
            if "invariants" in data:
                return list(data["invariants"])
            loop = data.get("loop")
            if isinstance(loop, dict) and "synthesized_invariants" in loop:
                return list(loop["synthesized_invariants"])

        return []

    # No JSON provided: synthesize with Week 6
    invs = week6_lin.synthesize_linear_invariants_for_loop(src, method_summary)
    return invs or []


# ======================= Invariant insertion =======================

def insert_invariants_into_loop(src: str, loop: LoopMatch, invariants: List[str]) -> str:
    """
    Insert invariant clauses right after the loop header, before the '{'.

    while (i <= n)
    {
      ...
    }

    becomes:

    while (i <= n)
      invariant ...
      invariant ...
    {
      ...
    }
    """
    if not invariants:
        return src

    insert_pos = loop.header_end_idx

    inv_lines = "".join(
        f"\n{loop.indent}  invariant {inv}" for inv in invariants
    )

    return src[:insert_pos] + inv_lines + src[insert_pos:]


# ======================= Dafny runner =======================

def run_dafny_verify(dafny_path: str, dfy_path: pathlib.Path) -> Dict[str, str]:
    """
    Run Dafny verifier on the given .dfy file.
    Returns:
      {
        "ok": "true"/"false",
        "raw_output": "<full stdout+stderr>"
      }
    Uses a relaxed success check to support both old and new CLI output.
    """
    try:
        completed = subprocess.run(
            [dafny_path, "/compile:0", str(dfy_path)],
            capture_output=True,
            text=True,
            check=False,
        )
    except FileNotFoundError:
        return {
            "ok": "false",
            "raw_output": "Error: Dafny executable not found. Please ensure 'dafny' is on PATH."
        }

    output = (completed.stdout or "") + (completed.stderr or "")

    # Consider it a success if Dafny says it finished and reports 0 errors.
    # This matches both:
    # - "Dafny program verifier finished with X verified, 0 errors"
    # - future similar formats that still contain "0 errors".
    ok = ("Dafny program verifier finished" in output and "0 errors" in output)

    return {
        "ok": "true" if ok else "false",
        "raw_output": output.strip(),
    }


# ======================= Pipeline =======================

def build_and_verify(
    src_path: pathlib.Path,
    inv_json_path: Optional[str],
    out_path: Optional[str],
    run_dafny: bool,
    dafny_exe: str,
) -> Dict:
    """
    Full Week 7 pipeline for a single program:
      1. Parse with Week 5.
      2. Get invariants (JSON or Week 6).
      3. Locate loop (summary-based, then fallback).
      4. Insert invariants (if any).
      5. Optionally run Dafny.
      6. Return a JSON-able summary.
    """
    src = src_path.read_text(encoding="utf-8")
    method_summary = week5_parser.parse_dafny(src)

    # Step 1+2: get invariants
    invariants = load_invariants(inv_json_path, src, method_summary)

    # Step 3: locate loop
    loops = method_summary.get("loops", [])
    loop_match: Optional[LoopMatch] = None

    if loops:
        first = loops[0]
        cond = (first.get("condition") or "").strip()
        if cond:
            loop_match = find_loop_match_by_condition(src, cond)

    if loop_match is None:
        loop_match = find_first_loop_fallback(src)

    # Step 4: insert invariants (if we have a loop + invariants)
    if loop_match is not None and invariants:
        instrumented = insert_invariants_into_loop(src, loop_match, invariants)
    else:
        instrumented = src

    # Write instrumented program if requested
    out_written = ""
    if out_path:
        out_file = pathlib.Path(out_path)
        out_file.write_text(instrumented, encoding="utf-8")
        out_written = str(out_file)

    # Step 5: optionally run Dafny
    verify_result: Dict[str, str] = {"ok": "false", "raw_output": ""}
    if run_dafny:
        if out_path:
            dfy_to_check = pathlib.Path(out_path)
        else:
            tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".dfy")
            tmp.write(instrumented.encode("utf-8"))
            tmp.flush()
            tmp.close()
            dfy_to_check = pathlib.Path(tmp.name)

        verify_result = run_dafny_verify(dafny_exe, dfy_to_check)

    return {
        "method_name": method_summary.get("method_name"),
        "loop_condition": loop_match.cond_text if loop_match else None,
        "inserted_invariants": invariants if (loop_match and invariants) else [],
        "output_path": out_written,
        "verification": verify_result,
    }


# ========================== CLI ===============================

def main():
    import argparse

    ap = argparse.ArgumentParser(
        description="Week 7: Automated Correctness Checking Pipeline"
    )
    ap.add_argument("source", help="Path to a .dfy file")
    ap.add_argument(
        "--inv",
        help="Path to invariants JSON (if omitted, uses Week 6 synthesizer)",
        default=None,
    )
    ap.add_argument(
        "--out",
        help="Path to write instrumented Dafny program",
        default=None,
    )
    ap.add_argument(
        "--run-dafny",
        help="Run Dafny verifier on the instrumented program",
        action="store_true",
    )
    ap.add_argument(
        "--dafny",
        help="Dafny executable name or path",
        default="dafny",
    )

    args = ap.parse_args()

    src_path = pathlib.Path(args.source)
    result = build_and_verify(
        src_path=src_path,
        inv_json_path=args.inv,
        out_path=args.out,
        run_dafny=args.run_dafny,
        dafny_exe=args.dafny,
    )

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
