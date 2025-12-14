from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
import tempfile
from typing import Dict, List, Optional, Tuple

ROOT = pathlib.Path(__file__).resolve().parent.parent

# Make week modules importable
sys.path.append(str(ROOT / "week5"))
sys.path.append(str(ROOT / "week6"))
sys.path.append(str(ROOT / "week9"))
sys.path.append(str(ROOT / "week10"))
sys.path.append(str(ROOT / "week11"))
sys.path.append(str(ROOT / "week12"))

# Optional imports
try:
    import parser as week5_parser  # type: ignore
except ImportError:
    week5_parser = None

try:
    import linear_invariants as linv_linear  # type: ignore
except ImportError:
    linv_linear = None

try:
    import bool_linear_invariants as linv_bool  # type: ignore
except ImportError:
    linv_bool = None

try:
    import disjunctive_invariants as dinv  # type: ignore
except ImportError:
    dinv = None

try:
    import quadratic_invariants as qinv  # type: ignore
except ImportError:
    qinv = None

try:
    import array_list_invariants as arrinv  # type: ignore
except ImportError:
    arrinv = None


# -------------------------- loop handling --------------------------

WHILE_RE = re.compile(
    r"while\s*"
    r"(?:\((?P<cond_paren>[^)]*)\)|(?P<cond_noparen>[^{]*?))"
    r"\s*(?P<brace>\{)",
    re.DOTALL,
)


def find_first_while(src: str) -> Optional[re.Match]:
    return WHILE_RE.search(src)


def insert_invariants(src: str, invariants: List[str]) -> str:
    """Insert invariants before the first loop body brace."""
    clean: List[str] = []
    seen = set()
    for inv in invariants:
        inv = (inv or "").strip()
        if not inv:
            continue
        if inv in seen:
            continue
        seen.add(inv)
        if "||" in inv and not (inv.startswith("(") and inv.endswith(")")):
            inv = f"({inv})"
        clean.append(inv)

    if not clean:
        return src

    m = find_first_while(src)
    if not m:
        return src

    brace_pos = m.start("brace")
    line_start = src.rfind("\n", 0, m.start())
    if line_start == -1:
        line_start = 0
    else:
        line_start += 1
    while_indent = src[line_start:m.start()]
    inv_indent = while_indent + "  "

    block = "".join(f"\n{inv_indent}invariant {inv}" for inv in clean)
    return src[:brace_pos] + block + src[brace_pos:]


# --------------------------- helpers -------------------------------

def adapt_method_summary(raw: Dict) -> Dict:
    """Try available adaptors; otherwise return raw dict."""
    for mod in (linv_bool, dinv, arrinv):
        if mod and hasattr(mod, "adapt_method_summary"):
            try:
                return mod.adapt_method_summary(raw)  # type: ignore[attr-defined]
            except Exception:
                continue
    return raw or {}


def load_method_summary(src_path: pathlib.Path, summary_path: Optional[pathlib.Path]) -> Dict:
    if summary_path is not None:
        try:
            return adapt_method_summary(json.loads(summary_path.read_text(encoding="utf-8")))
        except Exception:
            return {}
    if week5_parser is not None:
        try:
            raw = week5_parser.run_parser(str(src_path))  # type: ignore[attr-defined]
            return adapt_method_summary(raw)
        except Exception:
            return {}
    return {}


# -------------------- synthesizer dispatch -------------------------

def synthesize_linear(src: str, method_summary: Dict) -> Tuple[List[str], Dict]:
    if linv_linear is None:
        return [], {"error": "linear invariants unavailable"}
    try:
        invs = linv_linear.synthesize_linear_invariants_for_loop(src, method_summary)  # type: ignore
        return invs or [], {"engine": "linear"}
    except Exception as e:
        return [], {"error": f"linear synthesis failed: {e}"}


def synthesize_boolean(src: str, method_summary: Dict) -> Tuple[List[str], Dict]:
    if linv_bool is None:
        return [], {"error": "boolean invariants unavailable"}
    try:
        invs = linv_bool.synthesize_boolean_dnf_invariant_for_loop(src, method_summary)  # type: ignore
        return invs or [], {"engine": "boolean"}
    except Exception as e:
        return [], {"error": f"boolean synthesis failed: {e}"}


def synthesize_disjunctive(src: str, method_summary: Dict) -> Tuple[List[str], Dict]:
    if dinv is None:
        return [], {"error": "disjunctive invariants unavailable"}
    try:
        res = dinv.synthesize_disjunctive_invariants_for_method(  # type: ignore[attr-defined]
            src,
            method_summary,
            use_boolean=False,  # equivalent to passing --no-bool
        )
        loops = res.get("loops", []) or []
        invs: List[str] = []
        if loops:
            for entry in loops[0].get("disjunctive_invariants", []):
                dnf = entry.get("dnf")
                if isinstance(dnf, str) and dnf.strip():
                    invs.append(dnf.strip())
        return invs, {"engine": "disjunctive", "raw": res}
    except Exception as e:
        return [], {"error": f"disjunctive synthesis failed: {e}"}


def synthesize_quadratic(src_path: pathlib.Path) -> Tuple[List[str], Dict]:
    if qinv is None:
        return [], {"error": "quadratic invariants unavailable"}
    try:
        res = qinv.synthesize_quadratic_invariants_for_file(src_path, summary_json=None)  # type: ignore[attr-defined]
        methods = res.get("methods") or []
        invs: List[str] = []
        if methods:
            loops = methods[0].get("loops") or []
            if loops:
                invs = [
                    s.strip()
                    for s in loops[0].get("quadratic_invariants", [])
                    if isinstance(s, str) and s.strip()
                ]
        return invs, {"engine": "quadratic", "raw": res}
    except Exception as e:
        return [], {"error": f"quadratic synthesis failed: {e}"}


def synthesize_arrays(src_path: pathlib.Path) -> Tuple[List[str], Dict]:
    if arrinv is None:
        return [], {"error": "array/list invariants unavailable"}
    try:
        res = arrinv.synthesize_invariants_for_file(src_path, summary_json=None)  # type: ignore[attr-defined]
        loops = res.get("loops") or []
        invs: List[str] = []
        if loops:
            invs = [
                s.strip()
                for s in loops[0].get("invariants", [])
                if isinstance(s, str) and s.strip()
            ]
        return invs, {"engine": "arrays", "raw": res}
    except Exception as e:
        return [], {"error": f"arrays synthesis failed: {e}"}


def synthesize_invariants(mode: str, src: str, src_path: pathlib.Path, method_summary: Dict) -> Tuple[List[str], Dict]:
    mode = mode.lower()
    if mode == "linear":
        return synthesize_linear(src, method_summary)
    if mode == "boolean":
        return synthesize_boolean(src, method_summary)
    if mode == "disjunctive":
        return synthesize_disjunctive(src, method_summary)
    if mode == "quadratic":
        return synthesize_quadratic(src_path)
    if mode == "arrays":
        return synthesize_arrays(src_path)
    return [], {"error": f"unknown mode: {mode}"}


def normalize_len_notation(invariants: List[str]) -> List[str]:
    """Convert len(x) to x.Length for Dafny syntax."""
    out: List[str] = []
    pattern = re.compile(r"\blen\(\s*([A-Za-z_][A-Za-z0-9_]*)\s*\)")
    for inv in invariants:
        out.append(pattern.sub(r"\1.Length", inv))
    return out


# --------------------------- dafny --------------------------------

def run_dafny(dafny_cmd: str, target: pathlib.Path) -> Dict[str, object]:
    cmd = [dafny_cmd, str(target)]
    try:
        res = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        return {"command": cmd, "returncode": res.returncode, "output": res.stdout}
    except FileNotFoundError:
        return {"command": cmd, "returncode": 1, "output": f"Dafny not found: {dafny_cmd}"}


# ----------------------------- CLI --------------------------------

def main():
    ap = argparse.ArgumentParser(
        description="Final auto-verify: choose a mode (linear / boolean / disjunctive / quadratic / arrays), synthesize invariants, inject, optionally run Dafny."
    )
    ap.add_argument("file", help="Input Dafny (.dfy) file")
    ap.add_argument(
        "--mode",
        required=True,
        choices=["linear", "boolean", "disjunctive", "quadratic", "arrays"],
        help="Invariant strategy to use.",
    )
    ap.add_argument(
        "--summary",
        help="Optional Week 5 JSON summary (used for linear/boolean/disjunctive modes).",
    )
    ap.add_argument(
        "--out",
        help="Write instrumented Dafny to this path. If omitted, a temp file is used for Dafny verification.",
    )
    ap.add_argument(
        "--run-dafny",
        action="store_true",
        help="Run Dafny verifier on the instrumented program.",
    )
    ap.add_argument(
        "--dafny",
        default="dafny",
        help="Dafny executable/command to use with --run-dafny.",
    )

    args = ap.parse_args()

    src_path = pathlib.Path(args.file)
    src = src_path.read_text(encoding="utf-8")
    summary_path = pathlib.Path(args.summary) if args.summary else None
    method_summary = load_method_summary(src_path, summary_path)

    invariants, detail = synthesize_invariants(args.mode, src, src_path, method_summary)
    dafny_invariants = normalize_len_notation(invariants)

    instrumented = insert_invariants(src, dafny_invariants) if dafny_invariants else src

    out_written: Optional[pathlib.Path] = None
    if args.out:
        out_written = pathlib.Path(args.out)
        out_written.write_text(instrumented, encoding="utf-8")

    dafny_result: Optional[Dict[str, object]] = None
    if args.run_dafny:
        target = out_written
        if target is None:
            tmp = tempfile.NamedTemporaryFile(delete=False, suffix=".dfy")
            tmp.write(instrumented.encode("utf-8"))
            tmp.flush()
            tmp.close()
            target = pathlib.Path(tmp.name)
        dafny_result = run_dafny(args.dafny, target)

    method_name = (
        method_summary.get("method_name")
        or detail.get("raw", {}).get("method_name")
        or src_path.stem
    )

    result = {
        "file": str(src_path),
        "mode": args.mode,
        "method_name": method_name,
        "invariants": dafny_invariants,
        "output_path": str(out_written) if out_written else None,
        "dafny": dafny_result,
        "detail": detail,
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
