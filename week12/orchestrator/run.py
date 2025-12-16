from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
from typing import Dict, List, Optional, Tuple

from dotenv import load_dotenv

from ..python_to_dafny import TranslationOptions, translate_python_to_dafny_with_meta
from .apply_patch import apply_patch
from .llm_client import LLMClient
from .patch_schema import validate_patch
from .verify import run_dafny

load_dotenv()

PROMPT_DIR = pathlib.Path(__file__).resolve().parent / "prompts"


def load_prompt(name: str) -> str:
    return (PROMPT_DIR / name).read_text(encoding="utf-8")


def write_text(path: pathlib.Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def _extract_error_context(dafny_src: str, verifier_output: str, context: int = 8) -> str:
    lines = dafny_src.splitlines()
    contexts: List[str] = []
    for m in re.finditer(r"\((\d+),\d+\):\s*Error", verifier_output):
        line_no = int(m.group(1))
        start = max(1, line_no - context)
        end = min(len(lines), line_no + context)
        snippet = [f"{i}:{lines[i-1]}" for i in range(start, end + 1)]
        contexts.append("\n".join(snippet))
    return "\n\n".join(contexts)


def orchestrate(
    python_path: pathlib.Path,
    out_dir: pathlib.Path,
    max_iters: int = 3,
    dafny_cmd: str = "dafny",
    self_check: bool = False,
    llm_backend: str = "openai",
    llm_model: Optional[str] = None,
) -> Tuple[pathlib.Path, bool]:
    python_src = python_path.read_text(encoding="utf-8")

    options = TranslationOptions(module_name=python_path.stem)
    draft_dafny, meta = translate_python_to_dafny_with_meta(python_src, options)
    metadata_json = json.dumps(meta, indent=2)

    out_dir.mkdir(parents=True, exist_ok=True)
    draft_path = out_dir / "draft.dfy"
    meta_path = out_dir / "meta.json"
    write_text(draft_path, draft_dafny)
    write_text(meta_path, metadata_json)

    if self_check:
        write_text(out_dir / "draft.selfcheck.log", "PASS")
        return draft_path, True

    llm = LLMClient(backend=llm_backend, model=llm_model)
    if not llm.enabled:
        hint = "set OPENAI_API_KEY" if llm_backend == "openai" else "set OPENROUTER_API_KEY"
        print(
            f"LLM unavailable (backend={llm_backend}); {hint} to enable. "
            f"Wrote draft to {draft_path} and metadata to {meta_path}"
        )
        return draft_path, False

    initial_prompt_tmpl = load_prompt("initial_patch.txt")
    repair_prompt_tmpl = load_prompt("repair_patch.txt")

    current_code = draft_dafny
    verifier_result = None
    latest_candidate: Optional[pathlib.Path] = None
    verified = False

    for attempt in range(max_iters):
        if attempt == 0:
            prompt = initial_prompt_tmpl.format(
                python_src=python_src,
                dafny_src=current_code,
                metadata_json=metadata_json,
            )
        else:
            verifier_output = verifier_result["output"] if verifier_result else ""
            context = _extract_error_context(current_code, verifier_output)
            prompt = repair_prompt_tmpl.format(
                dafny_src=current_code,
                verifier_output=verifier_output,
                metadata_json=metadata_json,
                error_context=context,
            )

        patch_json, llm_meta = llm.complete_json(prompt)
        patch_raw = patch_json or {}
        patch, validation_warnings = validate_patch(patch_raw)

        patch_path = out_dir / f"patch{attempt}.json"
        write_text(patch_path, json.dumps(patch_raw, indent=2))

        candidate_code, apply_warnings, apply_errors = apply_patch(current_code, patch)
        candidate_path = out_dir / f"candidate{attempt}.dfy"
        write_text(candidate_path, candidate_code)

        warnings_all: List[str] = []
        errors_all: List[str] = []
        if llm_meta.get("error"):
            warnings_all.append(str(llm_meta["error"]))
        warnings_all.extend(validation_warnings)
        warnings_all.extend(apply_warnings)
        errors_all.extend(apply_errors)

        if warnings_all:
            write_text(out_dir / f"candidate{attempt}.warnings.txt", "\n".join(warnings_all))
        if errors_all:
            write_text(out_dir / f"patch{attempt}.invalid.txt", "\n".join(errors_all))
            print(f"Patch {attempt} failed validation; aborting.")
            latest_candidate = candidate_path
            break

        verifier_result = run_dafny(str(candidate_path), dafny_cmd=dafny_cmd)
        log_path = out_dir / f"candidate{attempt}.verify.log"
        write_text(log_path, verifier_result.get("output", ""))

        latest_candidate = candidate_path
        if verifier_result.get("ok"):
            print(f"Verification succeeded at attempt {attempt}. Output: {candidate_path}")
            verified = True
            break

        current_code = candidate_code

    if not verified:
        print("Verification did not succeed within the iteration limit.")
        if verifier_result:
            print(f"Last return code: {verifier_result.get('returncode')}")

    return latest_candidate or draft_path, verified


def main() -> None:
    ap = argparse.ArgumentParser(
        description="LLM-aided Python→Dafny conversion."
    )
    ap.add_argument("python_file", help="Path to Python source file.")
    ap.add_argument(
        "--out-dir",
        default="orchestrator_out",
        help="Directory to write artifacts (default: orchestrator_out).",
    )
    ap.add_argument(
        "--max-iters",
        type=int,
        default=3,
        help="Maximum iterations (initial patch + repairs). Default: 3.",
    )
    ap.add_argument(
        "--dafny",
        default="dafny",
        help="Dafny executable/command (default: dafny).",
    )
    ap.add_argument(
        "--llm-backend",
        choices=["openai", "openrouter"],
        default="openai",
        help="LLM backend to use (default: openai).",
    )
    ap.add_argument(
        "--llm-model",
        help="Override model name for the selected backend.",
    )
    ap.add_argument(
        "--self-check",
        action="store_true",
        help="Generate draft/meta and stop (no LLM).",
    )

    args = ap.parse_args()

    orchestrate(
        python_path=pathlib.Path(args.python_file),
        out_dir=pathlib.Path(args.out_dir),
        max_iters=args.max_iters,
        dafny_cmd=args.dafny,
        self_check=args.self_check,
        llm_backend=args.llm_backend,
        llm_model=args.llm_model,
    )


if __name__ == "__main__":
    main()
