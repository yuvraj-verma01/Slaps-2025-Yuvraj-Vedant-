from __future__ import annotations

import subprocess
from typing import Dict, List


def run_dafny(file_path: str, dafny_cmd: str = "dafny") -> Dict[str, object]:
    cmd: List[str] = [dafny_cmd, file_path]
    try:
        res = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            check=False,
        )
        output = (res.stdout or "") + (res.stderr or "")
        return {
            "ok": res.returncode == 0,
            "returncode": res.returncode,
            "output": output,
            "command": cmd,
        }
    except FileNotFoundError:
        return {"ok": False, "returncode": 127, "output": "Dafny executable not found", "command": cmd}
    except Exception as exc:  # pragma: no cover
        return {"ok": False, "returncode": 1, "output": str(exc), "command": cmd}


__all__ = ["run_dafny"]
