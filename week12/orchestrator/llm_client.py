from __future__ import annotations

import hashlib
import json
import os
import pathlib
from typing import Dict, Optional, Tuple

import requests

try:
    import openai  # type: ignore
except ImportError:  # pragma: no cover
    openai = None  # type: ignore


CACHE_DIR = pathlib.Path(__file__).resolve().parent / "cache"


class LLMClient:
    """
    JSON-only client with disk caching. Supports openai and openrouter.
    """

    def __init__(self, backend: str = "openai", model: Optional[str] = None) -> None:
        self.backend = backend
        self.model = model or os.environ.get("OPENAI_MODEL", "gpt-4.1-mini")
        self.enabled = False
        self._client = None
        self._api_key = None

        if backend == "openai":
            self._api_key = os.environ.get("OPENAI_API_KEY")
            if self._api_key and openai is not None:
                try:
                    if hasattr(openai, "OpenAI"):
                        self._client = openai.OpenAI(api_key=self._api_key)  # type: ignore[attr-defined]
                    else:
                        openai.api_key = self._api_key  # type: ignore
                        self._client = openai
                    self.enabled = True
                except Exception:
                    self.enabled = False
        elif backend == "openrouter":
            self._api_key = os.environ.get("OPENROUTER_API_KEY")
            self.enabled = bool(self._api_key)
        else:
            self.enabled = False

    def _hash_prompt(self, prompt: str) -> str:
        payload = f"backend:{self.backend}\nmodel:{self.model}\n{prompt}"
        return hashlib.sha256(payload.encode("utf-8")).hexdigest()

    def _cache_path(self, prompt: str) -> pathlib.Path:
        return CACHE_DIR / f"{self._hash_prompt(prompt)}.json"

    def _call_openai(self, prompt: str) -> Tuple[Optional[str], Optional[str]]:
        if not self._client:
            return None, "LLM unavailable (missing OPENAI_API_KEY or openai package)"
        try:
            if hasattr(self._client, "chat") and hasattr(self._client.chat, "completions"):
                resp = self._client.chat.completions.create(  # type: ignore
                    model=self.model,
                    messages=[{"role": "user", "content": prompt}],
                    response_format={"type": "json_object"},
                )
                content = resp.choices[0].message.content  # type: ignore[index]
            else:
                resp = self._client.ChatCompletion.create(  # type: ignore
                    model=self.model,
                    messages=[{"role": "user", "content": prompt}],
                    temperature=0,
                )
                content = resp["choices"][0]["message"]["content"]
            return content, None
        except Exception as exc:
            return None, f"LLM call failed: {exc}"

    def _call_openrouter(self, prompt: str) -> Tuple[Optional[str], Optional[str]]:
        if not self._api_key:
            return None, "LLM unavailable (missing OPENROUTER_API_KEY)"
        url = "https://openrouter.ai/api/v1/chat/completions"
        headers = {
            "Authorization": f"Bearer {self._api_key}",
            "Content-Type": "application/json",
            "HTTP-Referer": "https://example.com",
            "X-Title": "Slaps-Orchestrator",
        }
        payload = {
            "model": self.model,
            "messages": [{"role": "user", "content": prompt}],
            "temperature": 0,
        }
        try:
            resp = requests.post(url, headers=headers, json=payload, timeout=60)
            resp.raise_for_status()
            data = resp.json()
            choices = data.get("choices") or []
            if not choices:
                return None, "empty response choices"
            content = choices[0].get("message", {}).get("content")
            return content, None
        except Exception as exc:
            return None, f"LLM call failed: {exc}"

    def _call_backend(self, prompt: str) -> Tuple[Optional[str], Optional[str]]:
        if self.backend == "openai":
            return self._call_openai(prompt)
        if self.backend == "openrouter":
            return self._call_openrouter(prompt)
        return None, f"unknown backend {self.backend}"

    def complete_json(self, prompt: str) -> Tuple[Optional[Dict], Dict[str, object]]:
        meta: Dict[str, object] = {
            "from_cache": False,
            "cache_path": str(self._cache_path(prompt)),
            "backend": self.backend,
            "model": self.model,
        }

        cache_path = self._cache_path(prompt)
        if cache_path.exists():
            try:
                cached = json.loads(cache_path.read_text(encoding="utf-8"))
                response_text = cached.get("response", "")
                parsed = json.loads(response_text)
                meta["from_cache"] = True
                meta["raw_response"] = response_text
                return parsed, meta
            except Exception as exc:
                meta["error"] = f"cache read/parse failed: {exc}"

        if not self.enabled:
            meta["error"] = f"LLM unavailable for backend {self.backend}"
            return None, meta

        content, err = self._call_backend(prompt)
        if err:
            meta["error"] = err
            return None, meta

        meta["raw_response"] = content
        if content is None:
            meta["error"] = "empty LLM response"
            return None, meta

        try:
            parsed = json.loads(content)
        except Exception as exc:
            meta["error"] = f"response was not valid JSON: {exc}"
            parsed = None

        try:
            CACHE_DIR.mkdir(parents=True, exist_ok=True)
            cache_payload = {
                "prompt": prompt,
                "response": content,
                "model": self.model,
                "backend": self.backend,
            }
            cache_path.write_text(json.dumps(cache_payload, indent=2), encoding="utf-8")
        except Exception:
            pass

        return parsed, meta


__all__ = ["LLMClient"]
