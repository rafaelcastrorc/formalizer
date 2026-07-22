"""HTTP API model runners for production-safe generation.

These backends call external model APIs directly using only the Python standard
library. They never edit files and never run shell commands. Instead, they
return text to ``generate_blueprint.py``; in API mode that text is expected to be
a JSON object containing metadata and ``content_tex``. The generator then
scaffolds files, validates the blueprint, and runs the build.

Credentials come from environment variables:

* ``OPENAI_API_KEY`` for ``OpenAIRunner``.
* ``ANTHROPIC_API_KEY`` for ``AnthropicRunner``.
"""
from __future__ import annotations

import json
import os
import urllib.error
import urllib.request
from pathlib import Path
from typing import Any

from .base import ModelRunner, RunnerError, RunResult

ANTHROPIC_API_URL = "https://api.anthropic.com/v1/messages"
ANTHROPIC_MODELS_URL = "https://api.anthropic.com/v1/models"
ANTHROPIC_API_VERSION = "2023-06-01"
OPENAI_MODELS_URL = "https://api.openai.com/v1/models"
OPENAI_RESPONSES_URL = "https://api.openai.com/v1/responses"
NON_TEXT_MODEL_MARKERS = (
    "audio",
    "dall",
    "embed",
    "image",
    "moderation",
    "realtime",
    "search",
    "speech",
    "tts",
    "transcribe",
    "vision",
    "whisper",
)


def is_text_model(model_id: str) -> bool:
    low = model_id.lower()
    return not any(marker in low for marker in NON_TEXT_MODEL_MARKERS)


def choose_model(models: list[str], *, prefer: tuple[str, ...], avoid: tuple[str, ...] = ()) -> str:
    """Pick a model from a live provider list using model-class keywords.

    The provider model-list endpoints tell us what the API key can use, but not
    price. This function deliberately avoids fixed model IDs and only uses broad
    family markers such as ``mini``/``haiku`` for the cheap tier and
    ``gpt``/``sonnet``/``opus`` for escalation.
    """
    for model in models:
        low = model.lower()
        if not is_text_model(model):
            continue
        if any(token in low for token in prefer) and not any(token in low for token in avoid):
            return model
    for model in models:
        low = model.lower()
        if is_text_model(model) and not any(token in low for token in avoid):
            return model
    return ""


def _get_json(url: str, headers: dict[str, str], timeout: int) -> dict:
    req = urllib.request.Request(url, headers=headers, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")[:3000]
        raise RunnerError(f"HTTP {exc.code}: {detail}") from exc
    except (urllib.error.URLError, TimeoutError) as exc:
        raise RunnerError(f"network error: {exc}") from exc


def _post_json(url: str, body: dict[str, Any], headers: dict[str, str], timeout: int) -> dict:
    req = urllib.request.Request(
        url,
        data=json.dumps(body).encode("utf-8"),
        headers=headers | {"Content-Type": "application/json"},
        method="POST",
    )
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))
    except urllib.error.HTTPError as exc:
        detail = exc.read().decode("utf-8", "replace")[:3000]
        raise RunnerError(f"HTTP {exc.code}: {detail}") from exc
    except (urllib.error.URLError, TimeoutError) as exc:
        raise RunnerError(f"network error: {exc}") from exc


def list_openai_model_ids(*, timeout: int = 5) -> list[str]:
    """Return model IDs available to the configured OpenAI API key."""
    key = os.environ.get("OPENAI_API_KEY")
    if not key:
        return []
    payload = _get_json(
        OPENAI_MODELS_URL,
        {"Authorization": f"Bearer {key}"},
        timeout,
    )
    ids = [
        item.get("id")
        for item in payload.get("data", [])
        if isinstance(item, dict) and isinstance(item.get("id"), str)
    ]
    return [model_id for model_id in ids if model_id]


def list_anthropic_model_ids(*, timeout: int = 5) -> list[str]:
    """Return model IDs available to the configured Anthropic API key."""
    key = os.environ.get("ANTHROPIC_API_KEY")
    if not key:
        return []
    payload = _get_json(
        ANTHROPIC_MODELS_URL,
        {"x-api-key": key, "anthropic-version": ANTHROPIC_API_VERSION},
        timeout,
    )
    ids = [
        item.get("id")
        for item in payload.get("data", [])
        if isinstance(item, dict) and isinstance(item.get("id"), str)
    ]
    return [model_id for model_id in ids if model_id]


def _openai_text(payload: dict) -> str:
    chunks: list[str] = []
    for item in payload.get("output", []):
        for content in item.get("content", []):
            if content.get("type") in {"output_text", "text"}:
                chunks.append(content.get("text", ""))
    if chunks:
        return "".join(chunks)
    text = payload.get("output_text")
    return text if isinstance(text, str) else ""


def _raise_if_openai_incomplete(payload: dict) -> None:
    status = payload.get("status")
    if status and status != "completed":
        detail = payload.get("incomplete_details") or payload.get("error") or {}
        raise RunnerError(f"OpenAI response status {status}: {str(detail)[:1000]}")
    details = payload.get("incomplete_details")
    if details:
        raise RunnerError(f"OpenAI response incomplete: {str(details)[:1000]}")


def _raise_if_anthropic_truncated(payload: dict) -> None:
    if payload.get("stop_reason") == "max_tokens":
        raise RunnerError("Anthropic response stopped at max_tokens; output was truncated")


class OpenAIRunner(ModelRunner):
    backend_name = "openai"
    mode = "api"

    def __init__(
        self,
        model: str | None = None,
        *,
        max_output_tokens: int | None = None,
        **kwargs,
    ):
        super().__init__(model, **kwargs)
        self.max_output_tokens = max_output_tokens

    @classmethod
    def default_model(cls) -> str:
        return "gpt-5"

    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        key = os.environ.get("OPENAI_API_KEY")
        if not key:
            raise RunnerError("OPENAI_API_KEY is not set")
        body: dict[str, Any] = {
            "model": self.model,
            "input": [
                *([{"role": "system", "content": system}] if system else []),
                {"role": "user", "content": prompt},
            ],
        }
        if self.max_output_tokens:
            body["max_output_tokens"] = self.max_output_tokens
        payload = _post_json(
            OPENAI_RESPONSES_URL,
            body,
            {"Authorization": f"Bearer {key}"},
            self.timeout,
        )
        _raise_if_openai_incomplete(payload)
        text = _openai_text(payload)
        if not text:
            raise RunnerError(f"OpenAI returned no text: {str(payload)[:1000]}")
        return RunResult(text=text, raw=payload)


class AnthropicRunner(ModelRunner):
    backend_name = "anthropic"
    mode = "api"

    def __init__(self, model: str | None = None, *, max_tokens: int = 8192, **kwargs):
        super().__init__(model, **kwargs)
        self.max_tokens = max_tokens

    @classmethod
    def default_model(cls) -> str:
        return "claude-sonnet-4-5"

    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        key = os.environ.get("ANTHROPIC_API_KEY")
        if not key:
            raise RunnerError("ANTHROPIC_API_KEY is not set")
        body: dict[str, Any] = {
            "model": self.model,
            "max_tokens": self.max_tokens,
            "messages": [{"role": "user", "content": prompt}],
        }
        if system:
            body["system"] = system
        payload = _post_json(
            ANTHROPIC_API_URL,
            body,
            {"x-api-key": key, "anthropic-version": ANTHROPIC_API_VERSION},
            self.timeout,
        )
        _raise_if_anthropic_truncated(payload)
        text = "".join(
            part.get("text", "")
            for part in payload.get("content", [])
            if part.get("type") == "text"
        )
        if not text:
            raise RunnerError(f"Anthropic returned no text: {str(payload)[:1000]}")
        return RunResult(text=text, raw=payload)
