"""Model runner registry.

This file is the one place that maps user-facing runner strings to concrete
backend classes. ``generate_blueprint.py`` calls ``get_runner("openai:gpt-5")``
or ``get_runner("codex")`` and receives an object with a common ``run`` method.

Keep backend names stable because they are part of the CLI surface:
``codex``, ``claude-code``, ``openai``, ``anthropic``, and ``mock``.
"""
from __future__ import annotations

from pathlib import Path

from .api import AnthropicRunner, OpenAIRunner
from .base import ModelRunner, RunnerError, RunResult, load_context_file
from .cli import ClaudeCodeRunner, CodexRunner
from .mock import MockRunner

BACKENDS: dict[str, type[ModelRunner]] = {
    "anthropic": AnthropicRunner,
    "claude-code": ClaudeCodeRunner,
    "codex": CodexRunner,
    "mock": MockRunner,
    "openai": OpenAIRunner,
}


def get_runner(
    spec: str,
    *,
    context_files: list[str | Path] | None = None,
    timeout: int = 3600,
    **kwargs,
) -> ModelRunner:
    """Instantiate a runner from ``backend[:model]``."""
    backend, _, model = spec.partition(":")
    backend = backend.strip()
    cls = BACKENDS.get(backend)
    if cls is None:
        choices = ", ".join(sorted(BACKENDS))
        raise RunnerError(f"unknown runner {backend!r}; choose one of: {choices}")
    return cls(model.strip() or None, context_files=context_files, timeout=timeout, **kwargs)


__all__ = [
    "AnthropicRunner",
    "BACKENDS",
    "ClaudeCodeRunner",
    "CodexRunner",
    "MockRunner",
    "ModelRunner",
    "OpenAIRunner",
    "RunResult",
    "RunnerError",
    "get_runner",
    "load_context_file",
]
