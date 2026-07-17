"""Shared runner contract used by every model backend.

The rest of Auto-Blueprint should not care whether a model is reached through a
local CLI, an HTTP API, or a test double. Each backend subclasses
``ModelRunner`` and implements ``_run_impl(prompt, system, cwd)``. The base
class handles context-file loading, retry/backoff, timing metadata, and a common
``RunResult`` shape.

Two runner modes matter:

* ``mode = "agent"``: the runner may edit files in the repo.
* ``mode = "api"``: the runner only returns text; Python code writes files.

Constructing any runner with ``readonly=True`` means the caller is asking for a
read-only generation pass. API backends satisfy this by construction. Local
agent backends apply the strongest restriction their CLI exposes; some CLIs can
still execute read-only shell commands inside a sandbox, so callers must still
use external timeouts and audits.
"""
from __future__ import annotations

import abc
import time
from dataclasses import dataclass
from pathlib import Path


class RunnerError(RuntimeError):
    """Backend failure: auth, CLI missing, network, timeout, or malformed reply."""


@dataclass
class RunResult:
    text: str
    backend: str = ""
    model: str = ""
    mode: str = ""
    duration_s: float = 0.0
    raw: object = None


def load_context_file(path: str | Path) -> str:
    """Read a context file, or a directory containing ``SKILL.md``."""
    p = Path(path).expanduser()
    if p.is_dir():
        p = p / "SKILL.md"
    if not p.is_file():
        raise RunnerError(f"context file not found: {p}")
    return p.read_text(encoding="utf-8")


class ModelRunner(abc.ABC):
    backend_name = "base"
    mode = "base"  # "agent" or "api"
    can_edit_files = False

    def __init__(
        self,
        model: str | None = None,
        *,
        context_files: list[str | Path] | None = None,
        timeout: int = 3600,
        readonly: bool = False,
    ):
        self.model = model or self.default_model()
        self.timeout = timeout
        self.readonly = readonly
        self.contexts = [load_context_file(p) for p in (context_files or [])]

    @classmethod
    def default_model(cls) -> str:
        return ""

    def build_system(self, extra_system: str | None = None) -> str:
        parts: list[str] = []
        for i, context in enumerate(self.contexts, start=1):
            parts.append(f"<context index=\"{i}\">\n{context}\n</context>")
        if extra_system:
            parts.append(extra_system)
        return "\n\n".join(parts)

    def run(
        self,
        prompt: str,
        *,
        system: str | None = None,
        cwd: str | Path | None = None,
        retries: int = 2,
    ) -> RunResult:
        full_system = self.build_system(system)
        cwd_path = Path(cwd) if cwd else None
        last_exc: Exception | None = None
        for attempt in range(retries + 1):
            start = time.time()
            try:
                result = self._run_impl(prompt, full_system, cwd_path)
                result.backend = self.backend_name
                result.model = result.model or self.model
                result.mode = self.mode
                result.duration_s = time.time() - start
                return result
            except RunnerError as exc:
                last_exc = exc
                if attempt < retries:
                    wait = 5 * (2**attempt)
                    print(f"  ! {self.backend_name} failed ({exc}); retrying in {wait}s")
                    time.sleep(wait)
        raise RunnerError(f"{self.backend_name} failed after {retries + 1} attempts: {last_exc}")

    @abc.abstractmethod
    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        ...
