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


# Server-side/transient failure signatures: retried automatically even when the
# caller asked for retries=0, because refinement runs are autonomous and must
# not die to a blip. Quota/spend/session limits are deliberately NOT here —
# those cannot be fixed by waiting a minute.
TRANSIENT_ERROR_MARKERS = (
    "529",
    "overloaded",
    "connection closed",
    "connection error",
    "connection reset",
    "network error",
    "internal server error",
    "502",
    "503",
    "504",
)

NON_RETRYABLE_MARKERS = (
    "session limit",
    "spend limit",
    "usage limit",
    "credit balance",
    "invalid api key",
    "not found on path",
)


def is_transient_error(exc: Exception) -> bool:
    text = str(exc).lower()
    if any(marker in text for marker in NON_RETRYABLE_MARKERS):
        return False
    return any(marker in text for marker in TRANSIENT_ERROR_MARKERS)


def is_environment_error(exc: Exception) -> bool:
    """True for failures no amount of refinement can fix (quota, auth, CLI)."""
    text = str(exc).lower()
    return any(marker in text for marker in NON_RETRYABLE_MARKERS)


@dataclass
class RunResult:
    text: str
    backend: str = ""
    model: str = ""
    mode: str = ""
    duration_s: float = 0.0
    raw: object = None
    # Backend conversation handle for follow-up calls (claude-code / codex
    # sessions). None when the backend has no session concept or the id could
    # not be determined; callers must treat session reuse as best-effort.
    session_id: str | None = None


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
        resume_session_id: str | None = None,
    ):
        self.model = model or self.default_model()
        self.timeout = timeout
        self.readonly = readonly
        # Best-effort: backends that support conversation resume (claude-code,
        # codex) continue this session; all other backends ignore it.
        self.resume_session_id = resume_session_id
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
        attempt = 0
        transient_budget = 3  # extra retries for server-side blips, even at retries=0
        while True:
            # monotonic: wall-clock (time.time) counts machine sleep, which made
            # reported durations disagree with the run log's monotonic stamps.
            start = time.monotonic()
            try:
                result = self._run_impl(prompt, full_system, cwd_path)
                result.backend = self.backend_name
                result.model = result.model or self.model
                result.mode = self.mode
                result.duration_s = time.monotonic() - start
                return result
            except RunnerError as exc:
                last_exc = exc
                if attempt < retries:
                    attempt += 1
                    wait = 5 * (2 ** (attempt - 1))
                    print(f"  ! {self.backend_name} failed ({exc}); retrying in {wait}s")
                    time.sleep(wait)
                    continue
                if transient_budget > 0 and is_transient_error(exc):
                    transient_budget -= 1
                    wait = 30 * (4 - transient_budget)
                    print(
                        f"  ! {self.backend_name} transient failure ({str(exc)[:200]}); "
                        f"retrying in {wait}s ({transient_budget} transient retries left)",
                        flush=True,
                    )
                    time.sleep(wait)
                    continue
                break
        raise RunnerError(f"{self.backend_name} failed after {attempt + 1} attempts: {last_exc}")

    @abc.abstractmethod
    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        ...
