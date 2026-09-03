"""Global locks, per-thread stage tracking, and thread-safe log/telemetry primitives.

Part of formalize_blueprint.py — the statements-first Lean formalization
pipeline. This file is not an importable module: formalize_blueprint.py
compiles and executes every part file into its own module namespace, in a
fixed order, so the pipeline keeps the single `formalize_blueprint`
namespace that its tests and tooling patch and import against. Names used
here may therefore be defined in earlier parts or in
formalize_blueprint.py's import block. See organize.md.
"""
from __future__ import annotations
# ruff: noqa: F821

_ACTIVE_STAGE_LOCK = threading.Lock()
_ACTIVE_STAGES: dict[int, str] = {}


def _set_active_stage(stage: str) -> None:
    with _ACTIVE_STAGE_LOCK:
        thread_id = threading.get_ident()
        if stage:
            _ACTIVE_STAGES[thread_id] = stage
        else:
            _ACTIVE_STAGES.pop(thread_id, None)


def _active_stage() -> str:
    with _ACTIVE_STAGE_LOCK:
        current = _ACTIVE_STAGES.get(threading.get_ident())
        if current:
            return current
        active = list(dict.fromkeys(_ACTIVE_STAGES.values()))
        return " | ".join(active) if active else "idle"


def _thread_active_stage() -> str:
    with _ACTIVE_STAGE_LOCK:
        return _ACTIVE_STAGES.get(threading.get_ident(), "")


@contextlib.contextmanager
def _stage(stage: str):
    previous = _thread_active_stage()
    _set_active_stage(stage)
    try:
        yield
    finally:
        _set_active_stage(previous)

_PRINT_LOCK = threading.Lock()
_TELEMETRY_LOCK = threading.Lock()
# Phase 1 workers share retry candidates and rejection evidence.  State helpers
# call one another (for example, a read prunes stale entries first), so this
# must be reentrant and every compound read/modify/write must use it.
_STATE_LOCK = threading.RLock()


def _log(message: str, *, tag: str = "") -> None:
    with _PRINT_LOCK:
        prefix = f"[{tag}] " if tag else ""
        print(f"{prefix}{message}", flush=True)


def _record(telemetry: TelemetryRun, event: str, **fields) -> None:
    with _TELEMETRY_LOCK:
        telemetry.record(event, **fields)


def _store_text(telemetry: TelemetryRun, kind: str, text: str, *, ext: str = "txt"):
    with _TELEMETRY_LOCK:
        return telemetry.store_text(kind, text, ext=ext)
