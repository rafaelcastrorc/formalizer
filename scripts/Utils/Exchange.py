"""Phase-1 exchange sample budget and model resume-session store.

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


def _phase1_exchange_start(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    prompt: str,
    candidate_code: str,
    purpose: str,
    tier: str,
) -> str:
    """Reserve one sample for an exact Phase-1 model-call context.

    The existing local correction allowance is three stochastic samples.  The
    reservation is persisted so an outer retry, process restart, or
    ``--continue`` cannot silently reset that allowance.  An empty return value
    means the exact statement/plan/model/prompt epoch is exhausted and the
    caller must route the retained evidence without launching another model.
    """
    ordered = list(dict.fromkeys(labels))
    statement_fps = getattr(ctx, "stmt_fps", {}) or {}
    payload = {
        "labels": ordered,
        "statement_fps": {
            label: statement_fps.get(label, "") for label in ordered
        },
        "plan_fps": {
            label: _candidate_plan_fingerprint(ctx, label) for label in ordered
        },
        "candidate_sha256": hashlib.sha256(
            candidate_code.encode("utf-8")
        ).hexdigest(),
        "purpose": purpose,
        "tier": tier,
        "runner_spec": str(
            getattr(ctx, "escalation_runner_spec", "")
            if tier == "escalation"
            else getattr(ctx, "runner_spec", "")
        ),
        "prompt_sha256": hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
    }
    key = hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()
    with _STATE_LOCK:
        history = getattr(ctx, "phase1_exchange_history", None)
        if history is None:
            history = {}
            ctx.phase1_exchange_history = history
        previous = history.get(key) or {}
        launches = int(previous.get("launches") or 0)
        if launches >= PHASE1_EXCHANGE_SAMPLE_LIMIT:
            return ""
        history[key] = {
            **payload,
            "launches": launches + 1,
            "response_sha256s": list(previous.get("response_sha256s") or [])[-3:],
            "statuses": list(previous.get("statuses") or [])[-3:],
        }
    return key


def _phase1_exchange_finish(
    ctx: Ctx,
    key: str,
    *,
    status: str,
    response_text: str = "",
) -> bool:
    """Persist an outcome and report a byte-identical successful response."""
    response_hash = (
        hashlib.sha256(response_text.encode("utf-8")).hexdigest()
        if response_text
        else ""
    )
    with _STATE_LOCK:
        history = getattr(ctx, "phase1_exchange_history", {})
        entry = history.get(key)
        if not isinstance(entry, dict):
            return False
        responses = list(entry.get("response_sha256s") or [])
        duplicate = bool(response_hash and response_hash in responses)
        if response_hash and not duplicate:
            responses.append(response_hash)
        entry["response_sha256s"] = responses[-3:]
        statuses = list(entry.get("statuses") or [])
        statuses.append(status)
        entry["statuses"] = statuses[-4:]
    return duplicate


def _model_resume_session_key(
    ctx: Ctx,
    *,
    purpose: str,
    labels: Iterable[str],
    prompt: str,
    runner_spec: str,
) -> str:
    """Stable key for carrying a captured model session across retries."""
    ordered = list(dict.fromkeys(labels))
    statement_fps = getattr(ctx, "stmt_fps", {}) or {}
    payload = {
        "purpose": purpose,
        "labels": ordered,
        "statement_fps": {
            label: statement_fps.get(label, "") for label in ordered
        },
        "plan_fps": {
            label: _candidate_plan_fingerprint(ctx, label) for label in ordered
        },
        "runner_spec": runner_spec,
        "prompt_sha256": hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
    }
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _get_model_resume_session(
    ctx: Ctx, key: str, runner_spec: str
) -> str | None:
    with _STATE_LOCK:
        entry = getattr(ctx, "model_resume_sessions", {}).get(key)
        if not isinstance(entry, dict):
            return None
        if str(entry.get("runner_spec") or "") != runner_spec:
            return None
        session_id = str(entry.get("session_id") or "")
        return session_id or None


def _set_model_resume_session(
    ctx: Ctx,
    key: str,
    runner_spec: str,
    session_id: str,
    *,
    labels: Iterable[str],
    prompt: str,
) -> None:
    if not session_id:
        return
    ordered = list(dict.fromkeys(labels))
    statement_fps = getattr(ctx, "stmt_fps", {}) or {}
    with _STATE_LOCK:
        store = getattr(ctx, "model_resume_sessions", None)
        if store is None:
            store = {}
            ctx.model_resume_sessions = store
        store[key] = {
            "runner_spec": runner_spec,
            "session_id": session_id,
            "purpose": "model_call_resume",
            "labels": ordered,
            "statement_fps": {
                label: statement_fps.get(label, "") for label in ordered
            },
            "plan_fps": {
                label: _candidate_plan_fingerprint(ctx, label) for label in ordered
            },
            "prompt_sha256": hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
        }


def _clear_model_resume_session(ctx: Ctx, key: str) -> None:
    with _STATE_LOCK:
        getattr(ctx, "model_resume_sessions", {}).pop(key, None)


def _prune_stale_model_resume_sessions(ctx: Ctx) -> set[str]:
    """Discard captured sessions whose statement/plan/prompt epoch changed."""
    with _STATE_LOCK:
        store = getattr(ctx, "model_resume_sessions", {})
        stale = {
            key
            for key, entry in store.items()
            if not isinstance(entry, dict)
            or any(
                label not in ctx.nodes
                or str((entry.get("statement_fps") or {}).get(label) or "")
                != ctx.stmt_fps.get(label, "")
                or str((entry.get("plan_fps") or {}).get(label) or "")
                != _candidate_plan_fingerprint(ctx, label)
                for label in entry.get("labels") or []
            )
        }
        for key in stale:
            store.pop(key, None)
    return stale


def _prune_stale_phase1_exchange_history(ctx: Ctx) -> set[str]:
    """Discard exchanges whose statement or accepted-plan epoch has changed."""
    with _STATE_LOCK:
        history = getattr(ctx, "phase1_exchange_history", {})
        stale = {
            key
            for key, entry in history.items()
            if not isinstance(entry, dict)
            or any(
                label not in ctx.nodes
                or str((entry.get("statement_fps") or {}).get(label) or "")
                != ctx.stmt_fps.get(label, "")
                or str((entry.get("plan_fps") or {}).get(label) or "")
                != _candidate_plan_fingerprint(ctx, label)
                for label in entry.get("labels") or []
            )
        }
        for key in stale:
            history.pop(key, None)
    return stale


def _clear_phase1_exchange_history(ctx: Ctx, labels: Iterable[str]) -> set[str]:
    """Forget model-exchange reservations involving a changed plan epoch."""
    wanted = set(labels)
    with _STATE_LOCK:
        history = getattr(ctx, "phase1_exchange_history", {})
        removed = {
            key
            for key, entry in history.items()
            if isinstance(entry, dict)
            and wanted.intersection(entry.get("labels") or [])
        }
        for key in removed:
            history.pop(key, None)
    return removed
