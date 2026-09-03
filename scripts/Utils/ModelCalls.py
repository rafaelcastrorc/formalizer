"""Model runner construction, cancellation, and the _call_model choke point.

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


def _default_fast_runner_specs() -> tuple[str, str]:
    """Default two-tier model policy for the statements-first pipeline.

    Prefer cheap hosted API calls for the wide batched skeleton/proof work, then
    reserve the stronger tier for singleton proof retries and blueprint repair.
    If no API credentials are configured, fall back to local Codex models so the
    command still works on a developer machine.
    """
    def spec(backend: str, model: str) -> str:
        return f"{backend}:{model}" if model else backend

    if os.environ.get("OPENAI_API_KEY"):
        models: list[str] = []
        with contextlib.suppress(Exception):
            models = list_openai_model_ids(timeout=5)
        return (
            spec("openai", choose_model(models, prefer=("mini", "nano"))),
            spec("openai", choose_model(models, prefer=("gpt", "o"), avoid=("mini", "nano"))),
        )
    if os.environ.get("ANTHROPIC_API_KEY"):
        models = []
        with contextlib.suppress(Exception):
            models = list_anthropic_model_ids(timeout=5)
        return (
            spec("anthropic", choose_model(models, prefer=("haiku",))),
            spec("anthropic", choose_model(models, prefer=("sonnet", "opus"), avoid=("haiku",))),
        )
    models = list_codex_model_ids(timeout=5)
    return (
        spec("codex", choose_codex_base_model(models)),
        spec("codex", choose_codex_escalation_model(models)),
    )


def _make_runner(
    spec: str,
    *,
    timeout: int,
    readonly: bool,
    effort: str | None,
    with_skill: bool = False,
    resume_session_id: str | None = None,
):
    kwargs = {}
    if spec.partition(":")[0] == "codex" and effort:
        kwargs["reasoning_effort"] = effort
    return get_runner(
        spec,
        context_files=[SKILL_PATH] if with_skill else None,
        timeout=timeout,
        readonly=readonly,
        resume_session_id=resume_session_id,
        **kwargs,
    )


class _ModelCallControl:
    """Thread-safe handle used to cancel one in-flight model call."""

    def __init__(self) -> None:
        self._lock = threading.Lock()
        self._runner: Any | None = None
        self._cancelled = False

    def attach(self, runner: Any) -> None:
        with self._lock:
            self._runner = runner
            cancelled = self._cancelled
        if cancelled:
            runner.cancel()

    def detach(self, runner: Any) -> None:
        with self._lock:
            if self._runner is runner:
                self._runner = None

    def cancel(self) -> None:
        with self._lock:
            self._cancelled = True
            runner = self._runner
        if runner is not None:
            runner.cancel()


def _call_model(
    ctx: Ctx,
    prompt: str,
    *,
    purpose: str,
    timeout: int,
    effort: str | None,
    labels: list[str],
    readonly: bool = True,
    escalated: bool = False,
    tag: str = "",
    sessions: dict[str, str] | None = None,
    force_fresh: bool = False,
    control: _ModelCallControl | None = None,
) -> CallResult:
    """One model call. When ``sessions`` is given (a per-lifecycle dict keyed
    by runner spec), the call resumes that spec's backend session so follow-up
    calls keep the context they already built (claude-code and codex support
    this; other backends ignore it). ``force_fresh`` skips both lifecycle-local
    and persisted sessions for this call, while still recording the new session
    for later follow-ups. Successful calls update the dict; timed-out calls keep
    a captured session under the exact model-call fingerprint so an outer retry
    can resume instead of restarting cold. Non-timeout failures drop the session
    so the next call starts clean."""
    runner_spec = ctx.escalation_runner_spec if escalated else ctx.runner_spec
    resume_key = _model_resume_session_key(
        ctx,
        purpose=purpose,
        labels=labels,
        prompt=prompt,
        runner_spec=runner_spec,
    )
    local_resume_session = sessions.get(runner_spec) if sessions is not None else None
    resume_session_id = None if force_fresh else (
        local_resume_session
        or _get_model_resume_session(ctx, resume_key, runner_spec)
    )
    prompt_artifact = _store_text(ctx.telemetry, f"prompt_{purpose}", prompt)
    try:
        runner = _make_runner(
            runner_spec,
            timeout=timeout,
            readonly=readonly,
            effort=effort,
            resume_session_id=resume_session_id,
        )
        if control is not None:
            control.attach(runner)
    except RunnerError as exc:
        _record(
            ctx.telemetry,
            "model_call",
            purpose=purpose,
            labels=labels,
            status=_runner_failure_status(exc),
            duration_s=0.0,
            timeout_s=timeout,
            effort=effort or "",
            backend=runner_spec.partition(":")[0],
            model=runner_spec.partition(":")[2],
            resumed_session=bool(resume_session_id),
            forced_fresh_session=force_fresh,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
            transport_error=is_transient_error(exc),
        )
        if is_environment_error(exc) or is_transient_error(exc):
            # Missing CLI, expired auth, exhausted quota: no amount of
            # retrying, escalating, or repairing the blueprint can fix this.
            # Propagate so the run stops with saved state instead of spinning
            # generation -> escalation -> repair and burning the repair budget
            # against a dead backend (observed: 33 trials in 3 seconds).
            raise
        return CallResult(status="error", error=str(exc), duration_s=0.0)
    _log(
        f"==> Model call: {purpose} "
        f"({len(labels)} node(s), timeout {timeout}s"
        + (", escalated" if escalated else "")
        + (", resumed" if resume_session_id else "")
        + (", fresh" if force_fresh else "")
        + ")",
        tag=tag,
    )
    stage = (
        f"model_call purpose={purpose} labels={labels[:8]}"
        + ("..." if len(labels) > 8 else "")
        + f" timeout={timeout}s runner={runner_spec}"
        + (" escalated" if escalated else "")
        + (" resumed" if resume_session_id else "")
    )
    started = time.monotonic()
    try:
        with _stage(stage):
            result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        duration = time.monotonic() - started
        status = _runner_failure_status(exc)
        if is_environment_error(exc):
            if sessions is not None:
                sessions.pop(runner_spec, None)
            _clear_model_resume_session(ctx, resume_key)
            _record(
                ctx.telemetry,
                "model_call",
                purpose=purpose,
                labels=labels,
                status="error",
                duration_s=duration,
                timeout_s=timeout,
                effort=effort or "",
                backend=runner.backend_name,
                model=runner.model,
                resumed_session=bool(resume_session_id),
                forced_fresh_session=force_fresh,
                prompt=prompt_artifact.to_event(REPO_ROOT),
                error=str(exc),
                environment_error=True,
            )
            _log(f"model call ({purpose}) environment error: {str(exc)[:160]}", tag=tag)
            raise
        if status == "transport_exhausted":
            if sessions is not None:
                sessions.pop(runner_spec, None)
            _clear_model_resume_session(ctx, resume_key)
            _record(
                ctx.telemetry,
                "model_call",
                purpose=purpose,
                labels=labels,
                status="transport_exhausted",
                duration_s=duration,
                timeout_s=timeout,
                effort=effort or "",
                backend=runner.backend_name,
                model=runner.model,
                resumed_session=bool(resume_session_id),
                forced_fresh_session=force_fresh,
                prompt=prompt_artifact.to_event(REPO_ROOT),
                error=str(exc),
                environment_error=False,
                transport_error=True,
            )
            _log(
                f"model call ({purpose}) transport retries exhausted; "
                "saving run state without consuming a mathematical repair trial: "
                f"{str(exc)[:160]}",
                tag=tag,
            )
            raise
        observed = getattr(runner, "observed_session_id", None)
        captured_for_resume = bool(status == "timeout" and observed)
        if sessions is not None:
            if captured_for_resume:
                # The killed CLI already persisted its transcript and printed
                # its session id, so the retry can resume the exploration
                # instead of restarting cold. Resume is best-effort: both
                # runners fall back to a fresh session if the id is unusable.
                sessions[runner_spec] = observed
            else:
                sessions.pop(runner_spec, None)
        if captured_for_resume:
            _set_model_resume_session(
                ctx,
                resume_key,
                runner_spec,
                observed,
                labels=labels,
                prompt=prompt,
            )
        else:
            _clear_model_resume_session(ctx, resume_key)
        _record(
            ctx.telemetry,
            "model_call",
            purpose=purpose,
            labels=labels,
            status=status,
            duration_s=duration,
            timeout_s=timeout,
            effort=effort or "",
            backend=runner.backend_name,
            model=runner.model,
            resumed_session=bool(resume_session_id),
            forced_fresh_session=force_fresh,
            session_captured_for_resume=captured_for_resume,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
        )
        _log(f"model call ({purpose}) {status}: {str(exc)[:160]}", tag=tag)
        return CallResult(
            status=status,
            error=str(exc),
            duration_s=duration,
            partial_text=getattr(runner, "partial_text", "") if status == "timeout" else "",
        )
    finally:
        if control is not None:
            control.detach(runner)
    if sessions is not None:
        if result.session_id:
            sessions[runner_spec] = result.session_id
        else:
            sessions.pop(runner_spec, None)
    _clear_model_resume_session(ctx, resume_key)
    response_artifact = _store_text(ctx.telemetry, f"response_{purpose}", result.text)
    _record(
        ctx.telemetry,
        "model_call",
        purpose=purpose,
        labels=labels,
        status="success",
        duration_s=result.duration_s,
        timeout_s=timeout,
        effort=effort or "",
        backend=result.backend,
        model=result.model,
        resumed_session=bool(resume_session_id),
        forced_fresh_session=force_fresh,
        prompt=prompt_artifact.to_event(REPO_ROOT),
        response=response_artifact.to_event(REPO_ROOT),
    )
    return CallResult(status="ok", text=result.text, duration_s=result.duration_s)
