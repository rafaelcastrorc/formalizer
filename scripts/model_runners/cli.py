"""Local coding-agent runners for the current skill-like workflow.

These backends invoke installed CLI tools, not hosted APIs. They are useful when
you want the model to behave like a repo collaborator: inspect files, run
``scripts/new_blueprint.py``, edit ``content.tex``, run the validator, and run
the build.

Because agent mode can edit files, it is more flexible than API mode but less
deterministic. The deterministic safety gate is still
``scripts/validate_blueprint.py``.
"""
from __future__ import annotations

import json
import os
import re
import signal
import shutil
import subprocess
import tempfile
import threading
import time
from pathlib import Path

from .base import ModelRunner, RunnerError, RunResult

CODEX_APP_CLI = Path("/Applications/Codex.app/Contents/Resources/codex")
CLAUDE_APP_CLI = Path("/Applications/Claude.app/Contents/Resources/claude")


def _which_or_app(name: str, app_path: Path) -> str | None:
    exe = shutil.which(name)
    if exe:
        return exe
    if app_path.is_file():
        return str(app_path)
    return None


def list_codex_model_ids(*, timeout: int = 5) -> list[str]:
    """Return model slugs from the local Codex CLI catalog, if available."""
    exe = _which_or_app("codex", CODEX_APP_CLI)
    if not exe:
        return []
    try:
        proc = subprocess.run(
            [exe, "debug", "models"],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except (OSError, subprocess.TimeoutExpired):
        return []
    if proc.returncode != 0:
        return []
    payload = None
    for line in proc.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            payload = json.loads(line)
            break
        except json.JSONDecodeError:
            continue
    if not isinstance(payload, dict):
        return []
    slugs = [
        item.get("slug")
        for item in payload.get("models", [])
        if isinstance(item, dict)
        and isinstance(item.get("slug"), str)
        and item.get("visibility") != "hidden"
    ]
    return [slug for slug in slugs if slug]


def choose_codex_base_model(models: list[str]) -> str:
    """Pick the cheaper/lighter Codex model from the local catalog."""
    usable = [model for model in models if "review" not in model.lower()]
    for model in usable:
        if "mini" in model.lower():
            return model
    return usable[-1] if usable else ""


def choose_codex_escalation_model(models: list[str]) -> str:
    """Pick the strongest Codex model from the local catalog."""
    for model in models:
        low = model.lower()
        if "mini" not in low and "review" not in low:
            return model
    return choose_codex_base_model(models)


def _describe_tool_use(name: str, tool_input: dict) -> str:
    """One-line summary of an agent tool call for status output."""
    if name == "Bash":
        detail = tool_input.get("command", "")
    elif name in ("Read", "Edit", "Write", "NotebookEdit"):
        detail = tool_input.get("file_path", "")
    elif name in ("Grep", "Glob"):
        detail = tool_input.get("pattern", "")
    else:
        detail = ""
    detail = " ".join(str(detail).split())
    return f"{name}: {detail[:140]}" if detail else name


class ClaudeCodeRunner(ModelRunner):
    backend_name = "claude-code"
    mode = "agent"
    can_edit_files = True

    def __init__(
        self,
        model: str | None = None,
        *,
        allowed_tools: str = "Read,Grep,Glob,Bash,Edit,Write",
        disallowed_tools: str = "",
        max_turns: int = 60,
        **kwargs,
    ):
        super().__init__(model, **kwargs)
        self.allowed_tools = allowed_tools
        # --allowedTools only pre-approves; user/project settings can still
        # allow more. --disallowedTools is the hard block.
        self.disallowed_tools = disallowed_tools
        if self.readonly:
            self.allowed_tools = "Read,Grep,Glob"
            self.disallowed_tools = "Bash,Edit,Write,NotebookEdit,WebFetch,WebSearch"
        self.max_turns = max_turns

    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        exe = _which_or_app("claude", CLAUDE_APP_CLI)
        if not exe:
            raise RunnerError("`claude` CLI not found on PATH")
        # stream-json (which requires --verbose in -p mode) emits one JSON event
        # per line as the agent works, so we can narrate progress live instead
        # of sitting silent for the whole run.
        cmd = [
            exe, "-p", "--output-format", "stream-json", "--verbose",
            "--max-turns", str(self.max_turns),
        ]
        if self.allowed_tools:
            cmd += ["--allowedTools", self.allowed_tools]
        if self.disallowed_tools:
            cmd += ["--disallowedTools", self.disallowed_tools]
        if self.model:
            cmd += ["--model", self.model]
        if system:
            cmd += ["--append-system-prompt", system]

        if self.resume_session_id:
            try:
                return self._invoke(cmd + ["--resume", self.resume_session_id], prompt, cwd)
            except RunnerError as exc:
                if "timed out" in str(exc):
                    raise
                # Session may have expired or belong to another model; resume
                # is best-effort, so fall back to a fresh conversation.
                print(
                    f"  [claude] resume of session {self.resume_session_id[:8]}... failed "
                    f"({str(exc)[:120]}); starting fresh",
                    flush=True,
                )
        return self._invoke(cmd, prompt, cwd)

    def _invoke(self, cmd: list[str], prompt: str, cwd: Path | None) -> RunResult:
        proc = subprocess.Popen(
            cmd,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            cwd=str(cwd) if cwd else None,
            start_new_session=True,
        )
        assert proc.stdin and proc.stdout and proc.stderr

        def _feed_stdin() -> None:
            try:
                proc.stdin.write(prompt)
                proc.stdin.close()
            except (BrokenPipeError, OSError):
                pass

        stderr_lines: list[str] = []
        threading.Thread(target=_feed_stdin, daemon=True).start()
        stderr_thread = threading.Thread(
            target=lambda: stderr_lines.extend(proc.stderr), daemon=True
        )
        stderr_thread.start()

        timed_out = threading.Event()

        def _kill_on_timeout() -> None:
            timed_out.set()
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

        watchdog = threading.Timer(self.timeout, _kill_on_timeout)
        watchdog.daemon = True
        watchdog.start()

        start = time.monotonic()
        last_output = [start]
        heartbeat_stop = threading.Event()

        def _heartbeat() -> None:
            while not heartbeat_stop.wait(15):
                if time.monotonic() - last_output[0] >= 60:
                    elapsed = int(time.monotonic() - start)
                    print(
                        f"  [claude] still working... {elapsed // 60}m{elapsed % 60:02d}s elapsed",
                        flush=True,
                    )
                    last_output[0] = time.monotonic()

        threading.Thread(target=_heartbeat, daemon=True).start()

        result_event: dict | None = None
        final_text = ""
        session_id: str | None = None
        try:
            for line in proc.stdout:
                line = line.strip()
                if not line:
                    continue
                try:
                    event = json.loads(line)
                except json.JSONDecodeError:
                    continue
                last_output[0] = time.monotonic()
                etype = event.get("type")
                if isinstance(event.get("session_id"), str):
                    session_id = event["session_id"]
                if etype == "system" and event.get("subtype") == "init":
                    print(f"  [claude] session started (model {event.get('model', '?')})", flush=True)
                elif etype == "assistant":
                    for block in event.get("message", {}).get("content", []):
                        if block.get("type") == "tool_use":
                            desc = _describe_tool_use(block.get("name", "?"), block.get("input") or {})
                            print(f"  [claude] -> {desc}", flush=True)
                        elif block.get("type") == "text" and block.get("text", "").strip():
                            snippet = " ".join(block["text"].split())
                            print(f"  [claude] {snippet[:200]}", flush=True)
                elif etype == "result":
                    result_event = event
                    final_text = event.get("result") or ""
            returncode = proc.wait()
        finally:
            watchdog.cancel()
            heartbeat_stop.set()
            stderr_thread.join(timeout=1)

        if timed_out.is_set() and returncode != 0:
            raise RunnerError(f"claude CLI timed out after {self.timeout}s")
        if returncode != 0:
            tail = "\n".join(stderr_lines).strip()[-3000:]
            raise RunnerError(f"claude CLI exit {returncode}: {tail}")
        if not final_text:
            raise RunnerError("claude CLI returned empty output")
        elapsed = int(time.monotonic() - start)
        print(f"  [claude] finished in {elapsed // 60}m{elapsed % 60:02d}s", flush=True)
        return RunResult(text=final_text, raw=result_event, session_id=session_id)


class CodexRunner(ModelRunner):
    backend_name = "codex"
    mode = "agent"
    can_edit_files = True

    def __init__(
        self,
        model: str | None = None,
        *,
        sandbox: str = "workspace-write",
        reasoning_effort: str | None = None,
        **kwargs,
    ):
        super().__init__(model, **kwargs)
        self.sandbox = "read-only" if self.readonly else sandbox
        self.reasoning_effort = reasoning_effort

    # `codex exec` prints a "session id: <uuid>" banner line; that id is what
    # `codex exec resume <id>` accepts.
    _SESSION_ID_RE = re.compile(r"session id:\s*([0-9a-fA-F][0-9a-fA-F-]{7,63})", re.IGNORECASE)

    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        exe = _which_or_app("codex", CODEX_APP_CLI)
        if not exe:
            raise RunnerError("`codex` CLI not found on PATH or in /Applications/Codex.app")
        full_prompt = f"<system>\n{system}\n</system>\n\n{prompt}" if system else prompt
        exec_flags = [
            "--sandbox",
            self.sandbox,
            "--skip-git-repo-check",
        ]
        # `codex exec resume` does not accept every top-level `codex exec`
        # option. In particular, this CLI rejects `--sandbox` after the
        # `resume` subcommand with exit 2. A resumed session already carries
        # its sandbox/config, so only pass flags that `codex exec resume --help`
        # documents for the follow-up prompt.
        resume_flags = [
            "--skip-git-repo-check",
        ]
        if self.model:
            exec_flags += ["--model", self.model]
            resume_flags += ["--model", self.model]
        if self.reasoning_effort:
            reasoning_flag = ["-c", f'model_reasoning_effort="{self.reasoning_effort}"']
            exec_flags += reasoning_flag
            resume_flags += reasoning_flag
        if self.resume_session_id:
            try:
                return self._invoke(
                    [exe, "exec", "resume", self.resume_session_id, *resume_flags],
                    full_prompt,
                    cwd,
                )
            except RunnerError as exc:
                if "timed out" in str(exc):
                    raise
                # Resume is best-effort: the session may be gone, or this codex
                # CLI may predate `exec resume`. Fall back to a fresh call.
                print(
                    f"  ! codex resume of session {self.resume_session_id[:8]}... failed "
                    f"({str(exc)[:120]}); starting fresh",
                    flush=True,
                )
        return self._invoke([exe, "exec", *exec_flags], full_prompt, cwd)

    def _invoke(self, cmd: list[str], full_prompt: str, cwd: Path | None) -> RunResult:
        with tempfile.NamedTemporaryFile("r", suffix=".md", delete=False) as tmp:
            output_path = Path(tmp.name)
        cmd = [*cmd, "--output-last-message", str(output_path), "-"]
        try:
            print("  launching Codex CLI; live output follows if Codex emits any", flush=True)
            proc = subprocess.Popen(
                cmd,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                text=True,
                cwd=str(cwd) if cwd else None,
                start_new_session=True,
            )
            stdout, _stderr = proc.communicate(input=full_prompt, timeout=self.timeout)
            if proc.returncode != 0:
                tail = "\n".join((stdout or "").splitlines()[-12:])
                detail = f": {tail}" if tail else ""
                raise RunnerError(f"codex CLI exit {proc.returncode}{detail}")
            text = output_path.read_text(encoding="utf-8").strip() if output_path.exists() else ""
            if not text:
                text = (stdout or "").strip()
            if not text:
                raise RunnerError("codex CLI returned empty output")
            match = self._SESSION_ID_RE.search(stdout or "")
            return RunResult(text=text, session_id=match.group(1) if match else None)
        except subprocess.TimeoutExpired as exc:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.communicate()
            raise RunnerError(f"codex CLI timed out after {self.timeout}s") from exc
        finally:
            output_path.unlink(missing_ok=True)
