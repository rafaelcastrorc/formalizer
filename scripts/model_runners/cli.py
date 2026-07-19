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
        return RunResult(text=final_text, raw=result_event)


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

    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        exe = _which_or_app("codex", CODEX_APP_CLI)
        if not exe:
            raise RunnerError("`codex` CLI not found on PATH or in /Applications/Codex.app")
        full_prompt = f"<system>\n{system}\n</system>\n\n{prompt}" if system else prompt
        with tempfile.NamedTemporaryFile("r", suffix=".md", delete=False) as tmp:
            output_path = Path(tmp.name)
        cmd = [
            exe,
            "exec",
            "--sandbox",
            self.sandbox,
            "--skip-git-repo-check",
            "--output-last-message",
            str(output_path),
        ]
        if self.model:
            cmd += ["--model", self.model]
        if self.reasoning_effort:
            cmd += ["-c", f'model_reasoning_effort="{self.reasoning_effort}"']
        cmd += ["-"]
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
                raise RunnerError(f"codex CLI exit {proc.returncode}; see output above")
            text = output_path.read_text(encoding="utf-8").strip() if output_path.exists() else ""
            if not text:
                text = (stdout or "").strip()
            if not text:
                raise RunnerError("codex CLI returned empty output")
            return RunResult(text=text)
        except subprocess.TimeoutExpired as exc:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            proc.communicate()
            raise RunnerError(f"codex CLI timed out after {self.timeout}s") from exc
        finally:
            output_path.unlink(missing_ok=True)
