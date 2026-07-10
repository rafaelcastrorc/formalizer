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
import shutil
import subprocess
import tempfile
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


class ClaudeCodeRunner(ModelRunner):
    backend_name = "claude-code"
    mode = "agent"
    can_edit_files = True

    def __init__(
        self,
        model: str | None = None,
        *,
        allowed_tools: str = "Read,Grep,Glob,Bash,Edit,Write",
        max_turns: int = 60,
        **kwargs,
    ):
        super().__init__(model, **kwargs)
        self.allowed_tools = allowed_tools
        self.max_turns = max_turns

    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        exe = _which_or_app("claude", CLAUDE_APP_CLI)
        if not exe:
            raise RunnerError("`claude` CLI not found on PATH")
        cmd = [exe, "-p", "--output-format", "json", "--max-turns", str(self.max_turns)]
        if self.allowed_tools:
            cmd += ["--allowedTools", self.allowed_tools]
        if self.model:
            cmd += ["--model", self.model]
        if system:
            cmd += ["--append-system-prompt", system]
        try:
            proc = subprocess.run(
                cmd,
                input=prompt,
                capture_output=True,
                text=True,
                cwd=str(cwd) if cwd else None,
                timeout=self.timeout,
            )
        except subprocess.TimeoutExpired as exc:
            raise RunnerError(f"claude CLI timed out after {self.timeout}s") from exc
        if proc.returncode != 0:
            tail = (proc.stderr or proc.stdout or "").strip()[-3000:]
            raise RunnerError(f"claude CLI exit {proc.returncode}: {tail}")
        try:
            payload = json.loads(proc.stdout)
            text = payload.get("result", "")
        except json.JSONDecodeError:
            payload, text = None, proc.stdout
        if not text:
            raise RunnerError("claude CLI returned empty output")
        return RunResult(text=text, raw=payload)


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
        self.sandbox = sandbox
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
            proc = subprocess.run(
                cmd,
                input=full_prompt,
                text=True,
                cwd=str(cwd) if cwd else None,
                timeout=self.timeout,
            )
            if proc.returncode != 0:
                raise RunnerError(f"codex CLI exit {proc.returncode}; see output above")
            text = output_path.read_text(encoding="utf-8").strip() if output_path.exists() else ""
            if not text:
                text = (proc.stdout or "").strip()
            if not text:
                raise RunnerError("codex CLI returned empty output")
            return RunResult(text=text)
        except subprocess.TimeoutExpired as exc:
            raise RunnerError(f"codex CLI timed out after {self.timeout}s") from exc
        finally:
            output_path.unlink(missing_ok=True)
