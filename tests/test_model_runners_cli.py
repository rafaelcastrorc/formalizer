from __future__ import annotations

import sys
import threading
import time
import unittest
from pathlib import Path
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from model_runners.base import RunnerError, RunResult  # noqa: E402
from model_runners.cli import (  # noqa: E402
    ClaudeCodeRunner,
    CodexRunner,
    _which_or_app,
)


class RunnerExecutableDiscoveryTests(unittest.TestCase):
    def test_gui_path_falls_back_to_chatgpt_bundled_codex(self) -> None:
        chatgpt_cli = Path("/Applications/ChatGPT.app/Contents/Resources/codex")
        old_codex_cli = Path("/Applications/Codex.app/Contents/Resources/codex")

        with patch("model_runners.cli.shutil.which", return_value=None), patch.object(
            Path,
            "is_file",
            autospec=True,
            side_effect=lambda path: path == chatgpt_cli,
        ):
            self.assertEqual(
                _which_or_app("codex", chatgpt_cli, old_codex_cli),
                str(chatgpt_cli),
            )


class CodexReadonlyTests(unittest.TestCase):
    def _captured_command(self, *, resume: bool) -> list[str]:
        runner = CodexRunner(readonly=True, timeout=10)
        if resume:
            runner.resume_session_id = "00000000-0000-0000-0000-000000000001"
        commands: list[list[str]] = []

        def invoke(cmd, _prompt, _cwd):
            commands.append(cmd)
            return RunResult(text="ok")

        with patch("model_runners.cli._which_or_app", return_value="codex"), patch.object(
            runner, "_invoke", side_effect=invoke
        ):
            runner._run_impl("prompt", "system", REPO_ROOT)
        self.assertEqual(len(commands), 1)
        return commands[0]

    def test_fresh_readonly_call_disables_all_shell_paths(self) -> None:
        command = self._captured_command(resume=False)
        self.assertIn("exec", command)
        self.assertEqual(command.count("shell_tool"), 1)
        self.assertEqual(command.count("unified_exec"), 1)
        self.assertEqual(command.count("code_mode_host"), 1)

    def test_resumed_readonly_call_keeps_shell_disabled(self) -> None:
        command = self._captured_command(resume=True)
        self.assertIn("resume", command)
        self.assertEqual(command.count("shell_tool"), 1)
        self.assertEqual(command.count("unified_exec"), 1)
        self.assertEqual(command.count("code_mode_host"), 1)

    def test_editable_agent_keeps_shell_available(self) -> None:
        runner = CodexRunner(readonly=False, timeout=10)
        commands: list[list[str]] = []

        with patch("model_runners.cli._which_or_app", return_value="codex"), patch.object(
            runner,
            "_invoke",
            side_effect=lambda cmd, _prompt, _cwd: (
                commands.append(cmd) or RunResult(text="ok")
            ),
        ):
            runner._run_impl("prompt", "system", REPO_ROOT)
        self.assertNotIn("shell_tool", commands[0])
        self.assertNotIn("unified_exec", commands[0])
        self.assertNotIn("code_mode_host", commands[0])

    def test_cancel_terminates_active_process(self) -> None:
        runner = CodexRunner(readonly=True, timeout=10)
        errors: list[Exception] = []

        def invoke() -> None:
            try:
                runner._invoke(
                    [sys.executable, "-c", "import time; time.sleep(30)"],
                    "prompt",
                    REPO_ROOT,
                )
            except Exception as exc:  # noqa: BLE001 - asserted below
                errors.append(exc)

        thread = threading.Thread(target=invoke)
        thread.start()
        deadline = time.monotonic() + 2
        while runner._active_process is None and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertIsNotNone(runner._active_process)
        runner.cancel()
        thread.join(timeout=2)

        self.assertFalse(thread.is_alive())
        self.assertEqual(len(errors), 1)
        self.assertIsInstance(errors[0], RunnerError)
        self.assertIn("cancelled", str(errors[0]))


class ClaudeReadonlyTests(unittest.TestCase):
    def test_readonly_call_disables_all_tools(self) -> None:
        runner = ClaudeCodeRunner(readonly=True, timeout=10)
        commands: list[list[str]] = []

        with patch("model_runners.cli._which_or_app", return_value="claude"), patch.object(
            runner,
            "_invoke",
            side_effect=lambda cmd, _prompt, _cwd: (
                commands.append(cmd) or RunResult(text="ok")
            ),
        ):
            runner._run_impl("prompt", "system", REPO_ROOT)

        command = commands[0]
        tools_index = command.index("--tools")
        self.assertEqual(command[tools_index + 1], "")
        blocked = command[command.index("--disallowedTools") + 1]
        for name in ("Bash", "Read", "Grep", "Glob", "Edit", "Write", "Task"):
            self.assertIn(name, blocked.split(","))

    def test_cancel_terminates_active_process(self) -> None:
        runner = ClaudeCodeRunner(readonly=True, timeout=10)
        errors: list[Exception] = []

        def invoke() -> None:
            try:
                runner._invoke(
                    [sys.executable, "-c", "import time; time.sleep(30)"],
                    "prompt",
                    REPO_ROOT,
                )
            except Exception as exc:  # noqa: BLE001 - asserted below
                errors.append(exc)

        thread = threading.Thread(target=invoke)
        thread.start()
        deadline = time.monotonic() + 2
        while runner._active_process is None and time.monotonic() < deadline:
            time.sleep(0.01)
        self.assertIsNotNone(runner._active_process)
        runner.cancel()
        thread.join(timeout=2)

        self.assertFalse(thread.is_alive())
        self.assertEqual(len(errors), 1)
        self.assertIsInstance(errors[0], RunnerError)
        self.assertIn("cancelled", str(errors[0]))


if __name__ == "__main__":
    unittest.main()
