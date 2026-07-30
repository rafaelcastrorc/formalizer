from __future__ import annotations

import sys
import unittest
from pathlib import Path
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from model_runners.base import RunResult  # noqa: E402
from model_runners.cli import ClaudeCodeRunner, CodexRunner  # noqa: E402


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


if __name__ == "__main__":
    unittest.main()
