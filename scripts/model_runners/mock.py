"""Offline model runner for tests and demos.

The mock runner makes no network calls and does not require Codex, Claude Code,
OpenAI, or Anthropic credentials. It returns a tiny valid blueprint payload in
the same JSON shape expected from API runners, which lets us test
``generate_blueprint.py`` file writing and validation cheaply.
"""
from __future__ import annotations

import json
from pathlib import Path

from .base import ModelRunner, RunResult


class MockRunner(ModelRunner):
    backend_name = "mock"
    mode = "api"

    @classmethod
    def default_model(cls) -> str:
        return "mock"

    def _run_impl(self, prompt: str, system: str, cwd: Path | None) -> RunResult:
        payload = {
            "name": "mock-paper",
            "title": "Mock Paper",
            "authors": "Auto-Blueprint",
            "description": "A tiny generated blueprint used for runner smoke tests.",
            "home": "",
            "github": "",
            "build_pdf": False,
            "content_tex": (
                "\\chapter{Introduction}\n\n"
                "\\begin{definition}[Mock object]\n"
                "  \\label{def:mock-object}\n"
                "  A mock object is an object used for testing.\n"
                "\\end{definition}\n\n"
                "\\begin{theorem}[Mock theorem]\n"
                "  \\label{thm:mock-main}\n"
                "  \\uses{def:mock-object}\n"
                "  Every mock object is a mock object.\n"
                "\\end{theorem}\n"
                "\\begin{proof}\n"
                "  \\uses{def:mock-object}\n"
                "  This follows immediately from the definition.\n"
                "\\end{proof}\n"
            ),
        }
        return RunResult(text=json.dumps(payload, indent=2))
