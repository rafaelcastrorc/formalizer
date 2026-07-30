from __future__ import annotations

import os
import sys
import unittest
from pathlib import Path
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from model_runners.api import AnthropicRunner, OpenAIRunner  # noqa: E402


class ApiTextOnlyTests(unittest.TestCase):
    def test_anthropic_request_defines_no_tools(self) -> None:
        payload = {
            "stop_reason": "end_turn",
            "content": [{"type": "text", "text": "ok"}],
        }
        with patch.dict(os.environ, {"ANTHROPIC_API_KEY": "test"}), patch(
            "model_runners.api._post_json", return_value=payload
        ) as post:
            AnthropicRunner(readonly=True, timeout=10).run("prompt", retries=0)
        self.assertNotIn("tools", post.call_args.args[1])

    def test_openai_request_defines_no_tools(self) -> None:
        payload = {
            "status": "completed",
            "output": [
                {"content": [{"type": "output_text", "text": "ok"}]}
            ],
        }
        with patch.dict(os.environ, {"OPENAI_API_KEY": "test"}), patch(
            "model_runners.api._post_json", return_value=payload
        ) as post:
            OpenAIRunner(readonly=True, timeout=10).run("prompt", retries=0)
        self.assertNotIn("tools", post.call_args.args[1])


if __name__ == "__main__":
    unittest.main()
