"""Regression tests for replacement options in blueprint generation.

The Web UI invokes ``generate_blueprint.py``. API runners replace folders in
Python, while agent runners are instructed to invoke ``new_blueprint.py``;
these tests ensure the explicit Force choice reaches that agent command.
"""
from __future__ import annotations

import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from generate_blueprint import _agent_prompt  # noqa: E402
import new_blueprint  # noqa: E402


class AgentPromptForceTests(unittest.TestCase):
    def test_force_is_included_in_scaffold_command(self) -> None:
        prompt = _agent_prompt(
            "paper text",
            requested_name="simplex",
            source_label="paper.pdf",
            force=True,
        )

        self.assertIn("--description ... --force`", prompt)
        self.assertIn("MUST include `--force`", prompt)

    def test_force_is_absent_without_explicit_request(self) -> None:
        prompt = _agent_prompt(
            "paper text",
            requested_name="simplex",
            source_label="paper.pdf",
        )

        self.assertNotIn("--description ... --force`", prompt)
        self.assertIn("Do not replace an existing blueprint folder.", prompt)

    def test_no_build_changes_agent_instructions(self) -> None:
        prompt = _agent_prompt(
            "paper text",
            requested_name="simplex",
            source_label="paper.pdf",
            no_build=True,
        )

        self.assertIn("Do not build the site", prompt)
        self.assertNotIn("scripts/build.py <name>", prompt)


class ScaffoldForceTests(unittest.TestCase):
    def test_force_replaces_existing_folder(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            skeleton = root / "skeleton"
            blueprints = root / "blueprints"
            destination = blueprints / "example"
            skeleton.mkdir()
            (skeleton / "fresh.txt").write_text("fresh", encoding="utf-8")
            destination.mkdir(parents=True)
            (destination / "stale.txt").write_text("stale", encoding="utf-8")

            with (
                patch.object(new_blueprint, "REPO_ROOT", root),
                patch.object(new_blueprint, "SKELETON_DIR", skeleton),
                patch.object(new_blueprint, "BLUEPRINTS_DIR", blueprints),
            ):
                result = new_blueprint.main(["example", "--force"])

            self.assertEqual(result, 0)
            self.assertFalse((destination / "stale.txt").exists())
            self.assertEqual((destination / "fresh.txt").read_text(encoding="utf-8"), "fresh")
            self.assertTrue((destination / "meta.yml").is_file())


if __name__ == "__main__":
    unittest.main()
