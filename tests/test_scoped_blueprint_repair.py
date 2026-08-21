from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from formalize_blueprint import (  # noqa: E402
    _repair_blueprint,
    _scoped_blueprint_repair_content,
    _scoped_blueprint_repair_prompt,
    _write_scoped_blueprint_repair_to,
)
from model_runners.base import RunResult  # noqa: E402


FIXTURE = (
    REPO_ROOT
    / "tests"
    / "fixtures"
    / "phase1_orchestration_replay"
    / "scoped_blueprint_repair.json"
)


def _cases() -> dict:
    return json.loads(FIXTURE.read_text(encoding="utf-8"))


class ScopedBlueprintRepairTests(unittest.TestCase):
    def test_valid_historical_shapes_preserve_unrelated_source(self) -> None:
        for case in _cases()["valid_cases"]:
            with self.subTest(case=case["name"]):
                updated, metadata = _scoped_blueprint_repair_content(
                    case["original_content"],
                    json.dumps(case["response"]),
                    requested_labels=case["requested_labels"],
                    existing_blocks=case["existing_blocks"],
                    existing_labels=case["existing_labels"],
                )
                self.assertEqual(
                    metadata["new_helper_labels"], case["expected_new_labels"]
                )
                for fragment in case["expected_contains"]:
                    self.assertIn(fragment, updated)
                for fragment in case["unchanged_fragments"]:
                    self.assertEqual(updated.count(fragment), 1)

    def test_invalid_historical_shapes_are_rejected_before_writing(self) -> None:
        for case in _cases()["invalid_cases"]:
            with self.subTest(case=case["name"]):
                with self.assertRaisesRegex(ValueError, case["expected_error"]):
                    _scoped_blueprint_repair_content(
                        case["original_content"],
                        json.dumps(case["response"]),
                        requested_labels=case["requested_labels"],
                        existing_blocks=case["existing_blocks"],
                        existing_labels=case["existing_labels"],
                    )

    def test_writer_uses_immutable_pre_call_source(self) -> None:
        case = _cases()["valid_cases"][0]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "content.tex"
            path.write_text("BACKEND-WROTE-UNAUTHORIZED-CONTENT\n", encoding="utf-8")
            _write_scoped_blueprint_repair_to(
                path,
                json.dumps(case["response"]),
                original_content=case["original_content"],
                requested_labels=case["requested_labels"],
                existing_blocks=case["existing_blocks"],
                existing_labels=case["existing_labels"],
            )
            updated = path.read_text(encoding="utf-8")
        self.assertNotIn("BACKEND-WROTE-UNAUTHORIZED-CONTENT", updated)
        self.assertIn("PREFIX", updated)
        self.assertIn("SUFFIX", updated)

    def test_prompt_is_return_only_and_provider_neutral(self) -> None:
        block = (
            "\\begin{lemma}\nTarget.\\label{lem:target}\n"
            "\\uses{def:base}\\end{lemma}"
        )
        node = SimpleNamespace(kind="lemma", uses={"def:base"})
        dependency = SimpleNamespace(kind="definition", uses=set())
        ctx = SimpleNamespace(
            nodes={"lem:target": node, "def:base": dependency},
            tex_blocks={"lem:target": block, "def:base": ""},
            stmt_blocks={"lem:target": block, "def:base": "Base definition."},
            paper_text="A short relevant paper excerpt.",
            phase2_started=False,
        )
        prompt = _scoped_blueprint_repair_prompt(
            ctx,
            ["lem:target"],
            "exact audit evidence",
            3,
            model_timeout_s=600,
        )
        self.assertIn("RETURN-SCOPED-BLUEPRINT-REPAIR", prompt)
        self.assertIn('"replacements"', prompt)
        self.assertNotIn("Current blueprint source", prompt)
        self.assertNotIn("edit it in place", prompt)
        self.assertIn("Do not inspect or edit", prompt)
        self.assertIn("exact audit evidence", prompt)

    def test_agent_and_api_coordinator_paths_are_both_read_only(self) -> None:
        old_block = "\\begin{lemma}Old.\\label{lem:target}\\end{lemma}"
        new_block = "\\begin{lemma}New.\\label{lem:target}\\end{lemma}"
        response = json.dumps(
            {"replacements": {"lem:target": new_block}, "notes": "scoped"}
        )

        class FakeCtx:
            def __init__(self, content_path: Path) -> None:
                self.content_path = content_path
                self.nodes = {"lem:target": SimpleNamespace(uses=set())}
                self.tex_blocks = {"lem:target": old_block}
                self.contract_fps = {"lem:target": "old"}
                self.escalation_runner_spec = "fake:model"
                self.escalation_effort = None
                self.hard_timeout = 60
                self.telemetry = object()
                self.last_blueprint_repair_rejection = ""

            def refresh_nodes(self, nodes) -> None:
                self.nodes = nodes
                self.contract_fps = {"lem:target": "new"}

        runner = SimpleNamespace(
            backend_name="fake",
            model="model",
            run=lambda *_args, **_kwargs: RunResult(text=response),
        )
        artifact = SimpleNamespace(to_event=lambda _root: {})
        validation = SimpleNamespace(
            ok=True, nodes={"lem:target": SimpleNamespace(uses=set())}
        )
        for agent_mode in (True, False):
            with self.subTest(agent_mode=agent_mode), tempfile.TemporaryDirectory() as tmp:
                content_path = Path(tmp) / "content.tex"
                content_path.write_text(old_block + "\n", encoding="utf-8")
                ctx = FakeCtx(content_path)
                with (
                    patch(
                        "formalize_blueprint._scoped_blueprint_repair_prompt",
                        return_value="scoped prompt",
                    ),
                    patch(
                        "formalize_blueprint._make_runner", return_value=runner
                    ) as make_runner,
                    patch(
                        "formalize_blueprint._validate_draft",
                        return_value=validation,
                    ),
                    patch("formalize_blueprint._store_text", return_value=artifact),
                    patch("formalize_blueprint._record"),
                ):
                    changed = _repair_blueprint(
                        ctx,
                        "evidence",
                        ["lem:target"],
                        trial=1,
                        max_trials=3,
                        escalation_note="",
                        repair_runner_agent=agent_mode,
                    )
                self.assertEqual(changed, {"lem:target"})
                self.assertIn("New.", content_path.read_text(encoding="utf-8"))
                self.assertTrue(make_runner.call_args.kwargs["readonly"])


if __name__ == "__main__":
    unittest.main()
