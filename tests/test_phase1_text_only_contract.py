"""Regressions for the text-only read-only model-call contract.

Historical Simplex runs recorded Claude Phase 1 statement calls that answered
the read-only prompt with tool-invocation text, bare shell commands, or
investigation narration instead of Lean. The old budget sentence licensed
spending half the call "verifying library APIs or exploring", which no
text-only backend can do. These tests pin both halves of the fix:

- the recorded narration responses stay rejected at the shared ingestion
  boundary as ordinary generation failures (never accepted, never a crash);
- every read-only generation prompt states the text-only contract and no
  longer contains the exploration allowance, while the specific-import and
  statements-only rules remain intact.
"""
from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from formalize_blueprint import (  # noqa: E402
    _bulk_skeleton_prompt,
    _ingest_model_lean,
    _lean_name,
    _proof_prompt,
    _skeleton_prompt,
    _targeted_skeleton_patch_prompt,
    _text_only_budget_rule,
)
from validate_blueprint import Node  # noqa: E402

FIXTURE_DIR = REPO_ROOT / "tests" / "fixtures" / "phase1_tool_narration"

EXPLORATION_WORDING = "verifying library APIs"
TEXT_ONLY_WORDING = "text-only: no shell,\n  file, search, or web tool is available"


class FakeTelemetry:
    def __init__(self) -> None:
        self.events: list[tuple[str, dict]] = []

    def record(self, event: str, **fields) -> None:
        self.events.append((event, fields))


def _node(label: str, *, uses: set[str] | None = None) -> Node:
    return Node(
        label=label,
        kind="definition" if label.startswith("def:") else "lemma",
        file=Path("content.tex"),
        line=1,
        uses=uses or set(),
        statement_uses=set(uses or set()),
    )


def _ctx_for(labels: list[str]) -> SimpleNamespace:
    return SimpleNamespace(
        name="simplex",
        nodes={label: _node(label) for label in labels},
        stmt_blocks={label: "statement" for label in labels},
        tex_blocks={label: "statement with proof" for label in labels},
        stmt_fps={label: "fp" for label in labels},
        design_plan_entries={},
        semantic_plan_entries={},
        generation_feedback={},
        unavailable_imports=set(),
        library_context="",
        library_candidates=[],
        conjecture_policy="record",
        telemetry=FakeTelemetry(),
    )


class RecordedNarrationResponseTests(unittest.TestCase):
    """The exact recorded no-Lean responses are deterministic rejections."""

    def test_recorded_tool_narration_responses_are_rejected_as_format_failures(
        self,
    ) -> None:
        cases = json.loads((FIXTURE_DIR / "cases.json").read_text("utf-8"))
        self.assertGreaterEqual(len(cases), 4)
        for case in cases:
            response = (FIXTURE_DIR / case["response_file"]).read_text("utf-8")
            ctx = _ctx_for(case["labels"])
            with self.subTest(case=case["case"]):
                with self.assertRaises(ValueError) as raised:
                    _ingest_model_lean(
                        ctx,
                        case["labels"],
                        response,
                        defer_phase1_bodies=True,
                    )
                self.assertIn(
                    "model response contains unsupported module-level command",
                    str(raised.exception),
                )


class TextOnlyPromptContractTests(unittest.TestCase):
    """Every read-only generation prompt carries the text-only contract."""

    def _assert_contract(self, prompt: str) -> None:
        self.assertNotIn(EXPLORATION_WORDING, prompt)
        self.assertNotIn("exploring", prompt)
        self.assertIn(TEXT_ONLY_WORDING, prompt)
        self.assertIn("already verified, so reason\n  directly from them", prompt)
        self.assertIn(
            "Never end the budget without having\n  produced the requested code",
            prompt,
        )

    def test_budget_rule_names_the_timeout(self) -> None:
        rule = _text_only_budget_rule(300)
        self.assertIn("about 300s", rule)
        self.assertNotIn(EXPLORATION_WORDING, rule)

    def test_bulk_skeleton_prompt(self) -> None:
        labels = ["def:pk", "lem:support-sum"]
        ctx = _ctx_for(labels)
        with patch(
            "formalize_blueprint._frozen_interface_digest", return_value="-- iface"
        ), patch(
            "formalize_blueprint._dependency_contract_table", return_value="table"
        ), patch(
            "formalize_blueprint._design_plan_block", return_value="PLAN"
        ), patch(
            "formalize_blueprint._common_rules", return_value="COMMON"
        ):
            prompt = _bulk_skeleton_prompt(ctx, labels, [], [], timeout_s=300)
        self._assert_contract(prompt)
        self.assertIn("statements only, no proofs", prompt)

    def test_skeleton_retry_prompt(self) -> None:
        labels = ["def:pk"]
        ctx = _ctx_for(labels)
        with patch(
            "formalize_blueprint._minimal_dependency_interface",
            return_value="-- iface",
        ), patch(
            "formalize_blueprint._dependency_contract_table", return_value="table"
        ), patch(
            "formalize_blueprint._design_plan_block", return_value="PLAN"
        ), patch(
            "formalize_blueprint._local_node_summary", return_value="- nearby"
        ), patch(
            "formalize_blueprint._common_rules", return_value="COMMON"
        ):
            prompt = _skeleton_prompt(
                ctx, labels, [], [], feedback="fix it", timeout_s=300
            )
        self._assert_contract(prompt)
        self.assertIn("statements only", prompt)

    def test_targeted_patch_prompt(self) -> None:
        labels = ["def:pk"]
        ctx = _ctx_for(labels)
        with patch(
            "formalize_blueprint._minimal_dependency_interface",
            return_value="-- iface",
        ), patch(
            "formalize_blueprint._planned_helper_specs", return_value=[]
        ), patch(
            "formalize_blueprint._design_plan_block", return_value="PLAN"
        ), patch(
            "formalize_blueprint._common_rules", return_value="COMMON"
        ):
            prompt = _targeted_skeleton_patch_prompt(
                ctx,
                labels,
                [],
                [],
                f"def {_lean_name(labels[0])} : Prop := sorry",
                [],
                timeout_s=300,
            )
        self._assert_contract(prompt)

    def test_proof_prompt(self) -> None:
        labels = ["lem:support-sum"]
        ctx = _ctx_for(labels)
        with patch(
            "formalize_blueprint._frozen_interface_digest", return_value="-- iface"
        ), patch(
            "formalize_blueprint._downstream_proof_context", return_value=""
        ), patch(
            "formalize_blueprint._common_rules", return_value="COMMON"
        ):
            prompt = _proof_prompt(
                ctx,
                [(labels[0], "theorem lem_support_sum : True := sorry")],
                [],
                [],
                timeout_s=600,
            )
        self._assert_contract(prompt)

    def test_specific_import_rule_is_untouched(self) -> None:
        # _common_rules still forbids blanket imports; the budget rule change
        # must not alter that contract.
        from formalize_blueprint import _common_rules

        ctx = _ctx_for(["def:pk"])
        rules = _common_rules(ctx, ["def:pk"])
        self.assertIn("never blanket `import Mathlib`", rules)
        self.assertIn("module paths verified by deterministic search", rules)


if __name__ == "__main__":
    unittest.main()
