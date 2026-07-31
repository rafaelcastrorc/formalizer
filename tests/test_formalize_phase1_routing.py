from __future__ import annotations

import copy
import sys
import json
import re
import tempfile
import threading
import time
import unittest
from unittest.mock import patch
from pathlib import Path
from types import SimpleNamespace


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from formalize_blueprint import (  # noqa: E402
    AlignmentAuditResult,
    DESIGN_PLAN_SCHEMA_VERSION,
    PHASE1_STATEMENT_ORDER,
    PHASE2_PROOF_ORDER,
    _add_phase1_boilerplate_names,
    _bottom_up_proof_layers,
    _bottom_up_statement_layers,
    _bottom_up_ready_frontier,
    _apply_proof_batch,
    _apply_phase1_retry_scheduling,
    _apply_required_dependency_edges,
    _apply_skeleton_replacements,
    _audit_phase1_design_plan,
    _audit_phase1_layer_candidates,
    _dependency_contract_table,
    _delivered_decl_texts,
    _design_plan_block,
    _evaluate_design_plan_candidate,
    _merge_design_plan_candidates,
    _design_plan_prompt,
    _design_plan_contract_closure_findings,
    _ensure_phase1_design_plan,
    _findings_require_plan_revision,
    _generation_feedback_for,
    _generation_candidates_for,
    _invalid_mathlib_refusal_mappings,
    _route_lean_generation_failure,
    _invalidate_after_repair,
    _insert_statement_dependencies,
    _lean_error_shape,
    _lean_failure_fingerprint,
    _lean_name,
    _lean_compile_findings,
    _lean_declarations,
    _load_state,
    _model_alignment_audit,
    _minimal_dependency_interface,
    _note_frozen_section,
    _next_phase1_group,
    _next_implementation_frontier,
    _parts_around_labels,
    _parse_design_plan_entries,
    _prepare_blueprint_draft,
    _promote_blueprint_draft,
    _prune_stale_generated,
    _prune_stale_generation_feedback,
    _prune_stale_generation_candidates,
    _prune_stale_quarantine,
    _prune_stale_retry_lifecycle,
    _parse_module,
    _normalize_theorem_like_keywords,
    _canonicalize_model_lean,
    _closure_blocked_labels,
    _closure_findings_for_scope,
    _planned_helper_owner_by_name,
    _plan_owned_declaration_cycle_findings,
    _candidate_is_reusable_uncompiled,
    _candidate_transition_decision,
    _decomposition_orientation_findings,
    _isolated_deterministic_failure_labels,
    _quarantine_labels,
    _reactivate_deferred_sections,
    _retry_statement_patch_compile_once,
    _run_initial_declaration_pass,
    _run_phase1,
    _refine_statement_group,
    _phase1_repair_scope_violations,
    _generate_uncompiled_phase1_candidate,
    _compile_semantic_phase1_candidates,
    _compile_and_finalize_semantic_candidates,
    _correct_phase1_design_plan,
    _reusable_uncompiled_candidate,
    _retained_generation_candidate_code,
    _salvage_partial_phase1_response,
    _semantic_repair_candidate,
    _semantic_first_failure_request,
    _route_exhausted_phase1_semantics,
    _revise_semantic_candidates,
    _revise_exhausted_phase1_contracts,
    _run_validated_contract_phase1_layer,
    _repair_graph_distances,
    _save_state,
    _store_generation_feedback,
    _store_generation_candidates,
    _statement_audit_prompt,
    _stuck_state_for,
    _record_retry_failure,
    _retry_next_tier,
    _freeze_parts,
    _freeze_section,
    _frozen_labels,
    _phase2_body_progress,
    _generate_phase1_statement_group,
    _proved_labels,
    _reserved_labels,
    _requires_initial_declaration_pass,
    _skeleton_code_findings,
    _skeleton_deterministic_findings,
    _target_components_from_helpers,
    _top_down_statement_layers,
    _SectionNumberAllocator,
    CallResult,
    RepairRequest,
    Section,
    Phase1LayerCandidate,
    SectionStuckState,
    SkeletonFinding,
    TARGETED_DECL_PATCH_ROUNDS,
)
from validate_blueprint import Node, validate_blueprint  # noqa: E402
from build_classifier_dataset import build_datasets  # noqa: E402
from webui import build_command as build_webui_command  # noqa: E402


class FakeTelemetry:
    def __init__(self) -> None:
        self.events: list[tuple[str, dict]] = []

    def record(self, event: str, **fields) -> None:
        self.events.append((event, fields))


def node(
    label: str,
    *,
    uses: set[str] | None = None,
    mathlibok: bool = False,
    lean_decl: str | None = None,
) -> Node:
    return Node(
        label=label,
        kind="definition" if label.startswith("def:") else "lemma",
        file=Path("content.tex"),
        line=1,
        uses=uses or set(),
        mathlibok=mathlibok,
        lean_decl=lean_decl,
    )


class PhaseOneRoutingTests(unittest.TestCase):
    def setUp(self) -> None:
        self.nodes = {
            "def:finite-real-arrays": node(
                "def:finite-real-arrays", mathlibok=True, lean_decl="Fin"
            ),
            "def:inner-norm": node(
                "def:inner-norm",
                uses={"def:finite-real-arrays"},
                mathlibok=True,
                lean_decl="inner",
            ),
            "def:binary-vector-ops": node(
                "def:binary-vector-ops", uses={"def:finite-real-arrays"}
            ),
            "lem:binary-complement-inner": node(
                "lem:binary-complement-inner",
                uses={"def:binary-vector-ops", "def:inner-norm"},
            ),
        }
        self.ctx = SimpleNamespace(nodes=self.nodes)

    def test_generation_feedback_is_bound_to_statement_fingerprint(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"lem:a": node("lem:a")},
            stmt_fps={"lem:a": "statement-v1"},
            generation_feedback={},
            telemetry=telemetry,
        )
        _store_generation_feedback(
            ctx,
            ["lem:a"],
            "the audit requires the missing parameter",
            source="statement_audit",
        )
        self.assertIn("missing parameter", _generation_feedback_for(ctx, ["lem:a"]))

        ctx.stmt_fps["lem:a"] = "statement-v2"
        self.assertEqual(_prune_stale_generation_feedback(ctx), {"lem:a"})
        self.assertEqual(_generation_feedback_for(ctx, ["lem:a"]), "")

    def test_candidate_transition_requires_monotonic_deterministic_progress(self) -> None:
        previous = {
            "code": "old",
            "candidate_hash": "old-hash",
            "deterministic_violations": ["missing:a"],
        }
        regressing = {
            "candidate_hash": "new-hash",
            "deterministic_violations": ["missing:b"],
            "lean_status": "unknown",
        }
        improving = {
            "candidate_hash": "better-hash",
            "deterministic_violations": [],
            "lean_status": "unknown",
        }

        accepted, reason, regressed, improved = _candidate_transition_decision(
            previous, regressing
        )
        self.assertFalse(accepted)
        self.assertEqual(reason, "deterministic_regression")
        self.assertEqual(regressed, {"missing:b"})
        self.assertEqual(improved, {"missing:a"})

        accepted, reason, regressed, improved = _candidate_transition_decision(
            previous, improving
        )
        self.assertTrue(accepted)
        self.assertEqual(reason, "deterministic_progress")
        self.assertEqual(regressed, set())
        self.assertEqual(improved, {"missing:a"})

    def test_candidate_store_keeps_best_code_when_proposal_regresses(self) -> None:
        label = "def:network"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "network-v1"},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            telemetry=telemetry,
        )
        best = "def def_network : Nat := sorry"
        regressing = "theorem def_network : True := sorry"

        _store_generation_candidates(
            ctx, [label], best, source="initial", all_labels=[label]
        )
        best_hash = ctx.generation_candidates[label]["candidate_hash"]
        _store_generation_candidates(
            ctx, [label], regressing, source="patch", all_labels=[label]
        )

        self.assertEqual(ctx.generation_candidates[label]["code"], best)
        self.assertEqual(
            ctx.generation_candidates[label]["candidate_hash"], best_hash
        )
        transitions = [
            fields
            for event, fields in telemetry.events
            if event == "phase1_candidate_transition"
        ]
        self.assertFalse(transitions[-1]["accepted_as_best"])
        self.assertTrue(transitions[-1]["regressed_obligations"])
        self.assertIn("did not improve", ctx.generation_feedback[label]["evidence"])

    def test_correction_baseline_uses_retained_candidate_after_regression(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "network-v1"},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            telemetry=FakeTelemetry(),
            unavailable_imports=set(),
        )
        best = "def def_network : Nat := sorry"
        regressing = "theorem def_network : True := sorry"

        _store_generation_candidates(
            ctx, [label], best, source="initial", all_labels=[label]
        )
        _store_generation_candidates(
            ctx, [label], regressing, source="compiler_patch", all_labels=[label]
        )

        retained = _retained_generation_candidate_code(ctx, [label])
        self.assertIn(best, retained)
        self.assertNotIn(regressing, retained)

    def test_compiler_intermediate_survives_without_replacing_best(self) -> None:
        label = "def:network"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "network-v1"},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            telemetry=telemetry,
        )
        best = "def def_network : Nat := sorry"
        intermediate = "def def_network : Nat := by\n  sorry"
        first_error = "Candidate.lean:2:8: error: unknown identifier 'old_name'"
        next_error = "Candidate.lean:2:8: error: unknown identifier 'missing_name'"

        _store_generation_candidates(
            ctx, [label], best, source="initial", all_labels=[label]
        )
        _store_generation_candidates(
            ctx,
            [label],
            best,
            source="validated_contract_compile_baseline",
            all_labels=[label],
            lean_status="failed",
            lean_output=first_error,
        )
        _store_generation_candidates(
            ctx,
            [label],
            intermediate,
            source="validated_contract_compiler_check",
            all_labels=[label],
            lean_status="failed",
            lean_output=next_error,
        )

        entry = ctx.generation_candidates[label]
        self.assertEqual(entry["code"], best)
        self.assertEqual(entry["working_candidate"]["code"], intermediate)
        self.assertIn(intermediate, _generation_candidates_for(ctx, [label]))
        transition = [
            fields
            for event, fields in telemetry.events
            if event == "phase1_candidate_transition"
        ][-1]
        self.assertFalse(transition["accepted_as_best"])
        self.assertTrue(transition["accepted_as_working"])

    def test_compiling_intermediate_promotes_and_clears_transaction(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "network-v1"},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            telemetry=FakeTelemetry(),
        )
        best = "def def_network : Nat := sorry"
        intermediate = "def def_network : Nat := by\n  sorry"

        _store_generation_candidates(
            ctx,
            [label],
            best,
            source="validated_contract_compile_baseline",
            all_labels=[label],
            lean_status="failed",
            lean_output="Candidate.lean:1:1: error: unresolved placeholder",
        )
        _store_generation_candidates(
            ctx,
            [label],
            intermediate,
            source="validated_contract_compiler_check",
            all_labels=[label],
            lean_status="failed",
            lean_output="Candidate.lean:1:1: error: same count, later diagnostic",
        )
        _store_generation_candidates(
            ctx,
            [label],
            intermediate,
            source="validated_contract_compiler_check",
            all_labels=[label],
            lean_status="passed",
        )

        entry = ctx.generation_candidates[label]
        self.assertEqual(entry["code"], intermediate)
        self.assertEqual(entry["lean_status"], "passed")
        self.assertEqual(entry["working_candidate"], {})

    def test_candidate_store_retains_exact_compiler_and_semantic_evidence(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "network-v1"},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            telemetry=FakeTelemetry(),
        )
        code = "def def_network : Nat := sorry"
        _store_generation_candidates(
            ctx, [label], code, source="initial", all_labels=[label]
        )
        _store_generation_candidates(
            ctx,
            [label],
            code,
            source="compile",
            all_labels=[label],
            lean_status="failed",
            lean_output="Candidate.lean:4:2: error: type mismatch",
        )
        _store_generation_candidates(
            ctx,
            [label],
            code,
            source="audit",
            all_labels=[label],
            repair_stage="semantic_rejected",
            lean_status="passed",
            semantic_status="rejected",
            semantic_evidence="the declaration drops the network depth",
        )

        entry = ctx.generation_candidates[label]
        self.assertEqual(entry["lean_status"], "passed")
        self.assertIn("type mismatch", entry["lean_output"])
        self.assertEqual(entry["semantic_status"], "rejected")
        self.assertIn("network depth", entry["semantic_evidence"])
        self.assertEqual(entry["revision"], 1)

    def test_generation_candidate_is_reused_only_for_same_statement(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"lem:a": node("lem:a")},
            stmt_fps={"lem:a": "statement-v1"},
            generation_candidates={},
            telemetry=telemetry,
        )
        stored = _store_generation_candidates(
            ctx,
            ["lem:a"],
            "theorem lem_a (n : Nat) : n = n := sorry\n",
            source="statement_audit",
        )
        self.assertEqual(stored, ["lem:a"])
        self.assertIn(
            "theorem lem_a (n : Nat) : n = n := sorry",
            _generation_candidates_for(ctx, ["lem:a"]),
        )

        ctx.stmt_fps["lem:a"] = "statement-v2"
        self.assertEqual(_prune_stale_generation_candidates(ctx), {"lem:a"})
        self.assertEqual(_generation_candidates_for(ctx, ["lem:a"]), "")

    def test_generation_candidate_is_invalidated_when_plan_contract_changes(self) -> None:
        label = "def:a"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def_a : Nat",
                    "helpers": [],
                    "decisions": ["first contract"],
                }
            },
            generation_candidates={},
            telemetry=FakeTelemetry(),
        )
        _store_generation_candidates(
            ctx,
            [label],
            "def def_a : Nat := sorry\n",
            source="semantic_first_pre_audit",
            reusable_uncompiled=True,
        )

        ctx.design_plan_entries[label]["decisions"] = ["revised contract"]

        self.assertEqual(_prune_stale_generation_candidates(ctx), {label})

    def test_deterministically_valid_candidate_reuses_full_module_context(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"def:a": node("def:a")},
            stmt_fps={"def:a": "statement-v1"},
            generation_candidates={},
            unavailable_imports=set(),
            telemetry=telemetry,
        )
        _store_generation_candidates(
            ctx,
            ["def:a"],
            "import Mathlib\n\nopen scoped BigOperators\n\ndef def_a : Nat := 1\n",
            source="semantic_first_pre_audit",
            reusable_uncompiled=True,
            generation_tier="escalation",
        )
        with patch(
            "formalize_blueprint._missing_olean_imports", return_value=[]
        ), patch(
            "formalize_blueprint._sections_for_deps", return_value=["Generated.Dep"]
        ), patch(
            "formalize_blueprint._skeleton_code_findings", return_value=[]
        ), patch(
            "formalize_blueprint._skeleton_deterministic_findings", return_value=[]
        ):
            candidate = _reusable_uncompiled_candidate(ctx, ["def:a"], [])

        self.assertIsNotNone(candidate)
        assert candidate is not None
        self.assertEqual(candidate.generation_tier, "escalation")
        self.assertEqual(candidate.import_modules, ["Generated.Dep"])
        self.assertIn("import Mathlib", candidate.parsed.imports)
        self.assertIn("open scoped BigOperators", candidate.parsed.preamble)
        self.assertIn("def def_a : Nat := 1", candidate.parsed.decls[0].text)

    def test_rejected_candidate_cannot_bypass_regeneration(self) -> None:
        ctx = SimpleNamespace(
            nodes={"def:a": node("def:a")},
            stmt_fps={"def:a": "statement-v1"},
            generation_candidates={},
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )
        _store_generation_candidates(
            ctx,
            ["def:a"],
            "def def_a : Nat := 1\n",
            source="statement_audit",
        )
        self.assertIsNone(_reusable_uncompiled_candidate(ctx, ["def:a"], []))

    def test_legacy_incomplete_layer_sibling_is_migrated_as_reusable(self) -> None:
        self.assertTrue(
            _candidate_is_reusable_uncompiled(
                {
                    "source": "phase1_layer_7_incomplete_generation",
                    "reusable_uncompiled": False,
                }
            )
        )
        self.assertFalse(
            _candidate_is_reusable_uncompiled(
                {
                    "source": "semantic_first_deterministic",
                    "reusable_uncompiled": False,
                }
            )
        )

    def test_retry_lifecycle_is_monotone_and_statement_fingerprinted(self) -> None:
        ctx = SimpleNamespace(
            nodes={"lem:a": node("lem:a")},
            stmt_fps={"lem:a": "statement-v1"},
            retry_lifecycle={},
            telemetry=FakeTelemetry(),
        )
        exhausted = _record_retry_failure(
            ctx,
            ["lem:a"],
            stage="phase1_statement",
            attempted_tier="base",
            evidence="critic rejected it",
            source="test",
        )
        self.assertFalse(exhausted)
        self.assertEqual(
            _retry_next_tier(ctx, "lem:a", "phase1_statement"), "escalation"
        )
        exhausted = _record_retry_failure(
            ctx,
            ["lem:a"],
            stage="phase1_statement",
            attempted_tier="escalation",
            evidence="critic rejected it again",
            source="test",
        )
        self.assertEqual(exhausted, {"lem:a"})

        ctx.stmt_fps["lem:a"] = "statement-v2"
        self.assertEqual(
            _prune_stale_retry_lifecycle(ctx), {"phase1_statement:lem:a"}
        )
        self.assertEqual(_retry_next_tier(ctx, "lem:a", "phase1_statement"), "base")

    def test_deterministic_isolation_requires_an_owned_proper_subset(self) -> None:
        labels = ["def:a", "def:b", "def:c"]
        owned = [SkeletonFinding("bad b", label="def:b")]
        self.assertEqual(
            _isolated_deterministic_failure_labels(owned, labels), ["def:b"]
        )
        self.assertEqual(
            _isolated_deterministic_failure_labels(
                owned + [SkeletonFinding("file-level")], labels
            ),
            [],
        )

    def test_shared_failure_scope_router(self) -> None:
        labels = ["lem:a", "lem:b", "lem:c", "lem:d"]

        isolated = _route_lean_generation_failure(labels, ["lem:b"])
        self.assertEqual(isolated.action, "isolate")
        self.assertEqual(isolated.failed_labels, ("lem:b",))
        self.assertEqual(isolated.accepted_labels, ("lem:a", "lem:c", "lem:d"))
        self.assertEqual(
            isolated.parts,
            (("lem:a",), ("lem:b",), ("lem:c", "lem:d")),
        )

        unattributed = _route_lean_generation_failure(labels)
        self.assertEqual(unattributed.action, "bisect")
        self.assertEqual(
            unattributed.parts, (("lem:a", "lem:b"), ("lem:c", "lem:d"))
        )

        all_failed = _route_lean_generation_failure(labels, labels)
        self.assertEqual(all_failed.action, "bisect")

        singleton = _route_lean_generation_failure(["lem:a"], ["lem:a"])
        self.assertEqual(singleton.action, "singleton")
        self.assertEqual(
            _isolated_deterministic_failure_labels(
                [SkeletonFinding("bad", label=label) for label in labels], labels
            ),
            [],
        )

    def test_freeze_section_routes_only_deterministically_rejected_label(self) -> None:
        labels = ["lem:a", "lem:b", "lem:c"]
        nodes = {label: node(label) for label in labels}
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_blocks={label: label for label in labels},
            tex_blocks={label: label for label in labels},
            stmt_fps={label: f"fp-{label}" for label in labels},
            contract_fps={label: f"contract-{label}" for label in labels},
            generation_feedback={},
            quarantined_labels=set(),
            quarantine={},
            unavailable_imports=set(),
            base_timeout=30,
            hard_timeout=60,
            base_effort="medium",
            escalation_effort="high",
            runner_spec="codex:base",
            escalation_runner_spec="codex:strong",
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
            library_context="",
            library_candidates=[],
            paper_text="",
            defer_phase1_alignment=False,
            effective_section_size=3,
            section_size=3,
            section_clean_streak=0,
            proven_section_size=0,
        )
        response = CallResult(
            status="ok",
            text="""```lean
theorem lem_a : Nat = Nat := by sorry
theorem lem_b : Nat = Nat := by sorry
theorem lem_c : Nat = Nat := by sorry
```""",
        )
        finding = SkeletonFinding(
            "the declaration dropped a required parameter",
            label="lem:b",
            lean_name="lem_b",
        )
        with tempfile.TemporaryDirectory() as tmp, patch(
            "formalize_blueprint._section_module",
            return_value=(
                "AutoBlueprint.Generated.Paper.Skeleton01",
                Path(tmp) / "Skeleton01.lean",
            ),
        ), patch(
            "formalize_blueprint._skeleton_prompt", return_value="prompt"
        ), patch(
            "formalize_blueprint._call_model", return_value=response
        ), patch(
            "formalize_blueprint._skeleton_code_findings", return_value=[]
        ), patch(
            "formalize_blueprint._skeleton_deterministic_findings",
            return_value=[finding],
        ), patch(
            "formalize_blueprint._targeted_patch_skeleton_decls",
            return_value=(None, "not patchable"),
        ), patch(
            "formalize_blueprint._freeze_parts", return_value=[]
        ) as freeze_parts:
            _freeze_section(ctx, labels, [], _SectionNumberAllocator(1))

        self.assertEqual(ctx.quarantined_labels, {"lem:b"})
        self.assertIn("dropped a required parameter", ctx.generation_feedback["lem:b"]["evidence"])
        self.assertIn("theorem lem_b", ctx.generation_candidates["lem:b"]["code"])
        call = freeze_parts.call_args
        self.assertEqual(call.args[1], [["lem:a"], ["lem:b"], ["lem:c"]])
        self.assertEqual(call.kwargs["delivered_exclude"], {"lem:b"})

    def test_dependency_table_marks_mathlib_names_as_external(self) -> None:
        table = _dependency_contract_table(
            self.ctx,
            ["def:binary-vector-ops", "lem:binary-complement-inner"],
            [],
        )
        self.assertIn("use `inner` exactly", table)
        self.assertIn("do NOT generate or request `def_inner_norm`", table)
        self.assertIn("generated earlier in this same file", table)

    def test_minimal_dependency_interface_is_complete_without_unrelated_declarations(self) -> None:
        nodes = {
            "def:support": node("def:support"),
            "def:dependency": node("def:dependency", uses={"def:support"}),
            "def:unrelated": node("def:unrelated"),
            "lem:target": node("lem:target", uses={"def:dependency"}),
        }
        ctx = SimpleNamespace(nodes=nodes)
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "def def_support : Type := Nat\n\n"
                "def def_dependency (x : def_support) : Nat := by sorry\n\n"
                "def def_unrelated : Bool := true\n",
                encoding="utf-8",
            )
            section = Section(
                number=1,
                labels=["def:support", "def:dependency", "def:unrelated"],
                path=path,
                module="AutoBlueprint.Generated.Paper.Skeleton01",
                import_modules=[],
            )
            interface = _minimal_dependency_interface(
                ctx,
                ["lem:target"],
                [section],
                [section.module],
            )

        self.assertIn("def_dependency", interface)
        self.assertIn("def_support", interface)
        self.assertNotIn("def_unrelated", interface)

    def test_minimal_dependency_interface_rejects_missing_required_name(self) -> None:
        ctx = SimpleNamespace(
            nodes={
                "def:dependency": node("def:dependency"),
                "lem:target": node("lem:target", uses={"def:dependency"}),
            }
        )
        with self.assertRaisesRegex(ValueError, "missing def:dependency"):
            _minimal_dependency_interface(ctx, ["lem:target"], [], [])

    def test_alignment_audit_routes_explicit_decomposition(self) -> None:
        ctx = SimpleNamespace(
            name="paper",
            nodes={"def:bundled": node("def:bundled")},
            tex_blocks={"def:bundled": "Define f and assert property P."},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=10,
            base_effort="medium",
            hard_timeout=20,
            escalation_effort="high",
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "classification": "needs_decomposition",
                    "issues": [
                        {
                            "node": "def:bundled",
                            "severity": "reject",
                            "reason": "The property needs its own declaration.",
                            "missing_helpers": ["P holds for the defined f"],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(
                ctx,
                ["def:bundled"],
                "def def_bundled : Nat := 0\n",
            )
        self.assertIsNotNone(audit)
        kind, _reason, rejected, helpers = audit
        self.assertEqual(kind, "decomposition")
        self.assertEqual(rejected, {"def:bundled"})
        self.assertEqual(helpers, ["P holds for the defined f"])

    def test_alignment_audit_routes_mixed_batch_per_node(self) -> None:
        bundled = "def:bundled"
        translated = "lem:translated"
        ctx = SimpleNamespace(
            name="paper",
            nodes={bundled: node(bundled), translated: node(translated)},
            tex_blocks={
                bundled: "Define the construction and its concrete interface.",
                translated: "The translated equality holds.",
            },
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=10,
            base_effort="medium",
            hard_timeout=20,
            escalation_effort="high",
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "classification": "mixed",
                    "issues": [
                        {
                            "node": bundled,
                            "severity": "reject",
                            "classification": "needs_decomposition",
                            "reason": "The construction has no named interface.",
                            "missing_helpers": [
                                "define the construction used by the theorem"
                            ],
                        },
                        {
                            "node": translated,
                            "severity": "reject",
                            "classification": "lean_translation_issue",
                            "reason": "The generated equality reverses its operands.",
                            "missing_helpers": [],
                        },
                    ],
                }
            ),
        )
        code = (
            "def def_bundled : Nat := 0\n"
            "theorem lem_translated : True := by sorry\n"
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(ctx, [bundled, translated], code)

        self.assertIsNotNone(audit)
        self.assertEqual(audit.kind, "mixed")
        self.assertEqual(audit.labels_for("decomposition"), {bundled})
        self.assertEqual(audit.labels_for("lean-generation"), {translated})
        self.assertEqual(
            audit.helpers_for({bundled}),
            ["define the construction used by the theorem"],
        )

        candidates = [
            Phase1LayerCandidate(
                labels=[bundled, translated],
                parsed=_parse_module(code),
                import_modules=[],
                generation_tier="base",
            )
        ]
        with patch(
            "formalize_blueprint._record_retry_failure", return_value=set()
        ), patch(
            "formalize_blueprint._store_generation_candidates"
        ), patch(
            "formalize_blueprint._store_generation_feedback"
        ), patch(
            "formalize_blueprint._quarantine_labels"
        ):
            request = _semantic_first_failure_request(
                ctx, 3, candidates, audit, []
            )

        self.assertTrue(request.authorizes_blueprint_repair)
        self.assertEqual(request.labels, [bundled])
        self.assertEqual(
            request.decomposition_helpers,
            ["define the construction used by the theorem"],
        )

    def test_alignment_audit_does_not_rewrite_blueprint_for_representation_error(self) -> None:
        label = "def:polytope"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            tex_blocks={label: "A polytope is the convex hull of finitely many points."},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=10,
            base_effort="medium",
            hard_timeout=20,
            escalation_effort="high",
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "classification": "blueprint_issue",
                    "issues": [
                        {
                            "node": label,
                            "severity": "reject",
                            "reason": (
                                "The generated witness-carrying structure has "
                                "intensional rather than carrier equality."
                            ),
                            "missing_helpers": [],
                            "missing_blueprint_information": [],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(
                ctx,
                [label],
                "structure def_polytope where\n  carrier : Set Nat\n",
            )

        self.assertIsNotNone(audit)
        self.assertEqual(audit[0], "lean-generation")
        routing = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "statement_audit_routing"
        ]
        self.assertEqual(routing[-1]["reported_classification"], "blueprint_issue")
        self.assertFalse(routing[-1]["blueprint_repair_authorized"])

    def test_alignment_audit_requires_named_missing_fact_for_blueprint_repair(self) -> None:
        label = "thm:claim"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            tex_blocks={label: "For every x, f x = 0."},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=10,
            base_effort="medium",
            hard_timeout=20,
            escalation_effort="high",
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "classification": "blueprint_issue",
                    "issues": [
                        {
                            "node": label,
                            "severity": "reject",
                            "reason": "The domain of f is absent.",
                            "missing_helpers": [],
                            "missing_blueprint_information": [
                                "the domain and codomain of f"
                            ],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(
                ctx,
                [label],
                "theorem thm_claim : True := by sorry\n",
            )

        self.assertIsNotNone(audit)
        self.assertEqual(audit[0], "blueprint")

    def test_alignment_audit_preserves_required_statement_dependencies(self) -> None:
        target = "def:formal-difference"
        dependency = "def:polytope"
        ctx = SimpleNamespace(
            name="paper",
            nodes={target: node(target), dependency: node(dependency)},
            tex_blocks={target: "A formal difference of polytopes.", dependency: "A polytope."},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=10,
            base_effort="medium",
            hard_timeout=20,
            escalation_effort="high",
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "classification": "lean_translation_issue",
                    "issues": [
                        {
                            "node": target,
                            "severity": "reject",
                            "reason": "The public statement must quantify over polytopes.",
                            "missing_helpers": [],
                            "required_dependencies": [dependency, "missing:hallucination"],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(
                ctx, [target], "def def_formal_difference : Prop := sorry\n"
            )

        self.assertIsNotNone(audit)
        self.assertEqual(audit.required_dependencies, {target: {dependency}})

    def test_dependency_edge_insertion_preserves_node_prose(self) -> None:
        source = (
            "\\begin{definition}[Formal difference]\n"
            "  \\label{def:formal-difference}\n"
            "  \\uses{def:minkowski-join}\n"
            "  A polytope X satisfies X + P = Q.\n"
            "\\end{definition}\n"
        )
        updated, added = _insert_statement_dependencies(
            source, "def:formal-difference", {"def:polytope"}
        )

        self.assertEqual(added, {"def:polytope"})
        self.assertIn(
            r"\uses{def:minkowski-join, def:polytope}", updated
        )
        self.assertIn("A polytope X satisfies X + P = Q.", updated)

    def test_confirmed_dependency_edge_repair_updates_validated_draft(self) -> None:
        target = "def:formal-difference"
        dependency = "def:polytope"
        with tempfile.TemporaryDirectory() as tmp:
            content = Path(tmp) / "content.tex"
            content.write_text(
                "\\begin{definition}\n"
                f"  \\label{{{target}}}\n"
                "  \\uses{def:minkowski-join}\n"
                "  A formal difference of polytopes.\n"
                "\\end{definition}\n",
                encoding="utf-8",
            )
            target_before = node(target, uses={"def:minkowski-join"})
            target_before.file = content
            dependency_node = node(dependency)
            dependency_node.file = content
            target_after = node(
                target, uses={"def:minkowski-join", dependency}
            )
            target_after.file = content
            target_after.statement_uses = {"def:minkowski-join", dependency}
            dependency_after = node(dependency)
            dependency_after.file = content
            ctx = SimpleNamespace(
                nodes={target: target_before, dependency: dependency_node},
                telemetry=FakeTelemetry(),
            )
            ctx.refresh_nodes = lambda nodes: setattr(ctx, "nodes", nodes)
            validation = SimpleNamespace(
                ok=True,
                nodes={target: target_after, dependency: dependency_after},
            )
            with patch(
                "formalize_blueprint._validate_draft", return_value=validation
            ):
                changed = _apply_required_dependency_edges(
                    ctx, {target: {dependency}}
                )

            self.assertEqual(changed, {target})
            self.assertIn(
                r"\uses{def:minkowski-join, def:polytope}",
                content.read_text(encoding="utf-8"),
            )

    def test_cyclic_dependency_edge_is_rejected_before_file_edit(self) -> None:
        provider = "def:provider"
        consumer = "def:consumer"
        with tempfile.TemporaryDirectory() as tmp:
            content = Path(tmp) / "content.tex"
            original = (
                "\\begin{definition}\n"
                f"  \\label{{{provider}}}\n"
                "  Provider.\n"
                "\\end{definition}\n"
            )
            content.write_text(original, encoding="utf-8")
            provider_node = node(provider)
            provider_node.file = content
            consumer_node = node(consumer, uses={provider})
            consumer_node.file = content
            ctx = SimpleNamespace(
                nodes={provider: provider_node, consumer: consumer_node},
                telemetry=FakeTelemetry(),
            )

            with patch("formalize_blueprint._validate_draft") as validate:
                changed = _apply_required_dependency_edges(
                    ctx, {provider: {consumer}}
                )

            self.assertEqual(changed, set())
            self.assertEqual(content.read_text(encoding="utf-8"), original)
            validate.assert_not_called()
            rejection = ctx.last_dependency_edge_rejections[provider][consumer]
            self.assertIn(f"{consumer} -> {provider}", rejection)
            self.assertIn("would close the cycle", rejection)

    def test_decomposition_helpers_must_be_upstream_of_repaired_target(self) -> None:
        target = "def:cpwl"
        helper = "def:finite-subdivision"
        before = {target: node(target)}

        valid_target = node(target, uses={helper})
        valid_after = {target: valid_target, helper: node(helper)}
        self.assertEqual(
            _decomposition_orientation_findings(before, valid_after, [target]),
            [],
        )

        reversed_after = {
            target: node(target),
            helper: node(helper, uses={target}),
        }
        findings = _decomposition_orientation_findings(
            before, reversed_after, [target]
        )
        self.assertEqual(len(findings), 1)
        self.assertIn("instead of being their dependency", findings[0])

    def test_semantic_correction_routes_confirmed_dependency_to_blueprint(self) -> None:
        target = "def:formal-difference"
        dependency = "def:polytope"
        ctx = SimpleNamespace(
            nodes={target: node(target), dependency: node(dependency)},
            design_plan_entries={},
            telemetry=FakeTelemetry(),
            base_timeout=10,
            hard_timeout=20,
        )
        candidate = Phase1LayerCandidate(
            labels=[target],
            parsed=_parse_module("def def_formal_difference : Prop := sorry\n"),
            import_modules=[],
            generation_tier="base",
            sessions={},
        )
        corrected = _parse_module(
            "def def_formal_difference (_P : def_polytope) : Prop := sorry\n"
        )
        with patch(
            "formalize_blueprint._targeted_patch_skeleton_decls",
            return_value=(corrected, "patched"),
        ):
            with self.assertRaises(RepairRequest) as raised:
                _revise_semantic_candidates(
                    ctx,
                    [candidate],
                    {target},
                    "must quantify over polytopes",
                    [],
                    required_dependencies={target: {dependency}},
                )

        request = raised.exception
        self.assertTrue(request.authorizes_blueprint_repair)
        self.assertEqual(
            request.required_dependencies, {target: {dependency}}
        )

    def test_integrated_audit_request_preserves_required_dependencies(self) -> None:
        target = "lem:claim"
        dependency = "def:dependency"
        audit = AlignmentAuditResult(
            "lean-generation",
            "the statement requires an existing dependency",
            {target},
            [],
            {target: {dependency}},
        )
        ctx = SimpleNamespace(
            name="paper",
            nodes={target: node(target), dependency: node(dependency)},
            telemetry=FakeTelemetry(),
            lean_command=["lean"],
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "theorem lem_claim : True := by sorry\n", encoding="utf-8"
            )
            section = Section(
                1,
                [target],
                path,
                "Generated.Skeleton01",
                [],
                generation_tier="base",
            )
            with patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint.SCRATCH_DIR", Path(tmp)
            ), patch(
                "formalize_blueprint._model_alignment_audit", return_value=audit
            ), patch(
                "formalize_blueprint._store_generation_candidates"
            ), patch(
                "formalize_blueprint._record_retry_failure", return_value=set()
            ), patch(
                "formalize_blueprint._store_generation_feedback"
            ), patch(
                "formalize_blueprint._quarantine_labels"
            ), patch(
                "formalize_blueprint._discard_section_artifacts"
            ):
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(ctx, 0, [section])

        self.assertEqual(
            raised.exception.required_dependencies,
            {target: {dependency}},
        )

    def test_semantic_first_request_preserves_required_dependencies(self) -> None:
        target = "lem:claim"
        dependency = "def:dependency"
        audit = AlignmentAuditResult(
            "lean-generation",
            "the statement requires an existing dependency",
            {target},
            [],
            {target: {dependency}},
        )
        candidate = Phase1LayerCandidate(
            labels=[target],
            parsed=_parse_module("theorem lem_claim : True := by sorry\n"),
            import_modules=[],
            generation_tier="base",
        )
        ctx = SimpleNamespace(telemetry=FakeTelemetry())
        with patch(
            "formalize_blueprint._record_retry_failure", return_value=set()
        ), patch(
            "formalize_blueprint._store_generation_candidates"
        ), patch(
            "formalize_blueprint._store_generation_feedback"
        ), patch(
            "formalize_blueprint._quarantine_labels"
        ):
            request = _semantic_first_failure_request(
                ctx, 0, [candidate], audit, []
            )

        self.assertEqual(
            request.required_dependencies,
            {target: {dependency}},
        )

    def test_alignment_audit_reuses_accepted_statement_fingerprint(self) -> None:
        ctx = SimpleNamespace(
            name="paper",
            nodes={"lem:cached": node("lem:cached")},
            tex_blocks={"lem:cached": "The cached statement."},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=10,
            base_effort="medium",
            hard_timeout=20,
            escalation_effort="high",
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {"accepted": True, "classification": "accepted", "issues": []}
            ),
        )
        code = "theorem lem_cached : True := by sorry\n"
        with patch("formalize_blueprint._call_model", return_value=response) as call:
            self.assertIsNone(_model_alignment_audit(ctx, ["lem:cached"], code))
            self.assertIsNone(_model_alignment_audit(ctx, ["lem:cached"], code))
        self.assertEqual(call.call_count, 1)
        self.assertTrue(
            any(event == "statement_audit_cache_hit" for event, _ in ctx.telemetry.events)
        )

    def test_alignment_cache_includes_owned_local_helpers(self) -> None:
        ctx = SimpleNamespace(
            name="paper",
            nodes={"lem:cached": node("lem:cached")},
            tex_blocks={"lem:cached": "The cached statement."},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=10,
            base_effort="medium",
            hard_timeout=20,
            escalation_effort="high",
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {"accepted": True, "classification": "accepted", "issues": []}
            ),
        )
        first = (
            "def local_helper : Nat := 1\n\n"
            "theorem lem_cached : local_helper = 1 := by sorry\n"
        )
        changed_helper = (
            "def local_helper : Nat := 2\n\n"
            "theorem lem_cached : local_helper = 1 := by sorry\n"
        )
        with patch("formalize_blueprint._call_model", return_value=response) as call:
            self.assertIsNone(_model_alignment_audit(ctx, ["lem:cached"], first))
            self.assertIsNone(
                _model_alignment_audit(ctx, ["lem:cached"], changed_helper)
            )
        self.assertEqual(call.call_count, 2)

    def test_statement_audit_prompt_includes_referenced_local_interface(self) -> None:
        label = "def:relu-function"
        code = (
            "structure LocalReLUInterface where\n"
            "  scalar : Real -> Real\n"
            "  scalar_eq : forall t, scalar t = max 0 t\n\n"
            "def def_relu_function : LocalReLUInterface := sorry\n"
        )
        prompt = _statement_audit_prompt(
            "paper",
            {label: node(label)},
            {label: "Concrete scalar ReLU with ReLU(t) = max(0,t)."},
            _lean_declarations(code),
            "",
            skeleton_phase=True,
        )

        self.assertIn("structure LocalReLUInterface", prompt)
        self.assertIn("scalar_eq : forall t, scalar t = max 0 t", prompt)

    def test_multi_node_audit_failure_routes_without_whole_batch_escalation(self) -> None:
        labels = ["lem:a", "lem:b"]
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label) for label in labels},
            tex_blocks={label: f"Blueprint statement for {label}." for label in labels},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=10,
            base_effort="medium",
            hard_timeout=20,
            escalation_effort="high",
        )
        failed = CallResult(status="timeout", error="audit timed out")
        code = (
            "theorem lem_a : True := by sorry\n\n"
            "theorem lem_b : True := by sorry\n"
        )
        with patch("formalize_blueprint._call_model", return_value=failed) as call:
            audit = _model_alignment_audit(ctx, labels, code)

        self.assertEqual(call.call_count, 1)
        self.assertIsNotNone(audit)
        kind, reason, rejected, helpers = audit
        self.assertEqual(kind, "lean-generation")
        self.assertIn("timed out", reason)
        self.assertEqual(rejected, set(labels))
        self.assertEqual(helpers, [])

    def test_false_mathlib_refusal_is_detected_transitively(self) -> None:
        refusal = {
            "label": "lem:binary-complement-inner",
            "missing_helpers": ["def_inner_norm", "def_finite_real_arrays"],
            "reason": "The generated helper def_inner_norm is unavailable.",
        }
        self.assertEqual(
            _invalid_mathlib_refusal_mappings(self.ctx, refusal),
            {"def_inner_norm": "inner", "def_finite_real_arrays": "Fin"},
        )

    def test_refused_node_isolated_without_bisecting_neighbors(self) -> None:
        labels = ["a", "b", "hard", "c", "d"]
        self.assertEqual(
            _parts_around_labels(labels, ["hard"]),
            [["a", "b"], ["hard"], ["c", "d"]],
        )

    def test_capacity_recovers_exponentially_and_persists_on_context(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            effective_section_size=1,
            section_size=12,
            proven_section_size=1,
            section_clean_streak=0,
            quarantined_labels=set(),
            quarantine={},
            telemetry=telemetry,
        )
        _note_frozen_section(ctx, ["a"])
        self.assertEqual(ctx.effective_section_size, 1)
        _note_frozen_section(ctx, ["b"])
        self.assertEqual(ctx.effective_section_size, 2)
        _note_frozen_section(ctx, ["c", "d"])
        _note_frozen_section(ctx, ["e", "f"])
        self.assertEqual(ctx.effective_section_size, 4)
        self.assertEqual(
            [fields["size"] for event, fields in telemetry.events if event == "adaptive_section_size"],
            [2, 4],
        )

    def test_isolated_singleton_does_not_regrow_broad_capacity(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            effective_section_size=6,
            section_size=12,
            proven_section_size=12,
            section_clean_streak=1,
            quarantined_labels={"hard"},
            quarantine={
                "hard": {
                    "statement_fp": "hard-v1",
                    "failure_class": "lean_compile_failure",
                }
            },
            telemetry=telemetry,
        )
        _note_frozen_section(ctx, ["hard"])
        self.assertEqual(ctx.effective_section_size, 6)
        self.assertEqual(ctx.section_clean_streak, 1)
        self.assertNotIn("hard", ctx.quarantined_labels)
        self.assertNotIn("hard", ctx.quarantine)

    def test_quarantine_is_released_when_statement_fingerprint_changes(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"hard": node("hard")},
            stmt_fps={"hard": "hard-v1"},
            quarantined_labels=set(),
            quarantine={},
            telemetry=telemetry,
        )
        _quarantine_labels(ctx, ["hard"], "lean_compile_failure")
        self.assertEqual(ctx.quarantined_labels, {"hard"})
        self.assertEqual(
            ctx.quarantine["hard"],
            {
                "statement_fp": "hard-v1",
                "failure_class": "lean_compile_failure",
            },
        )

        ctx.stmt_fps["hard"] = "hard-v2"
        self.assertEqual(_prune_stale_quarantine(ctx), {"hard"})
        self.assertFalse(ctx.quarantined_labels)
        self.assertFalse(ctx.quarantine)
        event, fields = telemetry.events[-1]
        self.assertEqual(event, "skeleton_quarantine_released")
        self.assertEqual(fields["labels"], ["hard"])
        self.assertEqual(fields["reason"], "statement_fingerprint_changed")
        self.assertEqual(fields["records"]["hard"]["statement_fp"], "hard-v1")

    def test_quarantined_label_is_scheduled_as_singleton(self) -> None:
        order = ["a", "b", "hard", "c", "d"]
        self.assertEqual(_next_phase1_group(order, 0, 5, {"hard"}), ["a", "b"])
        self.assertEqual(_next_phase1_group(order, 2, 5, {"hard"}), ["hard"])

    def test_error_shape_ignores_locations_and_metavariable_ids(self) -> None:
        first = "A.lean:12:8: error: type mismatch\n  ?m.193"
        second = "B.lean:99:3: error: type mismatch\n  ?m_774"
        self.assertEqual(_lean_error_shape(first), _lean_error_shape(second))

    def test_single_declaration_gets_only_one_targeted_patch_per_tier(self) -> None:
        # A second failure moves to a fresh escalation tier instead of paying
        # for another declaration patch in the anchored producer session.
        self.assertEqual(TARGETED_DECL_PATCH_ROUNDS, 1)

    def test_failed_statement_correction_gets_one_bounded_compile_retry(self) -> None:
        target = node("lem:target")
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"lem:target": target},
            base_timeout=30,
            base_effort="medium",
            escalation_effort="high",
            hard_timeout=60,
            telemetry=telemetry,
            lean_command=["lean"],
        )
        parsed = _parse_module("theorem lem_target : True := by sorry\n")
        replacement = _parse_module("theorem lem_target : True := by sorry\n")
        finding = SkeletonFinding(
            "Lean rejected this declaration: type mismatch",
            label="lem:target",
            lean_name="lem_target",
        )

        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Candidate.lean"
            with (
                patch(
                    "formalize_blueprint._lean_compile_findings",
                    return_value=[finding],
                ),
                patch(
                    "formalize_blueprint._targeted_patch_skeleton_decls",
                    return_value=(replacement, "patched"),
                ) as targeted,
                patch("formalize_blueprint._skeleton_code_findings", return_value=[]),
                patch(
                    "formalize_blueprint._skeleton_deterministic_findings",
                    return_value=[],
                ),
                patch("formalize_blueprint._check_lean", return_value=(True, "")),
            ):
                corrected, _code, _note = _retry_statement_patch_compile_once(
                    ctx,
                    ["lem:target"],
                    ["lem:target"],
                    [],
                    [],
                    parsed,
                    "theorem lem_target : True := by sorry\n",
                    "type mismatch",
                    path,
                    sessions={},
                )

        self.assertIsNotNone(corrected)
        self.assertEqual(targeted.call_count, 1)
        self.assertEqual(targeted.call_args.kwargs["timeout"], 30)
        self.assertFalse(targeted.call_args.kwargs["escalated"])
        self.assertFalse(targeted.call_args.kwargs["escalate_timeout"])

    def test_statement_replacement_drops_colliding_model_helpers(self) -> None:
        original = _parse_module(
            """import Mathlib

def existing_helper : Nat := 1
theorem lem_target : True := by sorry
"""
        )
        replacement = """import Mathlib

def existing_helper : Nat := 2
def genuinely_new_helper : Nat := 3
theorem lem_target : True := by trivial
"""

        patched = _apply_skeleton_replacements(
            original, ["lem:target"], ["lem:target"], replacement
        )

        self.assertIsNotNone(patched)
        assert patched is not None
        names = [decl.name for decl in patched.decls]
        self.assertEqual(names.count("existing_helper"), 1)
        self.assertEqual(names.count("lem_target"), 1)
        self.assertIn("genuinely_new_helper", names)
        existing = next(decl.text for decl in patched.decls if decl.name == "existing_helper")
        self.assertIn(":= 2", existing)

    def test_corollary_is_parsed_and_normalized_without_duplicate_fallback(self) -> None:
        nodes = {"cor:result": node("cor:result")}
        parsed = _parse_module(
            "corollary cor_result (n : Nat) : n = n := by sorry\n"
        )
        normalized = _normalize_theorem_like_keywords(
            parsed, nodes, ["cor:result"]
        )
        self.assertEqual(len(normalized.decls), 1)
        self.assertEqual(normalized.decls[0].kind, "theorem")
        self.assertTrue(normalized.decls[0].text.startswith("theorem cor_result"))

    def test_model_module_boundary_owns_structure_and_flattens_namespace(self) -> None:
        nodes = {
            "def:base": node("def:base"),
            "lem:root": node("lem:root", uses={"def:base"}),
        }
        ctx = SimpleNamespace(nodes=nodes)
        canonical = _canonicalize_model_lean(
            ctx,
            nodes,
            """import Mathlib

set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace PaperOutput

def local_helper : Nat := 1
def def_base : Nat := local_helper
theorem lem_root : def_base = 1 := by sorry

end PaperOutput
""",
        )
        parsed = canonical.parsed
        helper_name = parsed.decls[0].name or ""
        self.assertTrue(helper_name.startswith("_autobp_"))
        self.assertEqual(
            [decl.name for decl in parsed.decls],
            [helper_name, "def_base", "lem_root"],
        )
        self.assertIn(f"def def_base : Nat := {helper_name}", parsed.decls[1].text)
        self.assertEqual(parsed.preamble, ["noncomputable section", "open scoped BigOperators"])
        self.assertFalse(any("namespace" in line or line.startswith("end") for line in parsed.preamble))
        self.assertEqual(canonical.owner_by_index[0], "def:base")
        self.assertEqual(canonical.owner_by_index[1], "def:base")
        self.assertEqual(canonical.owner_by_index[2], "lem:root")

    def test_independent_candidates_namespace_same_local_helper_differently(self) -> None:
        nodes = {
            "lem:a": node("lem:a"),
            "lem:b": node("lem:b"),
        }
        ctx = SimpleNamespace(name="paper", nodes=nodes)
        first = _canonicalize_model_lean(
            ctx,
            ["lem:a"],
            "def ceilLog (n : Nat) : Nat := n\n"
            "theorem lem_a : ceilLog 1 = 1 := by sorry\n",
        ).parsed
        second = _canonicalize_model_lean(
            ctx,
            ["lem:b"],
            "def ceilLog (n : Nat) : Nat := n\n"
            "theorem lem_b : ceilLog 2 = 2 := by sorry\n",
        ).parsed

        first_helper = first.decls[0].name or ""
        second_helper = second.decls[0].name or ""
        self.assertNotEqual(first_helper, second_helper)
        self.assertTrue(first_helper.startswith("_autobp_"))
        self.assertTrue(second_helper.startswith("_autobp_"))
        self.assertIn(first_helper, first.decls[1].text)
        self.assertIn(second_helper, second.decls[1].text)
        self.assertNotIn(" ceilLog ", first.decls[1].text)
        self.assertNotIn(" ceilLog ", second.decls[1].text)

    def test_planned_helper_uses_contract_name_without_model_retry(self) -> None:
        label = "def:polytope"
        ctx = SimpleNamespace(
            name="simplex",
            nodes={
                label: node(label),
                "def:consumer": node("def:consumer", uses={label}),
            },
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "helpers": [
                        {
                            "name": "Polytope",
                            "kind": "structure",
                            "required_members": [
                                "carrier",
                                "points",
                                "finite_points",
                                "eq_convexHull",
                            ],
                        }
                    ],
                }
            },
        )
        canonical = _canonicalize_model_lean(
            ctx,
            [label],
            """namespace def_polytope
structure Polytope where
  carrier : Set Nat
  points : List Nat
  finite_points : True
  eq_convexHull : True
end def_polytope

def def_polytope (n : Nat) : Type := sorry
""",
        )
        helper_name = canonical.parsed.decls[0].name or ""
        self.assertRegex(helper_name, r"^_autobp_[0-9a-f]{12}_Polytope$")
        self.assertNotIn("def_polytope_Polytope", helper_name)
        code = "\n\n".join(decl.text for decl in canonical.parsed.decls)
        self.assertEqual(
            _skeleton_deterministic_findings(code, ctx, [label]), []
        )
        downstream = _canonicalize_model_lean(
            ctx,
            ["def:consumer"],
            "def def_consumer (P : def_polytope.Polytope) : Type := sorry\n",
        ).parsed
        self.assertIn(helper_name, downstream.decls[0].text)
        self.assertNotIn("def_polytope.Polytope", downstream.decls[0].text)

    def test_phase1_accepts_transparent_alias_to_owned_structural_contract(self) -> None:
        label = "def:finite-subdivision"
        target = _lean_name(label)
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "helpers": [
                        {
                            "name": "FiniteSubdivisionInterface",
                            "kind": "structure",
                            "members": [
                                {"name": "cells", "type": "Finset Nat"},
                            ],
                            "required_members": ["cells"],
                        }
                    ],
                }
            },
        )
        owners = _planned_helper_owner_by_name(ctx, [label])
        helper = next(iter(owners))
        code = (
            f"structure {helper} (n : Nat) where\n"
            "  cells : Finset Nat\n\n"
            f"def {target} (n : Nat) : Type := {helper} n\n"
        )

        findings = _skeleton_code_findings(
            code,
            {target: "definition"},
            {target: label},
            owners,
        )

        self.assertEqual(findings, [])

    def test_phase1_still_rejects_arbitrary_completed_definition_body(self) -> None:
        label = "def:value"
        target = _lean_name(label)
        findings = _skeleton_code_findings(
            f"def {target} : Nat := 7\n",
            {target: "definition"},
            {target: label},
            {},
        )
        self.assertTrue(
            any("implementation belongs in Phase 2" in item.message for item in findings)
        )

    def test_planned_helper_ownership_overrides_adjacency_during_slicing(self) -> None:
        labels = ["def:relu-network", "def:tab"]
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label) for label in labels},
            design_plan_entries={
                "def:relu-network": {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "helpers": [],
                },
                "def:tab": {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "helpers": [
                        {
                            "name": "TabData",
                            "kind": "structure",
                            "required_members": [
                                "pair_terms",
                                "tail_terms",
                                "max_over_terms",
                            ],
                        }
                    ],
                },
            },
        )
        canonical = _canonicalize_model_lean(
            ctx,
            labels,
            """structure TabData where
  pair_terms : List Nat
  tail_terms : List Nat
  max_over_terms : Nat

def def_relu_network : Type := sorry
def def_tab : Type := sorry
""",
        )
        helper_name = canonical.parsed.decls[0].name or ""
        self.assertEqual(canonical.owner_by_index[0], "def:tab")
        owners = _planned_helper_owner_by_name(ctx, labels)
        target_names = {_lean_name(label) for label in labels}
        tab = _delivered_decl_texts(
            canonical.parsed, ["def:tab"], target_names, owners
        )
        relu = _delivered_decl_texts(
            canonical.parsed, ["def:relu-network"], target_names, owners
        )
        self.assertIsNotNone(tab)
        self.assertIsNotNone(relu)
        self.assertTrue(any(helper_name in text for text in tab or []))
        self.assertFalse(any(helper_name in text for text in relu or []))

    def test_shared_helper_keeps_consuming_targets_in_one_component(self) -> None:
        labels = ["lem:a", "lem:b"]
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label) for label in labels},
            telemetry=FakeTelemetry(),
        )
        parsed = _canonicalize_model_lean(
            ctx,
            labels,
            "def sharedValue : Nat := 1\n"
            "theorem lem_a : sharedValue = 1 := by sorry\n"
            "theorem lem_b : sharedValue = 1 := by sorry\n",
        ).parsed

        components = _target_components_from_helpers(
            parsed, {_lean_name(label): label for label in labels}
        )
        self.assertEqual(components, [set(labels)])
        self.assertIsNone(
            _delivered_decl_texts(
                parsed, ["lem:a"], {_lean_name(label) for label in labels}
            )
        )
        together = _delivered_decl_texts(
            parsed, labels, {_lean_name(label) for label in labels}
        )
        self.assertIsNotNone(together)
        self.assertFalse(
            any(
                re.search(r"\bsharedValue\b", text)
                for text in together or []
            )
        )
        helper_name = parsed.decls[0].name or ""
        self.assertEqual(sum(helper_name in text for text in together or []), 3)

    def test_statement_cannot_reference_generated_sibling_outside_blueprint_graph(self) -> None:
        labels = ["def:a", "def:b"]
        nodes = {label: node(label) for label in labels}
        ctx = SimpleNamespace(nodes=nodes)
        code = "def def_a : Nat := def_b\n\ndef def_b : Nat := 1\n"

        findings = _skeleton_deterministic_findings(code, ctx, labels)

        self.assertTrue(
            any(
                finding.label == "def:a"
                and "outside its blueprint dependency closure" in finding.message
                for finding in findings
            )
        )

    def test_model_module_boundary_rejects_duplicate_declarations(self) -> None:
        ctx = SimpleNamespace(nodes={"lem:root": node("lem:root")})
        with self.assertRaisesRegex(ValueError, "repeats declaration"):
            _canonicalize_model_lean(
                ctx,
                ["lem:root"],
                "theorem lem_root : True := by sorry\n"
                "theorem lem_root : True := by sorry\n",
            )

    def test_model_module_boundary_rejects_unbalanced_or_stateful_preamble(self) -> None:
        ctx = SimpleNamespace(nodes={"lem:root": node("lem:root")})
        with self.assertRaisesRegex(ValueError, "unclosed model module wrapper"):
            _canonicalize_model_lean(
                ctx,
                ["lem:root"],
                "namespace Output\ntheorem lem_root : True := by sorry\n",
            )
        with self.assertRaisesRegex(ValueError, "unsupported module-level"):
            _canonicalize_model_lean(
                ctx,
                ["lem:root"],
                "variable (n : Nat)\ntheorem lem_root : True := by sorry\n",
            )

    def test_invalid_local_helper_is_owned_by_adjacent_target(self) -> None:
        code = (
            "def polytopeUnionIsPolytope : Prop := True\n"
            "theorem lem_root : polytopeUnionIsPolytope := by sorry\n"
        )
        findings = _skeleton_code_findings(
            code,
            {"lem_root": "lemma"},
            {"lem_root": "lem:root"},
        )
        helper = next(
            finding
            for finding in findings
            if finding.lean_name == "polytopeUnionIsPolytope"
        )
        self.assertEqual(helper.label, "lem:root")
        self.assertIn("unplanned helper", helper.message)

    def test_phase1_allows_only_explicit_plan_owned_type_helpers(self) -> None:
        code = (
            "class OwnedInterface : Prop where\n"
            "  witness : True\n"
            "theorem lem_root : OwnedInterface := by sorry\n"
        )
        findings = _skeleton_code_findings(
            code,
            {"lem_root": "lemma"},
            {"lem_root": "lem:root"},
            {"OwnedInterface": "lem:root"},
        )
        self.assertEqual(findings, [])

    def test_phase1_rejects_complete_unplanned_executable_helper(self) -> None:
        findings = _skeleton_code_findings(
            "def ceilLog (n : Nat) : Nat := n\n"
            "theorem lem_root (n : Nat) : ceilLog n = n := by sorry\n",
            {"lem_root": "lemma"},
            {"lem_root": "lem:root"},
        )
        self.assertTrue(
            any(
                finding.lean_name == "ceilLog"
                and "unplanned helper" in finding.message
                for finding in findings
            )
        )

    def test_model_invented_helper_does_not_revise_closed_plan(self) -> None:
        label = "lem:root"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            workers=1,
            telemetry=telemetry,
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "statement-v1",
                    "target_signature": "theorem lem_root : True",
                    "helpers": [],
                    "decisions": [],
                }
            },
            generation_candidates={},
            retry_lifecycle={},
            quarantined_labels=set(),
        )
        request = RepairRequest(
            "Phase 1 emitted unplanned helper `ceilLog`",
            [label],
            authorizes_blueprint_repair=False,
            plan_revision_required=False,
        )
        with patch(
            "formalize_blueprint._generate_uncompiled_phase1_candidate",
            side_effect=request,
        ), patch(
            "formalize_blueprint._correct_phase1_design_plan",
            return_value=True,
        ) as correction:
            with self.assertRaises(RepairRequest):
                _run_validated_contract_phase1_layer(
                    ctx, 0, [[label]], [], _SectionNumberAllocator(1)
                )

        correction.assert_not_called()
        self.assertFalse(
            any(
                event == "phase1_outline_plan_closure_correction"
                for event, _fields in telemetry.events
            )
        )

    def test_only_contract_closure_findings_require_plan_revision(self) -> None:
        self.assertFalse(
            _findings_require_plan_revision(
                [SkeletonFinding("invented helper", category="unplanned_phase1_helper")]
            )
        )
        self.assertTrue(
            _findings_require_plan_revision(
                [SkeletonFinding("invalid plan", category="plan_contract_closure")]
            )
        )

    def test_semantic_correction_routes_plan_contract_conflict_to_plan_revision(self) -> None:
        label = "def:network"
        parsed = _parse_module("def def_network : Nat := sorry")
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=parsed,
            import_modules=[],
            generation_tier="base",
            sessions={},
        )
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={},
            base_timeout=120,
            hard_timeout=300,
            telemetry=FakeTelemetry(),
        )
        plan_finding = SkeletonFinding(
            "the accepted plan omits a required provider member",
            label=label,
            lean_name="def_network",
            category="plan_contract_closure",
        )

        with patch(
            "formalize_blueprint._targeted_patch_skeleton_decls",
            return_value=(parsed, "patched"),
        ), patch(
            "formalize_blueprint._skeleton_code_findings",
            return_value=[plan_finding],
        ), patch(
            "formalize_blueprint._skeleton_deterministic_findings",
            return_value=[],
        ):
            with self.assertRaises(RepairRequest) as raised:
                _revise_semantic_candidates(
                    ctx,
                    [candidate],
                    {label},
                    "the statement audit requires the missing member",
                    [],
                )

        self.assertTrue(raised.exception.plan_revision_required)
        self.assertFalse(raised.exception.authorizes_blueprint_repair)

    def test_plan_revision_retry_does_not_shrink_or_quarantine_generation(self) -> None:
        label = "def:relu-function"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            telemetry=telemetry,
            section_size=12,
            effective_section_size=12,
            section_clean_streak=1,
            stmt_fps={label: "statement-v1"},
            quarantined_labels=set(),
            quarantine={},
        )
        request = RepairRequest(
            "invalid contract plan",
            [label],
            failure_route=_route_lean_generation_failure(
                [label, "def:other"]
            ),
            plan_revision_required=True,
            authorizes_blueprint_repair=False,
        )

        _apply_phase1_retry_scheduling(ctx, request)

        self.assertEqual(ctx.effective_section_size, 12)
        self.assertEqual(ctx.section_clean_streak, 1)
        self.assertFalse(ctx.quarantined_labels)
        self.assertFalse(ctx.quarantine)
        self.assertIn(
            (
                "phase1_plan_revision_retry_scheduled",
                {
                    "labels": [label],
                    "scheduler_size": 12,
                    "scheduler_unchanged": True,
                },
            ),
            telemetry.events,
        )

    def test_phase1_allows_typed_definition_body_to_be_deferred(self) -> None:
        findings = _skeleton_code_findings(
            "def def_object (n : Nat) : Nat := by sorry\n",
            {"def_object": "definition"},
            {"def_object": "def:object"},
        )
        self.assertEqual(findings, [])

    def test_phase1_rejects_eager_definition_implementation(self) -> None:
        findings = _skeleton_code_findings(
            "def def_object (n : Nat) : Nat := n + 1\n",
            {"def_object": "definition"},
            {"def_object": "def:object"},
        )
        self.assertTrue(
            any("implementation belongs in Phase 2" in finding.message for finding in findings)
        )

    def test_phase1_still_rejects_sorry_in_local_helper(self) -> None:
        findings = _skeleton_code_findings(
            "def local_helper : Nat := by sorry\n"
            "def def_object : Nat := by sorry\n",
            {"def_object": "definition"},
            {"def_object": "def:object"},
        )
        self.assertTrue(
            any(finding.lean_name == "local_helper" for finding in findings)
        )

    def test_phase2_definition_body_requires_semantic_audit(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            name="paper",
            nodes={"def:object": node("def:object")},
            telemetry=telemetry,
            lean_command=["lean"],
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text("def def_object : Nat := sorry\n", encoding="utf-8")
            section = Section(1, ["def:object"], path, "Generated.Skeleton01", [])
            with patch("formalize_blueprint._check_lean", return_value=(True, "")), patch(
                "formalize_blueprint._model_alignment_audit",
                return_value=(
                    "blueprint",
                    "definition body does not realize the blueprint definition",
                    {"def:object"},
                    [],
                ),
            ) as audit:
                implemented, errors, repairs = _apply_proof_batch(
                    ctx,
                    section,
                    "def def_object : Nat := by exact 1",
                    {"def:object": "def def_object : Nat := sorry"},
                    tag="test",
                )

            audit.assert_called_once()
            self.assertEqual(implemented, [])
            self.assertEqual(repairs, {"def:object": []})
            self.assertIn("does not realize", errors["def:object"])
            self.assertIn(":= sorry", path.read_text(encoding="utf-8"))
            self.assertTrue(
                any(event == "definition_body_audit_result" for event, _ in telemetry.events)
            )

    def test_replacing_target_replaces_its_owned_helper_bundle(self) -> None:
        original = _parse_module(
            "def broken_local_helper : Prop := True\n"
            "theorem lem_target : broken_local_helper := by sorry\n"
        )
        replacement = (
            "def valid_local_helper : Prop := (1 = 1)\n"
            "theorem lem_target : valid_local_helper := by sorry\n"
        )
        patched = _apply_skeleton_replacements(
            original, ["lem:target"], ["lem:target"], replacement
        )
        self.assertIsNotNone(patched)
        assert patched is not None
        names = [decl.name for decl in patched.decls]
        self.assertNotIn("broken_local_helper", names)
        self.assertEqual(names, ["valid_local_helper", "lem_target"])

    def test_replacing_target_uses_plan_ownership_when_body_is_sorry(self) -> None:
        original = _parse_module(
            "class PlannedInterface : Prop where\n"
            "  old_field : True\n"
            "theorem lem_target : True := by sorry\n"
        )
        replacement = (
            "class PlannedInterface : Prop where\n"
            "  required_field : True\n"
            "theorem lem_target : True := by sorry\n"
        )
        patched = _apply_skeleton_replacements(
            original,
            ["lem:target"],
            ["lem:target"],
            replacement,
            {"PlannedInterface": "lem:target"},
        )
        self.assertIsNotNone(patched)
        assert patched is not None
        helpers = [decl for decl in patched.decls if decl.name == "PlannedInterface"]
        self.assertEqual(len(helpers), 1)
        self.assertIn("required_field", helpers[0].text)
        self.assertNotIn("old_field", helpers[0].text)

    def test_target_only_replacement_preserves_plan_owned_helper(self) -> None:
        original = _parse_module(
            "class PlannedInterface : Prop where\n"
            "  required_field : True\n"
            "theorem lem_target : PlannedInterface -> True := by sorry\n"
        )
        replacement = (
            "theorem lem_target (h : PlannedInterface) : True := by sorry\n"
        )

        patched = _apply_skeleton_replacements(
            original,
            ["lem:target"],
            ["lem:target"],
            replacement,
            {"PlannedInterface": "lem:target"},
        )

        self.assertIsNotNone(patched)
        assert patched is not None
        names = [decl.name for decl in patched.decls]
        self.assertEqual(names, ["PlannedInterface", "lem_target"])
        helper = next(
            decl.text for decl in patched.decls if decl.name == "PlannedInterface"
        )
        self.assertIn("required_field", helper)

    def test_explicit_helper_finding_requires_helper_replacement(self) -> None:
        original = _parse_module(
            "class PlannedInterface : Prop where\n"
            "  old_field : True\n"
            "theorem lem_target : True := by sorry\n"
        )
        replacement = "theorem lem_target : True := by sorry\n"

        patched = _apply_skeleton_replacements(
            original,
            ["lem:target"],
            ["lem:target"],
            replacement,
            {"PlannedInterface": "lem:target"},
            {"PlannedInterface"},
        )

        self.assertIsNone(patched)

    def test_phase1_normalizes_existing_corollary_before_replacement(self) -> None:
        target = node("cor:result")
        ctx = SimpleNamespace(
            base_timeout=30,
            hard_timeout=60,
            base_effort="medium",
            escalation_effort="high",
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
            nodes={"cor:result": target},
        )
        sec = Section(
            number=1,
            labels=["cor:result"],
            path=Path("Skeleton01.lean"),
            module="AutoBlueprint.Generated.Paper.Skeleton01",
            import_modules=[],
            refined_labels=set(),
        )
        parsed = _parse_module(
            "corollary cor_result : True := by sorry\n"
        )
        response = CallResult(
            status="ok",
            text="```lean\ncorollary cor_result : True := by sorry\n```",
        )
        with (
            patch("formalize_blueprint._bulk_skeleton_prompt", return_value="prompt"),
            patch("formalize_blueprint._call_model", return_value=response),
        ):
            result = _generate_phase1_statement_group(
                ctx, sec, ["cor:result"], [sec], [], parsed
            )
        declaration = next(decl for decl in result.decls if decl.name == "cor_result")
        self.assertEqual(declaration.kind, "theorem")
        self.assertTrue(declaration.text.startswith("theorem cor_result"))

    def test_compile_error_is_owned_by_lower_provisional_declaration(self) -> None:
        parsed = _parse_module(
            "theorem lem_root : True := by sorry\n\n"
            "theorem lem_lower : MissingType := by sorry\n"
        )
        _code, ranges = __import__("formalize_blueprint")._compose_module(
            [], [], [decl.text for decl in parsed.decls]
        )
        output = (
            f"Attempt.lean:{ranges[1][0]}:20: error: "
            "Unknown identifier `MissingType`"
        )
        findings = _lean_compile_findings(
            parsed, ["lem:root", "lem:lower"], ranges, output, "Attempt.lean"
        )
        self.assertEqual(findings[0].label, "lem:lower")
        self.assertNotEqual(findings[0].label, "lem:root")

    def test_phase1_repairs_lower_scaffolding_then_freezes_only_root(self) -> None:
        nodes = {
            "lem:lower": node("lem:lower"),
            "lem:root": node("lem:root", uses={"lem:lower"}),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            lean_command=["lean"],
            base_timeout=30,
            hard_timeout=60,
            telemetry=FakeTelemetry(),
        )
        initial = (
            "theorem lem_lower : MissingType := by sorry\n\n"
            "theorem lem_root : True := by sorry\n"
        )
        exact_root = _parse_module(
            "theorem lem_lower : MissingType := by sorry\n\n"
            "theorem lem_root : lem_lower := by sorry\n"
        )
        repaired = _parse_module(
            "theorem lem_lower : Prop := by sorry\n\n"
            "theorem lem_root : lem_lower := by sorry\n"
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(initial, encoding="utf-8")
            sec = Section(
                number=1,
                labels=["lem:lower", "lem:root"],
                path=path,
                module="AutoBlueprint.Generated.Paper.Skeleton01",
                import_modules=[],
                refined_labels=set(),
                provisional_environment=True,
            )
            error = (
                f"{path.name}:6:20: error: Unknown identifier `MissingType`"
            )
            with (
                patch(
                    "formalize_blueprint._generate_phase1_statement_group",
                    return_value=exact_root,
                ),
                patch("formalize_blueprint._skeleton_code_findings", return_value=[]),
                patch("formalize_blueprint._skeleton_deterministic_findings", return_value=[]),
                patch(
                    "formalize_blueprint._check_lean",
                    side_effect=[(False, error), (True, "")],
                ),
                patch(
                    "formalize_blueprint._targeted_patch_skeleton_decls",
                    return_value=(repaired, "patched"),
                ) as targeted,
                patch("formalize_blueprint._model_alignment_audit", return_value=None),
                patch(
                    "formalize_blueprint._compile_module_olean",
                    return_value=SimpleNamespace(ok=True, output=""),
                ),
                patch("formalize_blueprint._note_frozen_section"),
                patch("formalize_blueprint._record"),
                patch("formalize_blueprint.SCRATCH_DIR", Path(tmp) / "scratch"),
            ):
                _refine_statement_group(ctx, sec, ["lem:root"], [sec])

            self.assertEqual(sec.refined_labels, {"lem:root"})
            self.assertNotIn("lem:lower", sec.refined_labels)
            self.assertTrue(targeted.call_args.kwargs["provisional_only"])
            finding_labels = {
                finding.label for finding in targeted.call_args.args[6]
            }
            self.assertEqual(finding_labels, {"lem:lower"})

    def test_failed_phase1_candidate_does_not_overwrite_canonical_skeleton(self) -> None:
        target = node("lem:target")
        ctx = SimpleNamespace(
            name="paper",
            nodes={"lem:target": target},
            lean_command=["lean"],
            base_timeout=30,
            hard_timeout=60,
        )
        original = "theorem lem_target : True := by sorry\n"
        candidate = _parse_module("theorem lem_target : False := by sorry\n")

        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(original, encoding="utf-8")
            sec = Section(
                number=1,
                labels=["lem:target"],
                path=path,
                module="AutoBlueprint.Generated.Paper.Skeleton01",
                import_modules=[],
                refined_labels=set(),
            )
            with (
                patch(
                    "formalize_blueprint._generate_phase1_statement_group",
                    return_value=candidate,
                ),
                patch("formalize_blueprint._skeleton_code_findings", return_value=[]),
                patch("formalize_blueprint._skeleton_deterministic_findings", return_value=[]),
                patch("formalize_blueprint._check_lean", return_value=(False, "type mismatch")),
                patch(
                    "formalize_blueprint._targeted_patch_skeleton_decls",
                    return_value=(None, "not patchable"),
                ),
                patch("formalize_blueprint.SCRATCH_DIR", Path(tmp) / "scratch"),
            ):
                with self.assertRaises(RepairRequest):
                    _refine_statement_group(ctx, sec, ["lem:target"], [sec])

            self.assertEqual(path.read_text(encoding="utf-8"), original)

    def test_failed_phase1_candidate_heals_legacy_self_import_and_duplicates(self) -> None:
        target = node("lem:target")
        ctx = SimpleNamespace(
            name="paper",
            nodes={"lem:target": target},
            lean_command=["lean"],
            base_timeout=30,
            hard_timeout=60,
        )
        corrupted = """import AutoBlueprint.Generated.Paper.Skeleton01

def helper : Nat := 1
def helper : Nat := 2
theorem lem_target : True := by sorry
"""
        candidate = _parse_module("theorem lem_target : False := by sorry\n")

        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(corrupted, encoding="utf-8")
            sec = Section(
                number=1,
                labels=["lem:target"],
                path=path,
                module="AutoBlueprint.Generated.Paper.Skeleton01",
                import_modules=[],
                refined_labels=set(),
            )
            with (
                patch(
                    "formalize_blueprint._generate_phase1_statement_group",
                    return_value=candidate,
                ),
                patch("formalize_blueprint._skeleton_code_findings", return_value=[]),
                patch("formalize_blueprint._skeleton_deterministic_findings", return_value=[]),
                patch("formalize_blueprint._check_lean", return_value=(False, "type mismatch")),
                patch(
                    "formalize_blueprint._targeted_patch_skeleton_decls",
                    return_value=(None, "not patchable"),
                ),
                patch("formalize_blueprint.SCRATCH_DIR", Path(tmp) / "scratch"),
            ):
                with self.assertRaises(RepairRequest):
                    _refine_statement_group(ctx, sec, ["lem:target"], [sec])

            # A failed candidate is not committed. The legacy file remains on
            # disk until a candidate passes; its healed baseline is reserved
            # for rollback after an object-compilation failure.
            self.assertEqual(path.read_text(encoding="utf-8"), corrupted)

    def test_phase1_removes_self_import_using_parsed_import_format(self) -> None:
        target = node("lem:target")
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            base_timeout=30,
            hard_timeout=60,
            base_effort="medium",
            escalation_effort="high",
            unavailable_imports=set(),
            telemetry=telemetry,
            nodes={"lem:target": target},
        )
        sec = Section(
            number=1,
            labels=["lem:target"],
            path=Path("Skeleton01.lean"),
            module="AutoBlueprint.Generated.Paper.Skeleton01",
            import_modules=[],
            refined_labels=set(),
        )
        parsed = _parse_module("theorem lem_target : True := by sorry\n")
        response = CallResult(
            status="ok",
            text="""```lean
import AutoBlueprint.Generated.Paper.Skeleton01
theorem lem_target : True := by sorry
```""",
        )

        with (
            patch("formalize_blueprint._bulk_skeleton_prompt", return_value="prompt"),
            patch("formalize_blueprint._skeleton_prompt", return_value="retry"),
            patch("formalize_blueprint._call_model", return_value=response) as call,
        ):
            result = _generate_phase1_statement_group(
                ctx, sec, ["lem:target"], [sec], [], parsed
            )

        self.assertEqual(call.call_count, 1)
        self.assertNotIn(
            "import AutoBlueprint.Generated.Paper.Skeleton01", result.imports
        )
        self.assertTrue(
            any(event == "phase1_self_import_removed" for event, _ in telemetry.events)
        )

    def test_initial_declaration_timeout_never_uses_escalation_runner(self) -> None:
        telemetry = FakeTelemetry()
        target = node("lem:target")
        ctx = SimpleNamespace(
            name="paper",
            nodes={"lem:target": target},
            stmt_blocks={"lem:target": r"\begin{lemma} True \end{lemma}"},
            unavailable_imports=set(),
            base_timeout=30,
            hard_timeout=90,
            base_effort="medium",
            escalation_effort="high",
            runner_spec="codex:base",
            escalation_runner_spec="codex:expensive",
            lean_command=["lean"],
            telemetry=telemetry,
            library_context="",
            library_candidates=[],
            paper_text="",
        )
        calls: list[dict] = []

        def timed_out(*_args, **kwargs):
            calls.append(kwargs)
            return CallResult(status="timeout", error="timed out")

        with tempfile.TemporaryDirectory() as tmp, patch(
            "formalize_blueprint._section_module",
            return_value=("AutoBlueprint.Generated.Paper.Skeleton01", Path(tmp) / "Skeleton01.lean"),
        ), patch("formalize_blueprint._call_model", side_effect=timed_out):
            with self.assertRaises(RepairRequest):
                _freeze_section(
                    ctx,
                    ["lem:target"],
                    [],
                    _SectionNumberAllocator(1),
                    initial_only=True,
                )

        self.assertEqual(len(calls), 1)
        self.assertFalse(calls[0]["escalated"])
        self.assertEqual(calls[0]["effort"], "medium")
        self.assertEqual(calls[0]["timeout"], 30)

    def test_initial_pass_generates_one_complete_environment(self) -> None:
        telemetry = FakeTelemetry()
        nodes = {
            "def:base": node("def:base"),
            "lem:root": node("lem:root", uses={"def:base"}),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_blocks={
                "def:base": r"\begin{definition}A natural number.\end{definition}",
                "lem:root": r"\begin{lemma}\uses{def:base}The value equals itself.\end{lemma}",
            },
            unavailable_imports=set(),
            base_timeout=30,
            base_effort="medium",
            runner_spec="codex:base",
            escalation_runner_spec="codex:expensive",
            lean_command=["lean"],
            telemetry=telemetry,
            library_context="",
            library_candidates=[],
            paper_text="",
        )
        calls: list[dict] = []
        code = """```lean
namespace ModelOutput
def def_base : Nat := by sorry
theorem lem_root : def_base = def_base := by sorry
end ModelOutput
```"""

        def complete(*_args, **kwargs):
            calls.append(kwargs)
            return CallResult(status="ok", text=code)

        with tempfile.TemporaryDirectory() as tmp, patch(
            "formalize_blueprint._section_module",
            return_value=("AutoBlueprint.Generated.Paper.Skeleton01", Path(tmp) / "Skeleton01.lean"),
        ), patch("formalize_blueprint._call_model", side_effect=complete), patch(
            "formalize_blueprint._check_lean"
        ) as check_lean, patch(
            "formalize_blueprint._compile_module_olean"
        ) as compile_olean, patch(
            "formalize_blueprint._save_ctx_state"
        ):
            result = _run_initial_declaration_pass(ctx, [], set(nodes))
            generated = result[0].path.read_text(encoding="utf-8")

        self.assertEqual(len(calls), 1)
        check_lean.assert_not_called()
        compile_olean.assert_not_called()
        self.assertEqual(calls[0]["labels"], ["def:base", "lem:root"])
        self.assertFalse(calls[0]["escalated"])
        self.assertEqual(len(result), 1)
        self.assertEqual(result[0].labels, ["def:base", "lem:root"])
        self.assertNotIn("namespace ModelOutput", generated)
        self.assertNotIn("end ModelOutput", generated)

    def test_initial_pass_fills_model_omissions_without_retrying(self) -> None:
        telemetry = FakeTelemetry()
        nodes = {
            "def:base": node("def:base"),
            "lem:root": node("lem:root", uses={"def:base"}),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_blocks={label: "" for label in nodes},
            unavailable_imports=set(),
            base_timeout=30,
            base_effort="medium",
            telemetry=telemetry,
            library_context="",
            library_candidates=[],
            paper_text="",
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            with patch(
                "formalize_blueprint._section_module",
                return_value=("AutoBlueprint.Generated.Paper.Skeleton01", path),
            ), patch(
                "formalize_blueprint._call_model",
                return_value=CallResult(
                    status="ok", text="```lean\ndef def_base : Nat := 0\n```"
                ),
            ) as call_model, patch(
                "formalize_blueprint._check_lean"
            ) as check_lean, patch(
                "formalize_blueprint._compile_module_olean"
            ) as compile_olean, patch("formalize_blueprint._save_ctx_state"):
                result = _run_initial_declaration_pass(ctx, [], set(nodes))
                generated = path.read_text(encoding="utf-8")

        call_model.assert_called_once()
        check_lean.assert_not_called()
        compile_olean.assert_not_called()
        self.assertIn("def def_base : Nat := 0", generated)
        self.assertIn("theorem lem_root : True := by trivial", generated)
        self.assertEqual(result[0].refined_labels, set())
        event, fields = telemetry.events[-1]
        self.assertEqual(event, "initial_declaration_environment")
        self.assertEqual(fields["fallback_labels"], ["lem:root"])

    def test_phase1_repair_keeps_boilerplate_and_adds_new_names_locally(self) -> None:
        telemetry = FakeTelemetry()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "def def_base : Nat := 0\n\n"
                "theorem lem_root : def_base = def_base := by sorry\n",
                encoding="utf-8",
            )
            sec = Section(
                1,
                ["def:base", "lem:root"],
                path,
                "AutoBlueprint.Generated.Paper.Skeleton01",
                [],
                refined_labels={"def:base", "lem:root"},
                provisional_environment=True,
            )
            nodes = {
                "def:base": node("def:base"),
                "lem:new-helper": node("lem:new-helper", uses={"def:base"}),
                "lem:root": node(
                    "lem:root", uses={"def:base", "lem:new-helper"}
                ),
            }
            ctx = SimpleNamespace(
                name="paper",
                nodes=nodes,
                lean_command=["lean"],
                telemetry=telemetry,
                stmt_fps={label: label for label in nodes},
                contract_fps={label: label for label in nodes},
                quarantined_labels=set(),
                quarantine={},
                effective_section_size=1,
            )
            with patch("formalize_blueprint._save_ctx_state"), patch(
                "formalize_blueprint._check_lean"
            ) as check_lean, patch(
                "formalize_blueprint._compile_module_olean"
            ) as compile_olean:
                kept, invalidated = _invalidate_after_repair(
                    ctx,
                    [sec],
                    {"lem:root", "lem:new-helper"},
                    ["lean"],
                )
                result = _add_phase1_boilerplate_names(
                    ctx, kept, {"lem:new-helper"}
                )

            check_lean.assert_not_called()
            compile_olean.assert_not_called()
            self.assertEqual(len(result), 1)
            self.assertTrue(result[0].provisional_environment)
            self.assertIn("def:base", result[0].refined_labels)
            self.assertNotIn("lem:root", result[0].refined_labels)
            self.assertIn("lem:new-helper", result[0].labels)
            self.assertIn("lem:new-helper", invalidated)
            generated = path.read_text(encoding="utf-8")
            self.assertIn("theorem lem_new_helper : True := by trivial", generated)

    def test_phase1_generates_statements_before_auditing_boilerplate(self) -> None:
        telemetry = FakeTelemetry()
        nodes = {
            "def:claim": node("def:claim"),
            "lem:root": node("lem:root", uses={"def:claim"}),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_blocks={label: "" for label in nodes},
            tex_blocks={label: "" for label in nodes},
            unavailable_imports=set(),
            base_timeout=30,
            hard_timeout=60,
            base_effort="medium",
            escalation_effort="high",
            runner_spec="codex:base",
            escalation_runner_spec="codex:expensive",
            telemetry=telemetry,
            library_context="",
            library_candidates=[],
            paper_text="",
            design_plan="",
        )
        parsed = SimpleNamespace(
            imports=[],
            preamble=["noncomputable section"],
            decls=[],
        )
        # Use the real parser-shaped object while retaining intentionally weak
        # stage-zero declarations.
        from formalize_blueprint import _parse_module
        parsed = _parse_module(
            "noncomputable section\n\n"
            "def def_claim : Unit := ()\n\n"
            "theorem lem_root : True := by trivial\n"
        )
        sec = Section(
            1,
            list(nodes),
            Path("Skeleton01.lean"),
            "AutoBlueprint.Generated.Paper.Skeleton01",
            [],
            refined_labels=set(),
            provisional_environment=True,
        )
        exact = CallResult(
            status="ok",
            text=(
                "```lean\n"
                "theorem lem_root : def_claim = def_claim := by sorry\n"
                "```"
            ),
        )
        with patch(
            "formalize_blueprint._call_model", return_value=exact
        ) as call_model:
            replaced = _generate_phase1_statement_group(
                ctx, sec, ["lem:root"], [sec], [], parsed
            )

        call_model.assert_called_once()
        self.assertEqual(
            call_model.call_args.kwargs["purpose"],
            "phase1_statement_generation",
        )
        root = next(decl for decl in replaced.decls if decl.name == "lem_root")
        self.assertIn("def_claim = def_claim", root.text)
        self.assertNotIn(": True", root.text)

    def test_noncomputable_section_is_valid_provisional_preamble(self) -> None:
        findings = _skeleton_code_findings(
            "noncomputable section\nopen scoped BigOperators\n\n"
            "theorem lem_root : True := by sorry\n",
            {"lem_root": "lemma"},
            {"lem_root": "lem:root"},
        )
        self.assertFalse(
            any("unexpected non-`open` preamble" in item.message for item in findings)
        )

    def test_repair_scope_uses_union_of_old_and_new_graphs(self) -> None:
        before = {
            "target": node("target", uses={"old-helper"}),
            "old-helper": node("old-helper"),
            "unrelated": node("unrelated"),
        }
        after = {
            "target": node("target", uses={"new-helper"}),
            "new-helper": node("new-helper"),
            "unrelated": node("unrelated"),
        }
        distances = _repair_graph_distances(
            before, after, ["target"], {"old-helper", "new-helper", "unrelated"}
        )
        self.assertEqual(distances["old-helper"], 1)
        self.assertEqual(distances["new-helper"], 1)
        self.assertIsNone(distances["unrelated"])

    def test_phase1_repair_scope_allows_helpers_but_not_consumers(self) -> None:
        before = {
            "target": node("target", uses={"old-helper"}),
            "old-helper": node("old-helper"),
            "consumer": node("consumer", uses={"target"}),
        }
        after = {
            "target": node("target", uses={"new-helper"}),
            "new-helper": node("new-helper"),
            "consumer": node("consumer", uses={"target"}),
        }
        violations = _phase1_repair_scope_violations(
            before,
            after,
            ["target"],
            {"target", "old-helper", "new-helper", "consumer"},
        )
        self.assertEqual(violations, {"consumer"})

    def test_phase1_repair_scope_allows_new_helpers_that_use_target(self) -> None:
        before = {
            "target": node("target"),
            "consumer": node("consumer", uses={"target"}),
        }
        after = {
            "target": node("target"),
            "new-helper": node("new-helper", uses={"target"}),
            "new-helper-2": node("new-helper-2", uses={"new-helper"}),
            "consumer": node("consumer", uses={"target"}),
        }
        violations = _phase1_repair_scope_violations(
            before,
            after,
            ["target"],
            {"target", "new-helper", "new-helper-2", "consumer"},
        )
        self.assertEqual(violations, {"consumer"})

    def test_phase1_repair_scope_rejects_unconnected_new_nodes(self) -> None:
        before = {
            "target": node("target", uses={"old-dependency"}),
            "old-dependency": node("old-dependency"),
        }
        after = {
            "target": node("target", uses={"old-dependency"}),
            "old-dependency": node("old-dependency"),
            "new-helper": node("new-helper", uses={"target"}),
            "unrelated": node("unrelated", uses={"old-dependency"}),
        }
        violations = _phase1_repair_scope_violations(
            before,
            after,
            ["target"],
            {"new-helper", "unrelated"},
        )
        self.assertEqual(violations, {"unrelated"})

    def test_unchanged_descendant_is_recompiled_instead_of_regenerated(self) -> None:
        telemetry = FakeTelemetry()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            old_a = root / "Skeleton01.lean"
            cached_b = root / "Skeleton02.lean"
            new_a = root / "Skeleton03.lean"
            old_a.write_text("def a : Nat := 1\n", encoding="utf-8")
            cached_b.write_text(
                "import AutoBlueprint.Generated.Paper.Skeleton01\n\n"
                "def b : Nat := a\n",
                encoding="utf-8",
            )
            new_a.write_text("def a : Nat := 2\n", encoding="utf-8")
            sec_a = Section(
                1, ["a"], old_a,
                "AutoBlueprint.Generated.Paper.Skeleton01", [],
            )
            sec_b = Section(
                2, ["b"], cached_b,
                "AutoBlueprint.Generated.Paper.Skeleton02",
                ["AutoBlueprint.Generated.Paper.Skeleton01"],
            )
            ctx = SimpleNamespace(
                name="paper",
                nodes={"a": node("a"), "b": node("b", uses={"a"})},
                lean_command=["lean"],
                telemetry=telemetry,
            )
            kept, invalidated = _invalidate_after_repair(
                ctx, [sec_a, sec_b], {"a"}, ["lean"]
            )
            self.assertEqual(invalidated, {"a", "b"})
            self.assertEqual([sec.labels for sec in kept], [["b"]])
            self.assertTrue(kept[0].deferred)

            replacement = Section(
                3, ["a"], new_a,
                "AutoBlueprint.Generated.Paper.Skeleton03", [],
            )
            with patch("formalize_blueprint._check_lean", return_value=(True, "")), patch(
                "formalize_blueprint._compile_module_olean",
                return_value=SimpleNamespace(ok=True),
            ):
                sections, reactivated, dropped = _reactivate_deferred_sections(
                    ctx, [kept[0], replacement], drop_unready=True
                )
            self.assertEqual(reactivated, {"b"})
            self.assertFalse(dropped)
            restored_b = next(sec for sec in sections if sec.labels == ["b"])
            self.assertFalse(restored_b.deferred)
            self.assertIn(
                "import AutoBlueprint.Generated.Paper.Skeleton03",
                cached_b.read_text(encoding="utf-8"),
            )

    def test_invalidation_removes_lake_build_object(self) -> None:
        telemetry = FakeTelemetry()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "Skeleton28.lean"
            local_object = source.with_suffix(".olean")
            lake_object = root / "lake" / "Skeleton28.olean"
            lake_object.parent.mkdir()
            source.write_text("def def_old : Nat := 0\n", encoding="utf-8")
            local_object.write_bytes(b"old")
            lake_object.write_bytes(b"old")
            section = Section(
                28,
                ["def:old"],
                source,
                "AutoBlueprint.Generated.Paper.Skeleton28",
                [],
            )
            ctx = SimpleNamespace(
                name="paper",
                nodes={"def:old": node("def:old")},
                telemetry=telemetry,
            )
            with patch(
                "formalize_blueprint._lake_olean_path", return_value=lake_object
            ):
                kept, invalidated = _invalidate_after_repair(
                    ctx, [section], {"def:old"}, ["lean"]
                )
            self.assertFalse(kept)
            self.assertEqual(invalidated, {"def:old"})
            self.assertFalse(source.exists())
            self.assertFalse(local_object.exists())
            self.assertFalse(lake_object.exists())

    def test_resume_pruning_removes_orphaned_lake_object(self) -> None:
        telemetry = FakeTelemetry()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            generated = root / "generated"
            lake_generated = root / "lake-generated"
            generated.mkdir()
            lake_generated.mkdir()
            orphan = lake_generated / "Skeleton28.olean"
            orphan.write_bytes(b"stale")
            ctx = SimpleNamespace(name="paper", telemetry=telemetry)
            with patch(
                "formalize_blueprint._generated_module_dir", return_value=generated
            ), patch(
                "formalize_blueprint._generated_lake_module_dir",
                return_value=lake_generated,
            ):
                _prune_stale_generated(ctx, [])
            self.assertFalse(orphan.exists())
            self.assertTrue(
                any(event == "stale_artifacts_pruned" for event, _ in telemetry.events)
            )

    def test_blueprint_draft_continue_and_fresh_are_transactional(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            canonical = root / "canonical"
            draft = root / "draft"
            canonical_content = canonical / "blueprint" / "src" / "content.tex"
            canonical_content.parent.mkdir(parents=True)
            canonical_content.write_text("canonical\n", encoding="utf-8")
            with patch(
                "formalize_blueprint._canonical_blueprint_dir",
                return_value=canonical,
            ), patch(
                "formalize_blueprint._draft_blueprint_dir", return_value=draft
            ), patch(
                "formalize_blueprint.REPO_ROOT", root
            ):
                first = _prepare_blueprint_draft("paper", continue_run=False)
                draft_content = first / "blueprint" / "src" / "content.tex"
                draft_content.write_text("repaired draft\n", encoding="utf-8")
                resumed = _prepare_blueprint_draft("paper", continue_run=True)
                self.assertEqual(
                    (resumed / "blueprint" / "src" / "content.tex").read_text(),
                    "repaired draft\n",
                )
                fresh = _prepare_blueprint_draft("paper", continue_run=False)
                self.assertEqual(
                    (fresh / "blueprint" / "src" / "content.tex").read_text(),
                    "canonical\n",
                )
            self.assertEqual(canonical_content.read_text(), "canonical\n")

    def test_successful_promotion_atomically_updates_canonical_content(self) -> None:
        telemetry = FakeTelemetry()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            canonical = root / "canonical"
            draft = root / "draft"
            canonical_content = canonical / "blueprint" / "src" / "content.tex"
            draft_content = draft / "blueprint" / "src" / "content.tex"
            canonical_content.parent.mkdir(parents=True)
            draft_content.parent.mkdir(parents=True)
            canonical_content.write_text("canonical\n", encoding="utf-8")
            draft_content.write_text("verified draft\n", encoding="utf-8")
            ctx = SimpleNamespace(
                name="paper",
                blueprint_dir=draft,
                content_path=draft_content,
                telemetry=telemetry,
            )
            with patch(
                "formalize_blueprint._canonical_blueprint_dir",
                return_value=canonical,
            ), patch("formalize_blueprint.REPO_ROOT", root):
                published = _promote_blueprint_draft(ctx)
            self.assertEqual(published, canonical_content)
            self.assertEqual(canonical_content.read_text(), "verified draft\n")
            self.assertTrue(
                any(event == "blueprint_draft_promoted" for event, _ in telemetry.events)
            )

    def test_validator_reads_explicit_blueprint_draft(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            draft = root / "draft"
            src = draft / "blueprint" / "src"
            src.mkdir(parents=True)
            (src / "web.tex").write_text("", encoding="utf-8")
            (src / "content.tex").write_text(
                "\\begin{lemma}Draft claim\\label{lem:draft}\\end{lemma}\n",
                encoding="utf-8",
            )
            result = validate_blueprint(root, "paper", blueprint_dir=draft)
            self.assertTrue(result.ok, result.errors)
            self.assertEqual(set(result.nodes), {"lem:draft"})

    def test_validator_preserves_statement_and_proof_dependency_scopes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            draft = root / "draft"
            src = draft / "blueprint" / "src"
            src.mkdir(parents=True)
            (src / "web.tex").write_text("", encoding="utf-8")
            (src / "content.tex").write_text(
                "\\begin{definition}A\\label{def:a}\\end{definition}\n"
                "\\begin{definition}B\\label{def:b}\\end{definition}\n"
                "\\begin{lemma}Claim\\label{lem:claim}\\uses{def:a}"
                "\\end{lemma}\n"
                "\\begin{proof}Proof\\uses{def:b}\\end{proof}\n",
                encoding="utf-8",
            )
            result = validate_blueprint(root, "paper", blueprint_dir=draft)
            self.assertTrue(result.ok, result.errors)
            claim = result.nodes["lem:claim"]
            self.assertEqual(claim.statement_uses, {"def:a"})
            self.assertEqual(claim.proof_uses, {"def:b"})
            self.assertEqual(claim.uses, {"def:a", "def:b"})

    def test_directly_changed_section_keeps_only_compiling_prefix(self) -> None:
        telemetry = FakeTelemetry()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "def prefix : Nat := 1\n\n"
                "def changed : Nat := prefix\n\n"
                "def suffix : Nat := changed\n",
                encoding="utf-8",
            )
            section = Section(
                1,
                ["prefix", "changed", "suffix"],
                path,
                "AutoBlueprint.Generated.Paper.Skeleton01",
                [],
            )
            ctx = SimpleNamespace(
                name="paper",
                nodes={
                    "prefix": node("prefix"),
                    "changed": node("changed", uses={"prefix"}),
                    "suffix": node("suffix", uses={"changed"}),
                },
                telemetry=telemetry,
            )
            with patch("formalize_blueprint._check_lean", return_value=(True, "")), patch(
                "formalize_blueprint._compile_module_olean",
                return_value=SimpleNamespace(ok=True),
            ):
                kept, invalidated = _invalidate_after_repair(
                    ctx, [section], {"changed"}, ["lean"]
                )
            self.assertEqual(invalidated, {"changed", "suffix"})
            self.assertEqual(kept[0].labels, ["prefix"])
            self.assertFalse(kept[0].deferred)
            code = path.read_text(encoding="utf-8")
            self.assertIn("def prefix", code)
            self.assertNotIn("def changed", code)
            self.assertNotIn("def suffix", code)

    def test_scheduler_and_deferred_state_are_persisted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean = root / "Skeleton04.lean"
            state = root / "state.json"
            lean.write_text("def cached : Nat := 1\n", encoding="utf-8")
            section = Section(
                4,
                ["cached"],
                lean,
                "AutoBlueprint.Generated.Paper.Skeleton04",
                [],
                deferred=True,
                refined_labels=set(),
            )
            with patch("formalize_blueprint._state_path", return_value=state):
                _save_state(
                    "paper",
                    [section],
                    {"cached": "statement", "hard": "hard-v1"},
                    {"cached": "contract"},
                    quarantined_labels={"hard"},
                    generation_feedback={
                        "hard": {
                            "statement_fp": "hard-v1",
                            "evidence": "audit rejected the declaration",
                            "source": "deterministic_audit",
                        }
                    },
                    generation_candidates={
                        "hard": {
                            "statement_fp": "hard-v1",
                            "code": "theorem hard : True := sorry",
                            "source": "statement_alignment",
                            "required_dependencies": ["dependency"],
                            "working_candidate": {
                                "code": "theorem hard : True := by sorry",
                                "candidate_hash": "working-hash",
                                "source": "validated_contract_compiler_check",
                                "lean_status": "failed",
                                "lean_output": "error: unresolved identifier",
                                "lean_error_count": 1,
                            },
                        }
                    },
                    retry_lifecycle={
                        "phase1_statement:hard": {
                            "label": "hard",
                            "stage": "phase1_statement",
                            "statement_fp": "hard-v1",
                            "state": "escalation",
                            "last_tier": "base",
                            "failures": 1,
                            "source": "statement_alignment",
                            "evidence_sha256": "abc",
                        }
                    },
                    design_plan_entries={
                        "hard": {
                            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                            "statement_fp": "hard-v1",
                            "target_signature": "hard : True",
                            "helpers": [],
                            "decisions": ["exact contract"],
                            "semantic_revision_count": 1,
                            "closure_fp": "closed-plan-v1",
                        }
                    },
                    design_plan_alternates={
                        "hard": {
                            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                            "statement_fp": "hard-v1",
                            "target_signature": "hard : False",
                            "helpers": [],
                            "decisions": ["alternate contract"],
                        }
                    },
                    effective_section_size=6,
                    refinement_order="top-down",
                )
            payload = json.loads(state.read_text(encoding="utf-8"))
            self.assertEqual(payload["version"], 16)
            self.assertEqual(payload["refinement_order"], "top-down")
            self.assertEqual(
                payload["scheduler"]["quarantine"],
                {
                    "hard": {
                        "statement_fp": "hard-v1",
                        "failure_class": "unspecified",
                    }
                },
            )
            self.assertEqual(payload["scheduler"]["effective_section_size"], 6)
            self.assertEqual(
                payload["scheduler"]["generation_feedback"]["hard"]["evidence"],
                "audit rejected the declaration",
            )
            self.assertEqual(
                payload["scheduler"]["generation_candidates"]["hard"]["code"],
                "theorem hard : True := sorry",
            )
            self.assertEqual(
                payload["scheduler"]["generation_candidates"]["hard"]
                ["required_dependencies"],
                ["dependency"],
            )
            self.assertEqual(
                payload["scheduler"]["generation_candidates"]["hard"]
                ["working_candidate"]["code"],
                "theorem hard : True := by sorry",
            )
            self.assertEqual(
                payload["scheduler"]["retry_lifecycle"][
                    "phase1_statement:hard"
                ]["state"],
                "escalation",
            )
            self.assertEqual(
                payload["scheduler"]["design_plan_entries"]["hard"]["target_signature"],
                "hard : True",
            )
            self.assertEqual(
                payload["scheduler"]["design_plan_entries"]["hard"]["closure_fp"],
                "closed-plan-v1",
            )
            self.assertEqual(
                payload["scheduler"]["design_plan_entries"]["hard"]
                ["semantic_revision_count"],
                1,
            )
            self.assertEqual(
                payload["scheduler"]["design_plan_alternates"]["hard"]
                ["target_signature"],
                "hard : False",
            )
            self.assertTrue(payload["sections"][0]["deferred"])
            self.assertEqual(payload["sections"][0]["refined_labels"], [])

            ctx = SimpleNamespace(
                name="paper",
                nodes={"cached": node("cached"), "hard": node("hard")},
                stmt_fps={"cached": "statement", "hard": "hard-v1"},
                contract_fps={"cached": "contract"},
                quarantined_labels=set(),
                quarantine={},
                generation_feedback={},
                generation_candidates={},
                retry_lifecycle={},
                design_plan="",
                design_plan_entries={},
                design_plan_alternates={},
                effective_section_size=0,
                section_size=12,
                refinement_order="top-down",
            )
            with patch("formalize_blueprint._state_path", return_value=state), patch(
                "formalize_blueprint._generated_module_dir", return_value=root
            ), patch("formalize_blueprint._compile_module_olean") as compile_mock:
                loaded = _load_state(ctx, ["lean"])
            self.assertEqual(len(loaded), 1)
            self.assertTrue(loaded[0].deferred)
            self.assertEqual(loaded[0].refined_labels, set())
            self.assertEqual(ctx.quarantined_labels, {"hard"})
            self.assertEqual(
                ctx.quarantine["hard"]["failure_class"], "unspecified"
            )
            self.assertEqual(ctx.effective_section_size, 6)
            self.assertEqual(
                ctx.generation_feedback["hard"]["evidence"],
                "audit rejected the declaration",
            )
            self.assertEqual(
                ctx.generation_candidates["hard"]["code"],
                "theorem hard : True := sorry",
            )
            self.assertEqual(
                ctx.generation_candidates["hard"]["required_dependencies"],
                ["dependency"],
            )
            self.assertEqual(
                ctx.generation_candidates["hard"]["working_candidate"]["code"],
                "theorem hard : True := by sorry",
            )
            self.assertEqual(
                ctx.retry_lifecycle["phase1_statement:hard"]["state"],
                "escalation",
            )
            self.assertEqual(
                ctx.design_plan_entries["hard"]["target_signature"],
                "hard : True",
            )
            self.assertEqual(
                ctx.design_plan_entries["hard"]["closure_fp"],
                "closed-plan-v1",
            )
            self.assertEqual(
                ctx.design_plan_entries["hard"]["semantic_revision_count"],
                1,
            )
            self.assertEqual(
                ctx.design_plan_alternates["hard"]["target_signature"],
                "hard : False",
            )
            compile_mock.assert_not_called()

    def test_legacy_label_only_quarantine_is_not_reused(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state = Path(tmp) / "state.json"
            state.write_text(
                json.dumps(
                    {
                        "version": 2,
                        "sections": [],
                        "scheduler": {
                            "quarantined_labels": ["hard"],
                            "effective_section_size": 6,
                        },
                    }
                ),
                encoding="utf-8",
            )
            telemetry = FakeTelemetry()
            ctx = SimpleNamespace(
                name="paper",
                nodes={"hard": node("hard")},
                stmt_fps={"hard": "hard-v2"},
                contract_fps={"hard": "hard-contract"},
                quarantined_labels=set(),
                quarantine={},
                effective_section_size=0,
                section_size=12,
                telemetry=telemetry,
                refinement_order="top-down",
            )
            with patch("formalize_blueprint._state_path", return_value=state), patch(
                "formalize_blueprint._generated_module_dir", return_value=Path(tmp)
            ):
                loaded = _load_state(ctx, ["lean"])
            self.assertFalse(loaded)
            self.assertFalse(ctx.quarantined_labels)
            self.assertFalse(ctx.quarantine)
            self.assertEqual(
                telemetry.events[-1][1]["reason"],
                "legacy_state_missing_statement_fingerprint",
            )

    def test_resume_state_is_not_reused_across_traversal_modes(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            state = Path(tmp) / "state.json"
            state.write_text(
                json.dumps(
                    {
                        "version": 6,
                        "refinement_order": "top-down",
                        "sections": [],
                        "scheduler": {},
                    }
                ),
                encoding="utf-8",
            )
            telemetry = FakeTelemetry()
            ctx = SimpleNamespace(
                name="paper",
                nodes={},
                stmt_fps={},
                contract_fps={},
                quarantined_labels=set(),
                quarantine={},
                effective_section_size=0,
                section_size=12,
                telemetry=telemetry,
                refinement_order="bottom-up",
            )
            with patch("formalize_blueprint._state_path", return_value=state):
                self.assertEqual(_load_state(ctx, ["lean"]), [])
            self.assertEqual(
                telemetry.events[-1],
                (
                    "resume_state_rejected",
                    {
                        "reason": "refinement_order_changed",
                        "saved_order": "top-down",
                        "requested_order": "bottom-up",
                    },
                ),
            )

    def test_compile_failure_fingerprint_ignores_ansi_color(self) -> None:
        plain = _lean_failure_fingerprint("theorem x : False := by", "error: failed")
        colored = _lean_failure_fingerprint(
            "theorem x : False := by", "\x1b[31merror: failed\x1b[0m"
        )
        self.assertEqual(plain, colored)

    def test_partial_frozen_sections_survive_later_repair(self) -> None:
        first = Section(
            number=1,
            labels=["easy"],
            path=Path("Skeleton01.lean"),
            module="Generated.Skeleton01",
            import_modules=[],
        )
        calls = 0

        def fake_freeze(*_args, **_kwargs):
            nonlocal calls
            calls += 1
            if calls == 1:
                return [first]
            raise RepairRequest("hard node needs repair", ["hard"])

        with patch("formalize_blueprint._freeze_section", side_effect=fake_freeze), patch(
            "formalize_blueprint._save_ctx_state"
        ):
            with self.assertRaises(RepairRequest) as caught:
                _freeze_parts(SimpleNamespace(), [["easy"], ["hard"]], [], 1)
        self.assertEqual(caught.exception.frozen_sections, [first])

    def test_provisional_declarations_are_reserved_but_not_frozen_or_proved(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "def def_leaf : Nat := 1\n\n"
                "theorem thm_root : def_leaf = 1 := by sorry\n",
                encoding="utf-8",
            )
            section = Section(
                1,
                ["def:leaf", "thm:root"],
                path,
                "Generated.Skeleton01",
                [],
                refined_labels=set(),
            )
            self.assertEqual(_reserved_labels([section]), {"def:leaf", "thm:root"})
            self.assertEqual(_frozen_labels([section]), set())
            self.assertEqual(_proved_labels([section]), set())

            section.refined_labels.add("def:leaf")
            self.assertEqual(_frozen_labels([section]), {"def:leaf"})
            self.assertEqual(_proved_labels([section]), {"def:leaf"})

    def test_phase2_progress_excludes_interface_only_phase1_contracts(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "structure def_interface where\n"
                "  value : Nat\n\n"
                "theorem thm_pending : True := by sorry\n\n"
                "def def_done : Nat := 1\n",
                encoding="utf-8",
            )
            labels = ["def:interface", "thm:pending", "def:done"]
            section = Section(
                1,
                labels,
                path,
                "Generated.Skeleton01",
                [],
                refined_labels=set(labels),
            )
            ctx = SimpleNamespace(nodes={label: node(label) for label in labels})

            implemented, required = _phase2_body_progress(ctx, [section])

            self.assertEqual(required, {"thm:pending", "def:done"})
            self.assertEqual(implemented, {"def:done"})

    def test_statement_layers_walk_from_public_roots_to_dependencies(self) -> None:
        nodes = {
            "def:leaf": node("def:leaf"),
            "lem:middle": node("lem:middle", uses={"def:leaf"}),
            "thm:root": node("thm:root", uses={"lem:middle"}),
            "def:disconnected": node("def:disconnected"),
        }
        self.assertEqual(
            _top_down_statement_layers(nodes),
            [
                ["def:disconnected", "thm:root"],
                ["lem:middle"],
                ["def:leaf"],
            ],
        )

    def test_bottom_up_layers_walk_from_dependencies_to_public_roots(self) -> None:
        nodes = {
            "def:leaf": node("def:leaf"),
            "lem:middle": node("lem:middle", uses={"def:leaf"}),
            "thm:root": node("thm:root", uses={"lem:middle"}),
            "def:disconnected": node("def:disconnected"),
        }
        self.assertEqual(
            _bottom_up_statement_layers(nodes),
            [
                ["def:disconnected", "def:leaf"],
                ["lem:middle"],
                ["thm:root"],
            ],
        )
        self.assertEqual(
            _bottom_up_proof_layers(nodes),
            [["lem:middle"], ["thm:root"]],
        )
        self.assertEqual(
            _next_implementation_frontier(
                nodes,
                {"def:leaf", "lem:middle", "thm:root"},
                "bottom-up",
            ),
            (0, ["def:leaf"], ["def:disconnected", "def:leaf"]),
        )

    def test_pipeline_uses_fixed_phase_orders(self) -> None:
        nodes = {
            "def:leaf": node("def:leaf"),
            "lem:middle": node("lem:middle", uses={"def:leaf"}),
            "thm:root": node("thm:root", uses={"lem:middle"}),
        }

        self.assertEqual(PHASE1_STATEMENT_ORDER, "bottom-up")
        self.assertEqual(PHASE2_PROOF_ORDER, "top-down")
        self.assertEqual(
            _next_implementation_frontier(
                nodes,
                set(nodes),
                PHASE2_PROOF_ORDER,
            ),
            (0, ["thm:root"], ["thm:root"]),
        )

    def test_webui_does_not_emit_a_configurable_proof_order(self) -> None:
        command = build_webui_command(
            "refine",
            {
                "name": "simplex",
                "fast": True,
                "runner_backend": "codex",
                "runner_model": "gpt-5.5",
                "escalation_runner_backend": "codex",
                "escalation_runner_model": "gpt-5.5",
                "workers": "3",
                "section_size": "12",
                "timeout": "300",
                "hard_timeout": "600",
                "max_trials": "100",
                "continue_run": True,
                "proof_order": "top-down",
            },
        )

        self.assertNotIn("--proof-order", command)

    def test_bottom_up_ready_frontier_does_not_wait_for_unrelated_leaf(self) -> None:
        nodes = {
            "def:slow": node("def:slow"),
            "def:fast": node("def:fast"),
            "lem:fast-child": node("lem:fast-child", uses={"def:fast"}),
            "thm:slow-child": node("thm:slow-child", uses={"def:slow"}),
        }

        self.assertEqual(
            _bottom_up_ready_frontier(
                nodes,
                {"def:slow", "lem:fast-child", "thm:slow-child"},
                {"def:fast"},
            ),
            ["def:slow", "lem:fast-child"],
        )

    def test_only_top_down_requires_initial_declarations(self) -> None:
        self.assertTrue(_requires_initial_declaration_pass("top-down"))
        self.assertFalse(_requires_initial_declaration_pass("bottom-up"))

    def test_phase1_design_plan_is_shared_and_repairs_replan_only_changed_nodes(self) -> None:
        nodes = {
            "def:leaf": node("def:leaf"),
            "lem:middle": node("lem:middle", uses={"def:leaf"}),
            "thm:root": node("thm:root", uses={"lem:middle"}),
            "def:disconnected": node("def:disconnected"),
        }
        ctx = SimpleNamespace(
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan="",
            design_plan_entries={},
            telemetry=FakeTelemetry(),
            base_timeout=120,
            base_effort="medium",
        )
        first = CallResult(
            status="ok",
            text=json.dumps({"contracts": [
                {"label": "thm:root", "target_signature": "theorem thm_root (n : Nat) : lem_middle n", "helpers": [], "decisions": ["public result"]},
                {"label": "lem:middle", "target_signature": "theorem lem_middle (n : Nat) : def_leaf = def_leaf", "helpers": [], "decisions": ["bridge"]},
                {"label": "def:leaf", "target_signature": "def def_leaf : Nat", "helpers": [], "decisions": ["base object"]},
                {"label": "def:disconnected", "target_signature": "def def_disconnected : Bool", "helpers": [], "decisions": ["separate object"]},
            ]}),
        )
        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._design_plan_prompt", return_value="plan prompt"
        ), patch(
            "formalize_blueprint._audit_phase1_design_plan", return_value=None
        ), patch(
            "formalize_blueprint._call_model", return_value=first
        ) as call_model:
            _ensure_phase1_design_plan(ctx, set(nodes), [])

        self.assertEqual(set(ctx.design_plan_entries), set(nodes))
        self.assertEqual(call_model.call_count, 2)
        local_plan = _design_plan_block(ctx, ["def:leaf"])
        self.assertIn("def def_leaf : Nat", local_plan)
        self.assertIn("lem_middle (n : Nat) : def_leaf", local_plan)
        self.assertNotIn("def def_disconnected : Bool", local_plan)

        original_leaf = dict(ctx.design_plan_entries["def:leaf"])
        ctx.stmt_fps["lem:middle"] = "lem:middle-v2"
        revised = CallResult(
            status="ok",
            text=json.dumps({"contracts": [{
                "label": "lem:middle",
                "target_signature": "theorem lem_middle : def_leaf = def_leaf",
                "helpers": [],
                "decisions": ["revised bridge"],
            }]}),
        )
        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._design_plan_prompt", return_value="repair prompt"
        ), patch(
            "formalize_blueprint._audit_phase1_design_plan", return_value=None
        ), patch(
            "formalize_blueprint._call_model", return_value=revised
        ) as call_model:
            _ensure_phase1_design_plan(ctx, set(nodes), [])

        self.assertEqual(call_model.call_args.kwargs["labels"], ["lem:middle"])
        self.assertEqual(ctx.design_plan_entries["def:leaf"], original_leaf)
        self.assertEqual(
            ctx.design_plan_entries["lem:middle"]["statement_fp"],
            "lem:middle-v2",
        )

    def test_design_plan_prompt_has_no_generation_output_mode(self) -> None:
        label = "def:leaf"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            stmt_blocks={label: "Define the exact leaf object."},
            unavailable_imports=set(),
            library_candidates=[],
            library_context="",
        )

        prompt = _design_plan_prompt(
            ctx,
            [label],
            [],
            [],
            timeout_s=120,
        )

        self.assertIn("Return JSON only", prompt)
        self.assertNotIn("NEEDS-DECOMPOSITION", prompt)
        self.assertNotIn("return the Lean code block", prompt)

    def test_design_plan_candidates_merge_only_complete_closure_components(self) -> None:
        provider = "def:network"
        consumer = "lem:representable"
        unrelated = "def:scalar"
        nodes = {
            provider: node(provider),
            consumer: node(consumer, uses={provider}),
            unrelated: node(unrelated),
        }
        ctx = SimpleNamespace(
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan="",
            design_plan_entries={},
        )
        plan_a = {
            provider: {
                "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                "statement_fp": f"{provider}-v1",
                "target_signature": "structure def_network where\n  realizes : Prop",
                "helpers": [],
                "decisions": [],
            },
            consumer: {
                "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                "statement_fp": f"{consumer}-v1",
                "target_signature": "theorem lem_representable : def_network.Representable",
                "helpers": [],
                "decisions": [],
            },
            unrelated: {
                "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                "statement_fp": f"{unrelated}-v1",
                "target_signature": "def def_scalar : Nat",
                "helpers": [],
                "decisions": [],
            },
        }
        plan_b = copy.deepcopy(plan_a)
        plan_b[provider]["target_signature"] = (
            "structure def_network where\n  Representable : Prop"
        )
        plan_b[unrelated]["target_signature"] = (
            "def def_scalar : Nat\ndef extra_scalar : Nat"
        )
        ordered = [consumer, provider, unrelated]
        candidate_a = _evaluate_design_plan_candidate(ctx, ordered, plan_a, "A")
        candidate_b = _evaluate_design_plan_candidate(ctx, ordered, plan_b, "B")

        self.assertLess(candidate_b.score, candidate_a.score)
        merged, components = _merge_design_plan_candidates(
            ctx, ordered, candidate_b, candidate_a
        )

        self.assertTrue(merged.closed)
        self.assertEqual(merged.entries[provider], plan_b[provider])
        self.assertEqual(merged.entries[unrelated], plan_a[unrelated])
        self.assertEqual(components, [[unrelated]])

    def test_rejected_closed_contract_tries_retained_alternate_without_model(self) -> None:
        label = "def:leaf"
        selected = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": "def:leaf-v1",
            "target_signature": "def def_leaf : Nat",
            "helpers": [],
            "decisions": ["selected"],
        }
        alternate = {
            **selected,
            "target_signature": "def def_leaf : Int",
            "decisions": ["alternate"],
        }
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "def:leaf-v1"},
            design_plan="",
            design_plan_entries={label: selected},
            design_plan_alternates={label: alternate},
            telemetry=FakeTelemetry(),
        )

        with patch("formalize_blueprint._call_model") as call_model:
            changed = _correct_phase1_design_plan(
                ctx, [label], "statement audit rejected the selected contract"
            )

        self.assertTrue(changed)
        call_model.assert_not_called()
        self.assertIn("Int", ctx.design_plan_entries[label]["target_signature"])
        self.assertNotIn(label, ctx.design_plan_alternates)

    def test_empty_design_plan_retries_once_with_completeness_feedback(self) -> None:
        label = "def:leaf"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "def:leaf-v1"},
            design_plan="",
            design_plan_entries={},
            telemetry=FakeTelemetry(),
            base_timeout=120,
            base_effort="medium",
        )
        empty = CallResult(status="ok", text='{"contracts":[]}')
        valid = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "contracts": [
                        {
                            "label": label,
                            "target_signature": "def def_leaf : Nat",
                            "helpers": [],
                            "decisions": ["exact leaf object"],
                        }
                    ]
                }
            ),
        )

        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._design_plan_prompt", return_value="plan prompt"
        ) as prompt, patch(
            "formalize_blueprint._call_model", side_effect=[empty, valid]
        ) as call_model:
            _ensure_phase1_design_plan(ctx, {label}, [])

        self.assertEqual(call_model.call_count, 2)
        self.assertIn(
            "zero usable contracts",
            prompt.call_args_list[1].kwargs["feedback"],
        )
        self.assertIn(label, ctx.design_plan_entries)
        statuses = [
            fields["status"]
            for event, fields in ctx.telemetry.events
            if event == "phase1_design_plan_result"
        ]
        self.assertEqual(statuses, ["invalid_empty_contracts", "ok"])

    def test_design_plan_closure_is_corrected_before_statement_generation(self) -> None:
        provider = "def:network"
        consumer = "lem:representable"
        nodes = {
            provider: node(provider),
            consumer: node(consumer, uses={provider}),
        }
        ctx = SimpleNamespace(
            name="test",
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan="",
            design_plan_entries={},
            telemetry=FakeTelemetry(),
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
        )
        planned = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "contracts": [
                        {
                            "label": provider,
                            "target_signature": (
                                "structure def_network where\n  realizes : Prop"
                            ),
                            "helpers": [],
                            "decisions": [],
                        },
                        {
                            "label": consumer,
                            "target_signature": (
                                "theorem lem_representable : "
                                "def_network.Representable"
                            ),
                            "helpers": [],
                            "decisions": [],
                        },
                    ]
                }
            ),
        )

        def correct(
            _ctx, labels, evidence, *, escalated=False, try_alternate=True
        ):
            self.assertEqual(set(labels), {provider, consumer})
            self.assertFalse(escalated)
            self.assertFalse(try_alternate)
            self.assertIn("def_network.Representable", evidence)
            self.assertIn("Provider contract(s) implicated", evidence)
            _ctx.design_plan_entries[consumer]["target_signature"] = (
                "theorem lem_representable : def_network.realizes"
            )
            return True

        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._design_plan_prompt", return_value="plan prompt"
        ), patch(
            "formalize_blueprint._call_model", return_value=planned
        ), patch(
            "formalize_blueprint._correct_phase1_design_plan",
            side_effect=correct,
        ) as correction:
            _ensure_phase1_design_plan(ctx, set(nodes), [])

        correction.assert_called_once()
        self.assertIn("closure_fp", ctx.design_plan_entries[provider])
        self.assertIn("closure_fp", ctx.design_plan_entries[consumer])

    def test_unclosed_plan_gets_one_correction_then_invalidates_component(self) -> None:
        provider = "def:network"
        consumer = "lem:representable"
        nodes = {
            provider: node(provider),
            consumer: node(consumer, uses={provider}),
        }
        ctx = SimpleNamespace(
            name="test",
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan="",
            design_plan_entries={},
            telemetry=FakeTelemetry(),
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
        )
        planned = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "contracts": [
                        {
                            "label": provider,
                            "target_signature": (
                                "structure def_network where\n  realizes : Prop"
                            ),
                            "helpers": [],
                            "decisions": [],
                        },
                        {
                            "label": consumer,
                            "target_signature": (
                                "theorem lem_representable : "
                                "def_network.Representable"
                            ),
                            "helpers": [],
                            "decisions": [],
                        },
                    ]
                }
            ),
        )
        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._design_plan_prompt", return_value="plan prompt"
        ), patch(
            "formalize_blueprint._call_model", return_value=planned
        ), patch(
            "formalize_blueprint._correct_phase1_design_plan",
            return_value=False,
        ) as correction:
            with self.assertRaises(RepairRequest):
                _ensure_phase1_design_plan(ctx, set(nodes), [])

        self.assertEqual(
            [call.kwargs["escalated"] for call in correction.call_args_list],
            [False],
        )
        self.assertNotIn(provider, ctx.design_plan_entries)
        self.assertNotIn(consumer, ctx.design_plan_entries)
        invalidations = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_design_plan_invalidated"
            and fields.get("reason") == "contract_closure_correction_exhausted"
        ]
        self.assertEqual(
            set(invalidations[0]["labels"]),
            {provider, consumer},
        )
        self.assertEqual(invalidations[0]["rejected_labels"], [consumer])

    def test_deferred_closure_blocks_provider_component_not_unrelated_work(self) -> None:
        provider = "def:network"
        consumer = "lem:representable"
        unrelated = "def:scalar"
        nodes = {
            provider: node(provider),
            consumer: node(consumer, uses={provider}),
            unrelated: node(unrelated),
        }
        ctx = SimpleNamespace(
            name="test",
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan="",
            design_plan_entries={},
            telemetry=FakeTelemetry(),
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
        )
        planned = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "contracts": [
                        {
                            "label": provider,
                            "target_signature": (
                                "structure def_network where\n  realizes : Prop"
                            ),
                            "helpers": [],
                            "decisions": [],
                        },
                        {
                            "label": consumer,
                            "target_signature": (
                                "theorem lem_representable : "
                                "def_network.Representable"
                            ),
                            "helpers": [],
                            "decisions": [],
                        },
                        {
                            "label": unrelated,
                            "target_signature": "def def_scalar : Nat",
                            "helpers": [],
                            "decisions": [],
                        },
                    ]
                }
            ),
        )
        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._design_plan_prompt", return_value="plan prompt"
        ), patch(
            "formalize_blueprint._call_model", return_value=planned
        ), patch(
            "formalize_blueprint._correct_phase1_design_plan"
        ) as correction:
            findings = _ensure_phase1_design_plan(
                ctx,
                set(nodes),
                [],
                defer_closure_repair=True,
            )

        correction.assert_not_called()
        self.assertEqual(set(findings), {consumer})
        self.assertEqual(
            _closure_blocked_labels(ctx, findings),
            {provider, consumer},
        )
        self.assertEqual(
            _closure_findings_for_scope(ctx, findings, [unrelated]),
            {},
        )
        self.assertIn("closure_fp", ctx.design_plan_entries[unrelated])

    def test_bottom_up_phase1_runs_closed_work_before_blocked_component_repair(self) -> None:
        provider = "def:network"
        consumer = "lem:representable"
        unrelated = "def:scalar"
        nodes = {
            provider: node(provider),
            consumer: node(consumer, uses={provider}),
            unrelated: node(unrelated),
        }
        ctx = SimpleNamespace(
            name="test",
            nodes=nodes,
            design_plan_entries={
                provider: {
                    "target_signature": (
                        "structure def_network where\n  realizes : Prop"
                    ),
                    "helpers": [],
                },
                consumer: {
                    "target_signature": (
                        "theorem lem_representable : def_network.Representable"
                    ),
                    "helpers": [],
                },
                unrelated: {
                    "target_signature": "def def_scalar : Nat",
                    "helpers": [],
                },
            },
            effective_section_size=0,
            section_size=12,
            quarantined_labels=set(),
            generation_candidates={},
            workers=3,
            telemetry=FakeTelemetry(),
        )
        findings = _design_plan_contract_closure_findings(ctx, nodes)
        events: list[tuple[str, set[str]]] = []
        section_number = 1

        def generate(_ctx, _layer, groups, _sections, _alloc):
            nonlocal section_number
            labels = [label for group in groups for label in group]
            events.append(("generate", set(labels)))
            result = [
                Section(
                    number=section_number,
                    labels=labels,
                    path=Path(f"Chunk{section_number:02d}.lean"),
                    module=f"Chunk{section_number:02d}",
                    import_modules=[],
                )
            ]
            section_number += 1
            return result

        def repair(_ctx, _ordered, _findings, *, repair_scope=None):
            events.append(("repair", set(repair_scope or [])))

        with patch(
            "formalize_blueprint._ensure_phase1_design_plan",
            return_value=findings,
        ), patch(
            "formalize_blueprint._repair_phase1_design_plan_closure",
            side_effect=repair,
        ), patch(
            "formalize_blueprint._validate_design_plan_contract_closure",
            return_value={},
        ), patch(
            "formalize_blueprint._run_validated_contract_phase1_layer",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._save_ctx_state"
        ):
            sections = _run_phase1(ctx, [], set(nodes), "bottom-up")

        self.assertEqual(events[0], ("generate", {unrelated}))
        self.assertEqual(events[1][0], "repair")
        self.assertIn(provider, events[1][1])
        self.assertEqual(_frozen_labels(sections), set(nodes))

    def test_design_plan_preserves_helpers_and_generation_decisions(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "network-v1"},
        )
        parsed = _parse_design_plan_entries(
            ctx,
            [label],
            json.dumps({"contracts": [{
                "label": label,
                "target_signature": "def_network (n : Nat) : Prop",
                "helpers": [{
                    "name": "NetworkData",
                    "kind": "structure",
                    "members": [{"name": "width", "type": "Nat"}],
                    "purpose": "stores the concrete network interface",
                }],
                "decisions": ["The target exposes concrete network data."],
            }]}),
        )

        self.assertEqual(parsed[label]["helpers"][0]["name"], "NetworkData")
        self.assertEqual(
            parsed[label]["helpers"][0]["members"],
            [{"name": "width", "type": "Nat"}],
        )
        self.assertEqual(
            parsed[label]["decisions"],
            ["The target exposes concrete network data."],
        )

        ctx.design_plan_entries = parsed
        ctx.design_plan = ""
        block = _design_plan_block(ctx, [label])
        self.assertIn("structure NetworkData", block)
        self.assertIn("width : Nat", block)
        self.assertIn("The target exposes concrete network data", block)

    def test_design_plan_rejects_helper_members_without_types(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "network-v1"},
        )

        parsed = _parse_design_plan_entries(
            ctx,
            [label],
            json.dumps({"contracts": [{
                "label": label,
                "target_signature": "def_network (n : Nat) : Prop",
                "helpers": [{
                    "name": "NetworkData",
                    "kind": "structure",
                    "required_members": ["width"],
                    "purpose": "stores the concrete network interface",
                }],
                "decisions": [],
            }]}),
        )

        self.assertEqual(parsed, {})

    def test_design_plan_closure_rejects_missing_generated_member(self) -> None:
        provider = "def:network"
        consumer = "lem:representable"
        ctx = SimpleNamespace(
            name="test",
            nodes={
                provider: node(provider),
                consumer: node(consumer, uses={provider}),
            },
            design_plan_entries={
                provider: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "structure def_network where\n  realizes : Prop"
                    ),
                    "helpers": [],
                    "decisions": [],
                },
                consumer: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "theorem lem_representable : "
                        "def_network.Representable"
                    ),
                    "helpers": [],
                    "decisions": [],
                },
            },
        )

        findings = _design_plan_contract_closure_findings(
            ctx, [provider, consumer]
        )

        self.assertNotIn(provider, findings)
        self.assertIn(consumer, findings)
        self.assertIn(
            "def_network.Representable",
            "\n".join(findings[consumer]),
        )

    def test_design_plan_closure_accepts_exposed_generated_member(self) -> None:
        provider = "def:network"
        consumer = "lem:representable"
        ctx = SimpleNamespace(
            name="test",
            nodes={
                provider: node(provider),
                consumer: node(consumer, uses={provider}),
            },
            design_plan_entries={
                provider: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "structure def_network where\n"
                        "  Representable : Prop\n"
                        "  realizes : Prop"
                    ),
                    "helpers": [],
                    "decisions": [],
                },
                consumer: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "theorem lem_representable : "
                        "def_network.Representable"
                    ),
                    "helpers": [],
                    "decisions": [],
                },
            },
        )

        self.assertEqual(
            _design_plan_contract_closure_findings(
                ctx, [provider, consumer]
            ),
            {},
        )

    def test_design_plan_closure_rejects_multiple_public_targets_for_one_node(self) -> None:
        label = "def:relu-function"
        ctx = SimpleNamespace(
            name="test",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "def def_relu_function : Real → Real\n"
                        "def def_relu_vector {n : Nat} : "
                        "(Fin n → Real) → (Fin n → Real)"
                    ),
                    "helpers": [],
                    "decisions": [],
                }
            },
        )

        findings = _design_plan_contract_closure_findings(ctx, [label])

        self.assertIn(label, findings)
        evidence = "\n".join(findings[label])
        self.assertIn("additional public target", evidence)
        self.assertIn("def_relu_vector", evidence)
        self.assertIn("exactly one canonical public declaration", evidence)

    def test_design_plan_closure_accepts_bundled_operations_under_one_target(self) -> None:
        label = "def:relu-function"
        ctx = SimpleNamespace(
            name="test",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_relu_function : ReLUData",
                    "helpers": [
                        {
                            "name": "ReLUData",
                            "kind": "structure",
                            "required_members": ["scalar", "vector"],
                            "purpose": "scalar and coordinatewise ReLU operations",
                        }
                    ],
                    "decisions": [],
                }
            },
        )

        self.assertEqual(
            _design_plan_contract_closure_findings(ctx, [label]),
            {},
        )

    def test_design_plan_closure_accepts_projection_from_returned_owned_helper(self) -> None:
        provider = "def:Pk"
        consumer = "lem:Pk-member"
        ctx = SimpleNamespace(
            name="test",
            nodes={
                provider: node(provider),
                consumer: node(consumer, uses={provider}),
            },
            design_plan_entries={
                provider: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_Pk : PkInterface",
                    "helpers": [
                        {
                            "name": "PkInterface",
                            "kind": "structure",
                            "members": [{"name": "inPk", "type": "Nat -> Prop"}],
                            "required_members": ["inPk"],
                            "purpose": "membership interface",
                        }
                    ],
                    "decisions": [],
                },
                consumer: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "theorem lem_Pk_member : "
                        "def_Pk.inPk 0 = def_Pk.inPk 0"
                    ),
                    "helpers": [],
                    "decisions": [],
                },
            },
        )

        self.assertEqual(
            _design_plan_contract_closure_findings(ctx, [provider, consumer]),
            {},
        )

    def test_design_plan_closure_allows_dependency_owned_helper(self) -> None:
        provider = "def:network"
        consumer = "lem:network-width"
        ctx = SimpleNamespace(
            name="test",
            nodes={
                provider: node(provider),
                consumer: node(consumer, uses={provider}),
            },
            design_plan_entries={
                provider: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_network : NetworkData",
                    "helpers": [
                        {
                            "name": "NetworkData",
                            "kind": "structure",
                            "required_members": ["width"],
                            "purpose": "network carrier",
                        }
                    ],
                    "decisions": [],
                },
                consumer: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "theorem lem_network_width : "
                        "NetworkData.width def_network = "
                        "NetworkData.width def_network"
                    ),
                    "helpers": [],
                    "decisions": [],
                },
            },
        )

        self.assertEqual(
            _design_plan_contract_closure_findings(
                ctx, [provider, consumer]
            ),
            {},
        )

    def test_generated_owner_helper_cycle_requires_plan_revision(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            name="test",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_network : NetworkData",
                    "helpers": [
                        {
                            "name": "NetworkData",
                            "kind": "structure",
                            "required_members": ["owner"],
                            "purpose": "target carrier",
                        }
                    ],
                    "decisions": [],
                }
            },
        )
        code = """structure NetworkData where
  owner : def_network

def def_network : NetworkData := sorry
"""

        findings = _plan_owned_declaration_cycle_findings(code, ctx, [label])

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].label, label)
        self.assertEqual(findings[0].category, "plan_contract_closure")
        self.assertIn("impossible declaration cycle", findings[0].message)

    def test_design_plan_rejects_helpers_that_phase2_cannot_implement(self) -> None:
        label = "def:scalar-relu"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "relu-v1"},
        )
        parsed = _parse_design_plan_entries(
            ctx,
            [label],
            json.dumps({"contracts": [{
                "label": label,
                "target_signature": "def_scalar_relu : Real -> Real",
                "helpers": [
                    {
                        "name": "def_binary_max",
                        "kind": "def",
                        "required_members": ["apply"],
                        "purpose": "binary maximum operation",
                    },
                    {
                        "name": "def_scalar_relu_eq",
                        "kind": "theorem",
                        "required_members": ["eq_max"],
                        "purpose": "pointwise defining equation",
                    },
                ],
                "decisions": ["Implement the target pointwise as max 0 t."],
            }]}),
        )

        self.assertEqual(parsed, {})

    def test_exhausted_semantic_rejection_revises_plan_and_resets_only_node(self) -> None:
        label = "def:relu-function"
        other = "def:other"
        ctx = SimpleNamespace(
            nodes={label: node(label), other: node(other)},
            stmt_fps={label: "relu-v1", other: "other-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "relu-v1",
                    "target_signature": "def_relu_function : OldInterface",
                }
            },
            retry_lifecycle={
                f"phase1_statement:{label}": {
                    "label": label,
                    "stage": "phase1_statement",
                },
                f"phase1_statement:{other}": {
                    "label": other,
                    "stage": "phase1_statement",
                },
            },
            generation_candidates={
                label: {
                    "statement_fp": "relu-v1",
                    "plan_fp": "old-plan",
                    "code": "def def_relu_function : Unit := sorry",
                    "component_labels": [label],
                    "generation_tier": "base",
                },
                other: {"code": "keep"},
            },
            quarantined_labels={label, other},
            quarantine={label: {}, other: {}},
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._correct_phase1_design_plan", return_value=True
        ) as correct:
            revised = _revise_exhausted_phase1_contracts(
                ctx, [label], "opaque interface rejected"
            )

        self.assertEqual(revised, {label})
        correct.assert_called_once_with(
            ctx, [label], "opaque interface rejected", escalated=True
        )
        self.assertNotIn(f"phase1_statement:{label}", ctx.retry_lifecycle)
        self.assertIn(f"phase1_statement:{other}", ctx.retry_lifecycle)
        self.assertIn(label, ctx.generation_candidates)
        self.assertEqual(
            ctx.generation_candidates[label]["repair_stage"],
            "semantic_rejected",
        )
        self.assertFalse(
            ctx.generation_candidates[label]["reusable_uncompiled"]
        )
        self.assertIn(other, ctx.generation_candidates)
        self.assertNotIn(label, ctx.quarantined_labels)
        self.assertIn(other, ctx.quarantined_labels)
        self.assertEqual(
            ctx.design_plan_entries[label]["semantic_revision_count"], 1
        )

    def test_second_semantic_exhaustion_routes_only_revised_node_to_decomposition(
        self,
    ) -> None:
        repeated = "def:repeated"
        first_exhaustion = "lem:first-exhaustion"
        ctx = SimpleNamespace(
            design_plan_entries={
                repeated: {"semantic_revision_count": 1},
                first_exhaustion: {"semantic_revision_count": 0},
            },
            stmt_fps={repeated: "repeated-v1", first_exhaustion: "first-v1"},
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._revise_exhausted_phase1_contracts",
            return_value={first_exhaustion},
        ) as revise:
            decomposition, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    [repeated, first_exhaustion],
                    "exact semantic rejection",
                    layer_no=4,
                    source="test",
                )
            )

        self.assertEqual(decomposition, {repeated})
        self.assertEqual(revised, {first_exhaustion})
        self.assertEqual(unresolved, set())
        revise.assert_called_once_with(
            ctx, {first_exhaustion}, "exact semantic rejection"
        )
        events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_semantic_exhaustion_decomposition"
        ]
        self.assertEqual(events[-1]["labels"], [repeated])
        self.assertEqual(events[-1]["source"], "test")

    def test_first_decomposition_verdict_revises_plan_before_blueprint(self) -> None:
        label = "def:cpwl"
        ctx = SimpleNamespace(
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "semantic_revision_count": 0,
                }
            },
            telemetry=FakeTelemetry(),
        )
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("def def_cpwl : Prop := sorry\n"),
            import_modules=[],
            generation_tier="base",
            sessions={},
        )
        audit = AlignmentAuditResult(
            kind="decomposition",
            reason="the planned interface hides the finite subdivision data",
            rejected={label},
            helpers=["finite subdivision data"],
            kinds_by_label={label: "decomposition"},
            helpers_by_label={label: ["finite subdivision data"]},
            reasons_by_label={
                label: "the planned interface hides the finite subdivision data"
            },
        )

        with patch(
            "formalize_blueprint._revise_exhausted_phase1_contracts",
            return_value={label},
        ) as revise:
            request = _semantic_first_failure_request(
                ctx, 0, [candidate], audit, []
            )

        revise.assert_called_once_with(
            ctx,
            {label},
            "Blueprint contract audit rejected:\n"
            "- the planned interface hides the finite subdivision data",
        )
        self.assertFalse(request.authorizes_blueprint_repair)
        self.assertEqual(request.labels, [label])
        self.assertEqual(request.decomposition_helpers, [])
        self.assertEqual(request.failure_route.action, "independent")

    def test_semantic_rejection_repairs_saved_candidate_before_generation(self) -> None:
        label = "def:network"
        seed = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("def def_network : Nat := sorry\n"),
            import_modules=[],
            generation_tier="base",
        )
        revised = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("def def_network : Nat := sorry\n"),
            import_modules=[],
            generation_tier="escalation",
        )
        ctx = SimpleNamespace(
            nodes={
                label: node(label),
                "def:dependency": node("def:dependency"),
            },
            stmt_fps={label: "network-v1"},
            design_plan_entries={},
            generation_candidates={
                label: {
                    "statement_fp": "network-v1",
                    "plan_fp": "",
                    "code": "def def_network : Nat := sorry",
                    "repair_stage": "semantic_rejected",
                    "required_dependencies": ["def:dependency"],
                }
            },
            generation_feedback={
                label: {
                    "statement_fp": "network-v1",
                    "evidence": "the concrete network composition is missing",
                    "source": "statement_alignment",
                }
            },
            retry_lifecycle={},
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._reusable_uncompiled_candidate",
            return_value=seed,
        ), patch(
            "formalize_blueprint._revise_semantic_candidates",
            return_value=[revised],
        ) as repair, patch(
            "formalize_blueprint._store_generation_candidates"
        ) as store:
            result = _semantic_repair_candidate(ctx, [label], [])

        self.assertIs(result, revised)
        repair.assert_called_once()
        self.assertEqual(
            repair.call_args.args[3].splitlines()[-1],
            "the concrete network composition is missing",
        )
        self.assertEqual(
            repair.call_args.kwargs["required_dependencies"],
            {label: {"def:dependency"}},
        )
        self.assertEqual(
            store.call_args.kwargs["repair_stage"], "semantic_corrected"
        )

    def test_uncompiled_generation_prioritizes_semantic_repair(self) -> None:
        label = "def:network"
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("def def_network : Nat := sorry\n"),
            import_modules=[],
            generation_tier="escalation",
        )
        with patch(
            "formalize_blueprint._semantic_repair_candidate",
            return_value=candidate,
        ) as semantic, patch(
            "formalize_blueprint._reusable_uncompiled_candidate"
        ) as reuse, patch(
            "formalize_blueprint._generate_phase1_statement_group"
        ) as generate:
            result = _generate_uncompiled_phase1_candidate(
                SimpleNamespace(), [label], []
            )

        self.assertIs(result, candidate)
        semantic.assert_called_once()
        reuse.assert_not_called()
        generate.assert_not_called()

    def test_candidate_omitting_planned_helper_fails_before_compilation(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "network-v1",
                    "target_signature": "def_network (n : Nat) : Prop",
                    "helpers": [{
                        "name": "NetworkData",
                        "kind": "structure",
                        "required_members": ["width"],
                        "purpose": "stores the concrete network interface",
                    }],
                    "decisions": [],
                }
            },
        )

        findings = _skeleton_deterministic_findings(
            "def def_network (n : Nat) : Prop := sorry",
            ctx,
            [label],
        )

        self.assertEqual(len(findings), 1)
        self.assertEqual(findings[0].label, label)
        self.assertIn("omitted helper `NetworkData`", findings[0].message)

    def test_planned_helper_survives_canonical_collision_safe_rename(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            telemetry=FakeTelemetry(),
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "network-v1",
                    "target_signature": "def_network (n : Nat) : Prop",
                    "helpers": [
                        {
                            "name": "NetworkData",
                            "kind": "structure",
                            "required_members": ["width"],
                            "purpose": "stores the concrete network interface",
                        }
                    ],
                    "decisions": [],
                }
            },
        )
        canonical = _canonicalize_model_lean(
            ctx,
            [label],
            "structure NetworkData where\n"
            "  width : Nat\n\n"
            "def def_network (n : Nat) : Prop := sorry",
        )
        code = "\n\n".join(decl.text for decl in canonical.parsed.decls)

        self.assertIn("_autobp_", code)
        self.assertEqual(_skeleton_deterministic_findings(code, ctx, [label]), [])

    def test_design_plan_mistranslation_is_rejected_before_lean_generation(self) -> None:
        label = "def:relu"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "relu-v1"},
            tex_blocks={label: "scalar and coordinatewise ReLU"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "relu-v1",
                    "target_signature": "def_relu : Real -> Real",
                    "helpers": [],
                    "decisions": ["scalar only"],
                }
            },
            design_plan="",
            paper_text="",
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
            telemetry=FakeTelemetry(),
        )
        rejected = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "classification": "lean_translation_issue",
                    "issues": [
                        {
                            "node": label,
                            "severity": "reject",
                            "reason": "coordinatewise ReLU was omitted",
                            "missing_helpers": [],
                        }
                    ],
                }
            ),
        )
        with patch(
            "formalize_blueprint._call_model", return_value=rejected
        ) as call_model:
            audit = _audit_phase1_design_plan(ctx, [label])
            repeated = _audit_phase1_design_plan(ctx, [label])

        self.assertIsNotNone(audit)
        self.assertEqual(audit[0], "lean-generation")
        self.assertEqual(audit[2], {label})
        self.assertEqual(repeated, audit)
        self.assertEqual(call_model.call_count, 1)
        self.assertFalse(ctx.design_plan_entries[label].get("audit_fp"))

    def test_plan_audit_does_not_treat_proof_uses_as_public_dependencies(self) -> None:
        dependency = node("def:polytope")
        target = node("constr:delta3-rhombic", uses={"def:polytope", "def:Pk"})
        target.statement_uses = {"def:polytope"}
        target.proof_uses = {"def:Pk"}
        ctx = SimpleNamespace(
            nodes={
                "def:polytope": dependency,
                "def:Pk": node("def:Pk"),
                "constr:delta3-rhombic": target,
            },
            stmt_fps={"constr:delta3-rhombic": "rhombic-v1"},
            tex_blocks={"constr:delta3-rhombic": "A rhombic construction."},
            design_plan_entries={
                "constr:delta3-rhombic": {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "rhombic-v1",
                    "target_signature": (
                        "def constr_delta3_rhombic : def_polytope"
                    ),
                    "helpers": [],
                    "decisions": [],
                }
            },
            design_plan="",
            paper_text="",
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
            telemetry=FakeTelemetry(),
        )
        accepted = CallResult(
            status="ok",
            text=json.dumps(
                {"accepted": True, "classification": "accepted", "issues": []}
            ),
        )
        with patch(
            "formalize_blueprint._call_model", return_value=accepted
        ) as call_model:
            self.assertIsNone(
                _audit_phase1_design_plan(ctx, ["constr:delta3-rhombic"])
            )

        prompt = call_model.call_args.args[1]
        self.assertIn("statement-interface dependencies: def:polytope", prompt)
        self.assertIn("proof-only dependencies: def:Pk", prompt)

    def test_unchanged_plan_correction_is_not_called_twice(self) -> None:
        label = "def:value"
        entry = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": "value-v1",
            "target_signature": "def_value : Nat",
            "helpers": [],
            "decisions": ["exact object"],
            "rejected_audit_fp": "audit-fingerprint",
            "rejected_kind": "lean-generation",
            "rejected_reason": "same rejection",
            "rejected_helpers": [],
        }
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "value-v1"},
            tex_blocks={label: "a natural number"},
            design_plan_entries={label: entry},
            design_plan="",
            paper_text="",
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
            telemetry=FakeTelemetry(),
        )
        unchanged = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "contracts": [
                        {
                            "label": label,
                            "target_signature": "def_value : Nat",
                            "helpers": [],
                            "decisions": ["exact object"],
                        }
                    ]
                }
            ),
        )
        with patch(
            "formalize_blueprint._call_model", return_value=unchanged
        ) as call_model:
            self.assertFalse(
                _correct_phase1_design_plan(ctx, [label], "same rejection")
            )
            self.assertFalse(
                _correct_phase1_design_plan(ctx, [label], "same rejection")
            )

        self.assertEqual(call_model.call_count, 1)
        self.assertEqual(
            ctx.design_plan_entries[label]["rejected_reason"], "same rejection"
        )

    def test_accepted_design_plan_audit_is_fingerprinted_and_reused(self) -> None:
        label = "def:value"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "value-v1"},
            tex_blocks={label: "a natural number"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "value-v1",
                    "target_signature": "def_value : Nat",
                    "helpers": [],
                    "decisions": ["exact object"],
                }
            },
            design_plan="",
            paper_text="",
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
            telemetry=FakeTelemetry(),
        )
        accepted = CallResult(
            status="ok",
            text=json.dumps(
                {"accepted": True, "classification": "accepted", "issues": []}
            ),
        )
        with patch(
            "formalize_blueprint._call_model", return_value=accepted
        ) as call_model:
            self.assertIsNone(_audit_phase1_design_plan(ctx, [label]))
            self.assertIsNone(_audit_phase1_design_plan(ctx, [label]))

        self.assertEqual(call_model.call_count, 1)
        self.assertTrue(ctx.design_plan_entries[label].get("audit_fp"))

    def test_bottom_up_phase1_freezes_dependency_layers_directly(self) -> None:
        nodes = {
            "def:leaf": node("def:leaf"),
            "lem:middle": node("lem:middle", uses={"def:leaf"}),
            "thm:root": node("thm:root", uses={"lem:middle"}),
        }
        ctx = SimpleNamespace(
            nodes=nodes,
            effective_section_size=12,
            section_size=12,
            quarantined_labels=set(),
            telemetry=FakeTelemetry(),
        )
        calls: list[list[str]] = []

        def transact(_ctx, _layer, groups, _sections, alloc):
            labels = [label for group in groups for label in group]
            calls.append(labels)
            number = alloc()
            return [
                Section(
                    number,
                    labels,
                    Path(f"Skeleton{number:02d}.lean"),
                    f"Generated.Skeleton{number:02d}",
                    [],
                    refined_labels=set(labels),
                )
            ]

        with patch("formalize_blueprint._ensure_phase1_design_plan") as plan, patch(
            "formalize_blueprint._run_validated_contract_phase1_layer",
            side_effect=transact,
        ), patch("formalize_blueprint._save_ctx_state"):
            sections = _run_phase1(ctx, [], set(nodes), "bottom-up")
        plan.assert_called_once()
        self.assertIs(plan.call_args.args[0], ctx)
        self.assertEqual(plan.call_args.args[1], set(nodes))
        self.assertEqual(calls, [["def:leaf"], ["lem:middle"], ["thm:root"]])
        self.assertEqual([section.labels for section in sections], calls)

    def test_bottom_up_phase1_audits_each_layer_once(self) -> None:
        nodes = {f"def:n{i}": node(f"def:n{i}") for i in range(4)}
        ctx = SimpleNamespace(
            nodes=nodes,
            effective_section_size=2,
            section_size=2,
            quarantined_labels=set(),
            workers=2,
            telemetry=FakeTelemetry(),
        )

        audits: list[list[str]] = []

        def transact(_ctx, _layer, groups, _sections, alloc):
            labels = [label for group in groups for label in group]
            audits.append(labels)
            sections = []
            for group in groups:
                number = alloc()
                sections.append(
                    Section(
                        number,
                        list(group),
                        Path(f"Skeleton{number:02d}.lean"),
                        f"Generated.Skeleton{number:02d}",
                        [],
                        refined_labels=set(group),
                    )
                )
            return sections

        with patch("formalize_blueprint._ensure_phase1_design_plan"), patch(
            "formalize_blueprint._run_validated_contract_phase1_layer",
            side_effect=transact,
        ), patch("formalize_blueprint._save_ctx_state"):
            sections = _run_phase1(ctx, [], set(nodes), "bottom-up")
        self.assertEqual(len(sections), 2)
        self.assertEqual(len(audits), 1)
        self.assertEqual(set(audits[0]), set(nodes))

    def test_bottom_up_phase1_recomputes_ready_frontier_after_partial_progress(self) -> None:
        nodes = {
            "def:slow": node("def:slow"),
            "def:fast": node("def:fast"),
            "lem:fast-child": node("lem:fast-child", uses={"def:fast"}),
        }
        ctx = SimpleNamespace(
            nodes=nodes,
            effective_section_size=12,
            section_size=12,
            quarantined_labels=set(),
            workers=2,
            telemetry=FakeTelemetry(),
        )
        calls: list[list[str]] = []

        def transact(_ctx, _frontier, groups, _sections, alloc):
            labels = [label for group in groups for label in group]
            calls.append(labels)
            number = alloc()
            return [
                Section(
                    number,
                    labels,
                    Path(f"Skeleton{number:02d}.lean"),
                    f"Generated.Skeleton{number:02d}",
                    [],
                    refined_labels=set(labels),
                )
            ]

        existing = Section(
            1,
            ["def:fast"],
            Path("Skeleton01.lean"),
            "Generated.Skeleton01",
            [],
            refined_labels={"def:fast"},
        )
        with patch("formalize_blueprint._ensure_phase1_design_plan"), patch(
            "formalize_blueprint._run_validated_contract_phase1_layer",
            side_effect=transact,
        ), patch("formalize_blueprint._save_ctx_state"):
            _run_phase1(
                ctx,
                [existing],
                {"def:slow", "lem:fast-child"},
                "bottom-up",
            )

        self.assertEqual(calls, [["def:slow", "lem:fast-child"]])

    def test_reusable_singleton_candidate_is_not_batched_with_fresh_work(self) -> None:
        labels = ["def:a", "def:b"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp-{label}" for label in labels},
            generation_candidates={
                "def:a": {
                    "statement_fp": "fp-def:a",
                    "code": "def def_a : Nat := 1",
                    "component_labels": ["def:a"],
                    "reusable_uncompiled": True,
                }
            },
            effective_section_size=12,
            section_size=12,
            quarantined_labels=set(),
            workers=2,
            telemetry=FakeTelemetry(),
        )
        seen_groups: list[list[list[str]]] = []

        def transact(_ctx, _layer, groups, _sections, alloc):
            seen_groups.append(groups)
            accepted = []
            for group in groups:
                number = alloc()
                accepted.append(
                    Section(
                        number,
                        list(group),
                        Path(f"Skeleton{number:02d}.lean"),
                        f"Generated.Skeleton{number:02d}",
                        [],
                        refined_labels=set(group),
                    )
                )
            return accepted

        with patch("formalize_blueprint._ensure_phase1_design_plan"), patch(
            "formalize_blueprint._run_validated_contract_phase1_layer",
            side_effect=transact,
        ), patch("formalize_blueprint._save_ctx_state"):
            _run_phase1(ctx, [], set(labels), "bottom-up")

        self.assertEqual(seen_groups, [[["def:a"], ["def:b"]]])

    def test_validated_contract_layer_compiles_before_final_audit(self) -> None:
        labels = ["def:a", "def:b"]
        ctx = SimpleNamespace(workers=2, telemetry=FakeTelemetry())
        events: list[str] = []

        def candidate(label: str) -> Phase1LayerCandidate:
            return Phase1LayerCandidate(
                labels=[label],
                parsed=_parse_module(f"def {_lean_name(label)} : Nat := sorry\n"),
                import_modules=[],
                generation_tier="base",
            )

        def generate(_ctx, group, _sections):
            events.append(f"generate:{group[0]}")
            return candidate(group[0])

        compiled = [
            Section(1, labels, Path("Skeleton01.lean"), "Generated.S1", [])
        ]

        def compile_candidates(*_args, **_kwargs):
            events.append("compile")
            return compiled

        def integrate(*_args, **_kwargs):
            events.append("final-audit")
            return compiled

        with patch(
            "formalize_blueprint._generate_uncompiled_phase1_candidate",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._compile_semantic_phase1_candidates",
            side_effect=compile_candidates,
        ), patch(
            "formalize_blueprint._audit_phase1_layer_candidates",
            side_effect=integrate,
        ):
            result = _run_validated_contract_phase1_layer(
                ctx, 0, [["def:a"], ["def:b"]], [], _SectionNumberAllocator(1)
            )

        self.assertIs(result, compiled)
        compile_index = events.index("compile")
        self.assertTrue(
            all(events.index(f"generate:{label}") < compile_index for label in labels)
        )
        self.assertLess(compile_index, events.index("final-audit"))

    def test_validated_contract_layer_does_not_run_precompile_semantic_revision(self) -> None:
        labels = ["def:a", "def:b"]
        ctx = SimpleNamespace(workers=2, telemetry=FakeTelemetry())

        def candidate(label: str) -> Phase1LayerCandidate:
            return Phase1LayerCandidate(
                labels=[label],
                parsed=_parse_module(f"def {_lean_name(label)} : Nat := sorry\n"),
                import_modules=[],
                generation_tier="base",
            )

        generated = {label: candidate(label) for label in labels}
        compiled = [
            Section(1, labels, Path("Skeleton01.lean"), "Generated.S1", [])
        ]

        with patch(
            "formalize_blueprint._generate_uncompiled_phase1_candidate",
            side_effect=lambda _ctx, group, _sections: generated[group[0]],
        ), patch(
            "formalize_blueprint._revise_semantic_candidates",
            return_value=[generated["def:b"]],
        ) as revise, patch(
            "formalize_blueprint._compile_semantic_phase1_candidates",
            return_value=compiled,
        ) as compile_candidates, patch(
            "formalize_blueprint._audit_phase1_layer_candidates",
            return_value=compiled,
        ):
            _run_validated_contract_phase1_layer(
                ctx, 0, [["def:a"], ["def:b"]], [], _SectionNumberAllocator(1)
            )

        revise.assert_not_called()
        approved = compile_candidates.call_args.args[1]
        self.assertEqual(
            {label for item in approved for label in item.labels}, set(labels)
        )

    def test_generation_failure_keeps_deterministically_valid_sibling_candidate(self) -> None:
        good = Phase1LayerCandidate(
            labels=["def:a"],
            parsed=_parse_module("def def_a : Nat := sorry\n"),
            import_modules=[],
            generation_tier="escalation",
        )
        failure = RepairRequest(
            "def:b failed deterministic checks",
            ["def:b"],
            section_labels=["def:b"],
            authorizes_blueprint_repair=False,
        )
        ctx = SimpleNamespace(workers=2, telemetry=FakeTelemetry())
        accepted = Section(
            1,
            ["def:a"],
            Path("Skeleton01.lean"),
            "Generated.S1",
            [],
            refined_labels={"def:a"},
        )

        def generate(_ctx, group, _sections):
            if group == ["def:b"]:
                raise failure
            return good

        with patch(
            "formalize_blueprint._generate_uncompiled_phase1_candidate",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._store_generation_candidates"
        ) as store, patch(
            "formalize_blueprint._compile_and_finalize_semantic_candidates",
            return_value=[accepted],
        ) as finalize:
            with self.assertRaises(RepairRequest) as raised:
                _run_validated_contract_phase1_layer(
                    ctx,
                    1,
                    [["def:a"], ["def:b"]],
                    [],
                    _SectionNumberAllocator(1),
                )

        store.assert_called_once()
        self.assertTrue(store.call_args.kwargs["reusable_uncompiled"])
        self.assertEqual(store.call_args.kwargs["generation_tier"], "escalation")
        finalize.assert_called_once()
        self.assertEqual(raised.exception.labels, ["def:b"])
        self.assertEqual(raised.exception.frozen_sections, [accepted])

    def test_parallel_frontier_preserves_decomposition_beside_dependency_repair(self) -> None:
        decomposition = RepairRequest(
            "def:relu-network needs an explicit computation helper",
            ["def:relu-network"],
            decomposition_helpers=["define the alternating ReLU composition"],
            authorizes_blueprint_repair=True,
        )
        dependency = RepairRequest(
            "lem:valuation-identity must use the concrete polytope contracts",
            ["lem:valuation-identity"],
            authorizes_blueprint_repair=True,
            required_dependencies={
                "lem:valuation-identity": {"def:polytope", "def:support-newton"}
            },
        )
        ctx = SimpleNamespace(workers=2, telemetry=FakeTelemetry())

        def generate(_ctx, group, _sections):
            if group == ["def:relu-network"]:
                raise decomposition
            raise dependency

        with patch(
            "formalize_blueprint._generate_uncompiled_phase1_candidate",
            side_effect=generate,
        ):
            with self.assertRaises(RepairRequest) as raised:
                _run_validated_contract_phase1_layer(
                    ctx,
                    1,
                    [["def:relu-network"], ["lem:valuation-identity"]],
                    [],
                    _SectionNumberAllocator(1),
                )

        request = raised.exception
        self.assertTrue(request.authorizes_blueprint_repair)
        self.assertEqual(
            set(request.labels),
            {"def:relu-network", "lem:valuation-identity"},
        )
        self.assertEqual(request.model_repair_labels, ["def:relu-network"])
        self.assertEqual(
            request.required_dependencies,
            {
                "lem:valuation-identity": {
                    "def:polytope",
                    "def:support-newton",
                }
            },
        )
        self.assertIn(
            "define the alternating ReLU composition",
            request.decomposition_helpers,
        )
        self.assertIn("def:relu-network needs", request.evidence)
        self.assertIn("lem:valuation-identity must", request.evidence)

    def test_partial_response_salvages_deterministically_valid_declaration(self) -> None:
        labels = ["lem:a", "lem:b"]
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp-{label}" for label in labels},
            design_plan_entries={},
            generation_candidates={},
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )
        parsed = _parse_module(
            "theorem lem_a (n : Nat) : n = n := by rfl\n"
        )

        with patch(
            "formalize_blueprint._missing_olean_imports", return_value=[]
        ):
            salvaged = _salvage_partial_phase1_response(
                ctx,
                labels,
                parsed,
                [],
                generation_tier="base",
            )

        self.assertEqual(salvaged, ["lem:a"])
        self.assertTrue(
            ctx.generation_candidates["lem:a"]["reusable_uncompiled"]
        )
        self.assertNotIn("lem:b", ctx.generation_candidates)

    def test_missing_declaration_routes_only_unsalvaged_target(self) -> None:
        labels = ["lem:a", "lem:b"]
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp-{label}" for label in labels},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            unavailable_imports=set(),
            base_timeout=30,
            hard_timeout=60,
            base_effort=None,
            escalation_effort=None,
            telemetry=FakeTelemetry(),
        )
        placeholders = _parse_module(
            "theorem lem_a : True := sorry\n\n"
            "theorem lem_b : True := sorry\n"
        )
        section = Section(
            0,
            labels,
            Path("Phase1Uncompiled.lean"),
            "Generated.Phase1Uncompiled",
            [],
        )
        response = CallResult(
            status="ok", text="theorem lem_a : True := by trivial\n"
        )

        with patch("formalize_blueprint._bulk_skeleton_prompt", return_value="prompt"), patch(
            "formalize_blueprint._call_model", return_value=response
        ), patch(
            "formalize_blueprint._salvage_partial_phase1_response",
            return_value=["lem:a"],
        ):
            with self.assertRaises(RepairRequest) as raised:
                _generate_phase1_statement_group(
                    ctx, section, labels, [], [], placeholders
                )

        self.assertEqual(raised.exception.labels, ["lem:b"])
        self.assertEqual(raised.exception.failure_route.action, "isolate")
        self.assertEqual(raised.exception.failure_route.accepted_labels, ("lem:a",))

    def test_parallel_compile_persists_and_reports_every_failed_group(self) -> None:
        labels = ["def:a", "def:b"]
        candidates = [
            Phase1LayerCandidate(
                labels=[label],
                parsed=_parse_module(f"def {_lean_name(label)} : Nat := 1\n"),
                import_modules=[],
                generation_tier="base",
            )
            for label in labels
        ]
        ctx = SimpleNamespace(workers=2, telemetry=FakeTelemetry())

        def fail_compile(_ctx, candidate_labels, *_args, **kwargs):
            kwargs["failure_evidence"].append(
                f"Lean failed for {candidate_labels[0]}"
            )
            return None

        with patch(
            "formalize_blueprint._freeze_section_from_code",
            side_effect=fail_compile,
        ), patch("formalize_blueprint._store_generation_candidates") as store, patch(
            "formalize_blueprint._store_generation_feedback"
        ) as feedback:
            with self.assertRaises(RepairRequest) as raised:
                _compile_semantic_phase1_candidates(
                    ctx,
                    candidates,
                    [],
                    _SectionNumberAllocator(1),
                    layer_no=0,
                )

        self.assertEqual(set(raised.exception.labels), set(labels))
        self.assertEqual(len(raised.exception.failure_routes), 2)
        self.assertEqual(store.call_count, 2)
        self.assertEqual(feedback.call_count, 2)
        self.assertIn("Lean failed for def:a", raised.exception.evidence)
        self.assertIn("Lean failed for def:b", raised.exception.evidence)

    def test_generation_failure_preserves_siblings_accepted_beside_audit_failure(self) -> None:
        generated = Phase1LayerCandidate(
            labels=["def:a", "def:c"],
            parsed=_parse_module(
                "def def_a : Nat := sorry\n\ndef def_c : Nat := sorry\n"
            ),
            import_modules=[],
            generation_tier="base",
        )
        generation_failure = RepairRequest(
            "def:b failed deterministic checks",
            ["def:b"],
            authorizes_blueprint_repair=False,
        )
        accepted = Section(
            1,
            ["def:a"],
            Path("Skeleton01.lean"),
            "Generated.S1",
            [],
            refined_labels={"def:a"},
        )
        audit_failure = RepairRequest(
            "def:c failed statement alignment",
            ["def:c"],
            frozen_sections=[accepted],
            authorizes_blueprint_repair=False,
        )
        ctx = SimpleNamespace(workers=2, telemetry=FakeTelemetry())

        def generate(_ctx, group, _sections):
            if group == ["def:b"]:
                raise generation_failure
            return generated

        with patch(
            "formalize_blueprint._generate_uncompiled_phase1_candidate",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._store_generation_candidates"
        ), patch(
            "formalize_blueprint._compile_and_finalize_semantic_candidates",
            side_effect=audit_failure,
        ):
            with self.assertRaises(RepairRequest) as raised:
                _run_validated_contract_phase1_layer(
                    ctx,
                    1,
                    [["def:a", "def:c"], ["def:b"]],
                    [],
                    _SectionNumberAllocator(1),
                )

        self.assertEqual(set(raised.exception.labels), {"def:b", "def:c"})
        self.assertIn("def:b failed deterministic checks", raised.exception.evidence)
        self.assertIn("def:c failed statement alignment", raised.exception.evidence)
        self.assertEqual(raised.exception.frozen_sections, [accepted])

    def test_partial_compile_success_is_integrated_before_retry_preserves_it(self) -> None:
        candidate = Phase1LayerCandidate(
            labels=["def:a", "def:b"],
            parsed=_parse_module("def def_a : Nat := 1\n\ndef def_b : Nat := 2\n"),
            import_modules=[],
            generation_tier="base",
        )
        compiled = Section(
            1,
            ["def:a"],
            Path("Skeleton01.lean"),
            "Generated.S1",
            [],
        )
        finalized = Section(
            2,
            ["def:a"],
            Path("Skeleton02.lean"),
            "Generated.S2",
            [],
            refined_labels={"def:a"},
        )
        failure = RepairRequest(
            "def:b failed Lean",
            ["def:b"],
            frozen_sections=[compiled],
        )
        with patch(
            "formalize_blueprint._compile_semantic_phase1_candidates",
            side_effect=failure,
        ), patch(
            "formalize_blueprint._audit_phase1_layer_candidates",
            return_value=[finalized],
        ) as integrate:
            with self.assertRaises(RepairRequest) as raised:
                _compile_and_finalize_semantic_candidates(
                    SimpleNamespace(),
                    [candidate],
                    [],
                    _SectionNumberAllocator(1),
                    layer_no=0,
                )

        integrate.assert_called_once()
        self.assertEqual(raised.exception.frozen_sections, [finalized])

    def test_routed_phase1_fragments_run_concurrently(self) -> None:
        ctx = SimpleNamespace(
            defer_phase1_alignment=True,
            workers=3,
            nodes={label: node(label) for label in ("def:a", "def:b", "def:c")},
            telemetry=FakeTelemetry(),
        )
        thread_ids: set[int] = set()
        lock = threading.Lock()

        def freeze(_ctx, labels, _sections, alloc, **_kwargs):
            with lock:
                thread_ids.add(threading.get_ident())
            time.sleep(0.03)
            number = alloc()
            return [
                Section(
                    number,
                    list(labels),
                    Path(f"Skeleton{number:02d}.lean"),
                    f"Generated.Skeleton{number:02d}",
                    [],
                    refined_labels=set(),
                )
            ]

        with patch("formalize_blueprint._freeze_section", side_effect=freeze):
            sections = _freeze_parts(
                ctx,
                [["def:a"], ["def:b"], ["def:c"]],
                [],
                _SectionNumberAllocator(1),
            )
        self.assertEqual(len(sections), 3)
        self.assertGreater(len(thread_ids), 1)

    def test_layer_audit_routes_rejected_subset_without_escalated_patch(self) -> None:
        nodes = {
            "def:a": node("def:a"),
            "def:b": node("def:b"),
            "def:c": node("def:c"),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_fps={label: f"fp-{label}" for label in nodes},
            generation_feedback={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            workers=2,
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
        )
        first_audit = (
            "lean-generation",
            "def:b needs a more faithful Lean statement",
            {"def:b"},
            [],
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = [root / "Skeleton01.lean", root / "Skeleton02.lean"]
            paths[0].write_text(
                "def def_a : Nat := by sorry\n\ndef def_b : Nat := by sorry\n",
                encoding="utf-8",
            )
            paths[1].write_text("def def_c : Nat := by sorry\n", encoding="utf-8")
            candidates = [
                Section(1, ["def:a", "def:b"], paths[0], "Generated.S1", []),
                Section(2, ["def:c"], paths[1], "Generated.S2", []),
            ]
            retained = Section(
                3,
                ["def:a"],
                root / "Skeleton03.lean",
                "Generated.S3",
                [],
                refined_labels=set(),
            )
            with patch("formalize_blueprint.SCRATCH_DIR", root), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._model_alignment_audit",
                return_value=first_audit,
            ) as audit, patch(
                "formalize_blueprint._patch_phase1_candidate_section",
                return_value=True,
            ) as patch_candidate, patch(
                "formalize_blueprint._freeze_section_from_code",
                return_value=[retained],
            ), patch(
                "formalize_blueprint._note_frozen_section"
            ):
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(
                        ctx,
                        3,
                        candidates,
                        [],
                        _SectionNumberAllocator(3),
                    )
        self.assertEqual(audit.call_count, 1)
        patch_candidate.assert_not_called()
        self.assertEqual(raised.exception.labels, ["def:b"])
        self.assertEqual(raised.exception.failure_route.action, "independent")
        self.assertIn("def def_b", ctx.generation_candidates["def:b"]["code"])
        self.assertEqual(
            [
                label
                for section in raised.exception.frozen_sections
                for label in section.labels
            ],
            ["def:a", "def:c"],
        )

    def test_recombined_singletons_keep_independent_escalation_state(self) -> None:
        labels = ["def:a", "def:b"]
        nodes = {label: node(label) for label in labels}
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_fps={label: f"fp-{label}" for label in labels},
            generation_feedback={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            workers=2,
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
        )
        rejection = (
            "lean-generation",
            "both declarations dropped required contract details",
            set(labels),
            [],
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            candidates = []
            for number, label in enumerate(labels, 1):
                path = root / f"Skeleton{number:02d}.lean"
                path.write_text(
                    f"def {label.replace(':', '_')} : Nat := by sorry\n",
                    encoding="utf-8",
                )
                candidates.append(
                    Section(
                        number,
                        [label],
                        path,
                        f"Generated.S{number}",
                        [],
                        generation_tier="base",
                    )
                )
            with patch("formalize_blueprint.SCRATCH_DIR", root), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._model_alignment_audit", return_value=rejection
            ):
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(ctx, 1, candidates)

        self.assertFalse(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(raised.exception.failure_route.action, "independent")
        self.assertEqual(
            raised.exception.failure_route.parts,
            (("def:a",), ("def:b",)),
        )
        self.assertEqual(ctx.quarantined_labels, set(labels))
        for label in labels:
            self.assertEqual(
                _retry_next_tier(ctx, label, "phase1_statement"), "escalation"
            )

    def test_recombined_escalated_singletons_do_not_reset_to_base(self) -> None:
        labels = ["def:a", "def:b"]
        nodes = {label: node(label) for label in labels}
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_fps={label: f"fp-{label}" for label in labels},
            generation_feedback={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            workers=2,
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
        )
        rejection = (
            "lean-generation",
            "the escalated declarations still do not match",
            set(labels),
            [],
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            candidates = []
            for number, label in enumerate(labels, 1):
                path = root / f"Skeleton{number:02d}.lean"
                path.write_text("def placeholder : Nat := 0\n", encoding="utf-8")
                candidates.append(
                    Section(
                        number,
                        [label],
                        path,
                        f"Generated.S{number}",
                        [],
                        generation_tier="escalation",
                    )
                )
            with patch("formalize_blueprint.SCRATCH_DIR", root), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._model_alignment_audit", return_value=rejection
            ):
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(ctx, 1, candidates)

        self.assertFalse(raised.exception.authorizes_blueprint_repair)
        self.assertIsNone(raised.exception.failure_route)
        for label in labels:
            entry = ctx.retry_lifecycle[f"phase1_statement:{label}"]
            self.assertEqual(entry["state"], "exhausted")

    def test_mixed_tiers_repair_only_the_exhausted_contract(self) -> None:
        labels = ["def:exhausted", "def:retry-a", "def:retry-b"]
        nodes = {label: node(label) for label in labels}
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_fps={label: f"fp-{label}" for label in labels},
            generation_feedback={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            workers=3,
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
        )
        _record_retry_failure(
            ctx,
            ["def:exhausted"],
            stage="phase1_statement",
            attempted_tier="base",
            evidence="first rejection",
            source="test",
        )
        rejection = (
            "lean-generation",
            "all three declarations dropped contract details",
            set(labels),
            [],
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            candidates = []
            for number, label in enumerate(labels, 1):
                path = root / f"Skeleton{number:02d}.lean"
                path.write_text("def placeholder : Nat := 0\n", encoding="utf-8")
                candidates.append(
                    Section(
                        number,
                        [label],
                        path,
                        f"Generated.S{number}",
                        [],
                        generation_tier=(
                            "escalation" if label == "def:exhausted" else "base"
                        ),
                    )
                )
            with patch("formalize_blueprint.SCRATCH_DIR", root), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._model_alignment_audit", return_value=rejection
            ):
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(ctx, 1, candidates)

        self.assertFalse(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(raised.exception.labels, ["def:exhausted"])
        self.assertEqual(raised.exception.section_labels, ["def:exhausted"])
        self.assertEqual(raised.exception.context_labels, sorted(labels))
        self.assertEqual(
            _retry_next_tier(ctx, "def:exhausted", "phase1_statement"),
            "escalation",
        )
        self.assertEqual(
            ctx.retry_lifecycle["phase1_statement:def:exhausted"]["state"],
            "exhausted",
        )
        for label in ["def:retry-a", "def:retry-b"]:
            self.assertEqual(
                ctx.retry_lifecycle[f"phase1_statement:{label}"]["state"],
                "escalation",
            )

    def test_stuck_state_does_not_merge_overlapping_edit_scopes(self) -> None:
        states = [SectionStuckState(labels={"def:a", "def:b"}, repairs=1)]

        exact = _stuck_state_for(states, ["def:a", "def:b"])
        overlapping = _stuck_state_for(states, ["def:a", "def:c"])

        self.assertIs(exact, states[0])
        self.assertIsNot(overlapping, states[0])
        self.assertEqual(len(states), 2)
        self.assertEqual(states[0].labels, {"def:a", "def:b"})
        self.assertEqual(overlapping.labels, {"def:a", "def:c"})

    def test_bottom_up_retry_starts_rejected_singletons_at_escalation(self) -> None:
        label = "def:a"
        nodes = {label: node(label)}
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_fps={label: "fp-def:a"},
            retry_lifecycle={},
            telemetry=FakeTelemetry(),
            base_timeout=10,
            hard_timeout=20,
        )
        _record_retry_failure(
            ctx,
            [label],
            stage="phase1_statement",
            attempted_tier="base",
            evidence="layer audit rejected it",
            source="test",
        )
        observed: list[bool] = []

        def generate(_ctx, _sec, labels, _sections, _imports, parsed, **kwargs):
            observed.append(kwargs.get("force_first_escalated", False))
            kwargs["generation_tier_out"].append("escalation")
            return parsed

        with patch(
            "formalize_blueprint._generate_phase1_statement_group",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._skeleton_code_findings", return_value=[]
        ), patch(
            "formalize_blueprint._skeleton_deterministic_findings", return_value=[]
        ):
            candidate = _generate_uncompiled_phase1_candidate(ctx, [label], [])

        self.assertEqual(observed, [True])
        self.assertEqual(candidate.generation_tier, "escalation")

    def test_layer_audit_retains_accepted_siblings_from_rejected_section(self) -> None:
        nodes = {
            "def:a": node("def:a"),
            "def:b": node("def:b"),
            "def:c": node("def:c"),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            workers=2,
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
            defer_phase1_alignment=False,
        )
        rejection = (
            "blueprint",
            "def:b has the wrong contract",
            {"def:b"},
            [],
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            paths = [root / "Skeleton01.lean", root / "Skeleton02.lean"]
            paths[0].write_text(
                "def def_a : Nat := 0\n\ndef def_b : Nat := 0\n",
                encoding="utf-8",
            )
            paths[1].write_text("def def_c : Nat := 0\n", encoding="utf-8")
            candidates = [
                Section(1, ["def:a", "def:b"], paths[0], "Generated.S1", []),
                Section(2, ["def:c"], paths[1], "Generated.S2", []),
            ]
            retained = Section(
                3,
                ["def:a"],
                root / "Skeleton03.lean",
                "Generated.S3",
                [],
                refined_labels=set(),
            )
            with patch("formalize_blueprint.SCRATCH_DIR", root), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._model_alignment_audit", return_value=rejection
            ), patch(
                "formalize_blueprint._freeze_section_from_code",
                return_value=[retained],
            ) as reuse, patch(
                "formalize_blueprint._note_frozen_section"
            ):
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(
                        ctx,
                        2,
                        candidates,
                        [],
                        _SectionNumberAllocator(3),
                    )
        request = raised.exception
        self.assertEqual(request.section_labels, ["def:b"])
        self.assertEqual(
            [label for section in request.frozen_sections for label in section.labels],
            ["def:a", "def:c"],
        )
        self.assertEqual(reuse.call_args.args[1], ["def:a"])
        event_names = [event for event, _fields in ctx.telemetry.events]
        self.assertIn("phase1_partial_section_retained", event_names)

    def test_phase1_layer_telemetry_builds_classifier_rows(self) -> None:
        events = [
            {
                "event": "formalize_config",
                "run_id": "run-1",
                "blueprint": "paper",
            },
            {
                "event": "model_call",
                "run_id": "run-1",
                "blueprint": "paper",
                "purpose": "statement_audit",
                "labels": ["def:a", "def:b"],
                "duration_s": 12.0,
                "status": "ok",
            },
            {
                "event": "phase1_layer_rejected",
                "run_id": "run-1",
                "blueprint": "paper",
                "layer": 2,
                "labels": ["def:a", "def:b"],
                "rejected_labels": ["def:b"],
                "accepted_labels": ["def:a"],
                "discarded_labels": ["def:b"],
                "classification": "lean-generation",
            },
            {
                "event": "node_retry_lifecycle",
                "run_id": "run-1",
                "blueprint": "paper",
                "label": "def:b",
                "stage": "phase1_statement",
                "statement_fp": "fp-b",
                "previous_state": "base",
                "attempted_tier": "base",
                "next_state": "escalation",
                "failures": 1,
                "source": "phase1_layer_2_alignment",
                "evidence_sha256": "abc",
            },
            {
                "event": "phase1_retry_candidate_saved",
                "run_id": "run-1",
                "blueprint": "paper",
                "labels": ["def:b"],
                "source": "phase1_layer_2_alignment",
                "code_chars": 321,
                "statement_fps": {"def:b": "fp-b"},
            },
            {
                "event": "phase1_retry_candidate_injected",
                "run_id": "run-1",
                "blueprint": "paper",
                "labels": ["def:b"],
                "code_chars": 321,
            },
            {
                "event": "phase1_candidate_transition",
                "run_id": "run-1",
                "blueprint": "paper",
                "labels": ["def:b"],
                "statement_fps": {"def:b": "fp-b"},
                "plan_fps": {"def:b": "plan-b"},
                "candidate_hash": "candidate-b",
                "parent_candidate_hashes": ["candidate-a"],
                "source": "deterministic_patch",
                "generation_tier": "base",
                "accepted_as_best": False,
                "accepted_as_working": True,
                "decision_reasons": ["deterministic_regression"],
                "deterministic_obligations": ["requires:a", "requires:b"],
                "satisfied_obligations": ["requires:a"],
                "remaining_obligations": ["requires:b"],
                "newly_satisfied": [],
                "regressed_obligations": ["requires:b"],
                "lean_status": "unknown",
                "semantic_status": "unknown",
            },
        ]
        rows = build_datasets(events)["fast_phase1_layer_examples"]
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["rejected_labels"], ["def:b"])
        self.assertEqual(rows[0]["audit_model_call_count"], 1)
        self.assertEqual(rows[0]["audit_model_duration_total_s"], 12.0)
        lifecycle = build_datasets(events)["fast_skeleton_routing_examples"]
        self.assertEqual(len(lifecycle), 3)
        self.assertEqual(lifecycle[0]["next_state"], "escalation")
        self.assertEqual(lifecycle[0]["statement_fp"], "fp-b")
        self.assertEqual(lifecycle[1]["code_chars"], 321)
        self.assertEqual(lifecycle[2]["event"], "phase1_retry_candidate_injected")
        transitions = build_datasets(events)[
            "fast_phase1_candidate_transition_examples"
        ]
        self.assertEqual(len(transitions), 1)
        self.assertFalse(transitions[0]["accepted_as_best"])
        self.assertTrue(transitions[0]["accepted_as_working"])
        self.assertEqual(
            transitions[0]["regressed_obligations"], ["requires:b"]
        )


if __name__ == "__main__":
    unittest.main()
