from __future__ import annotations

import copy
import hashlib
import io
import sys
import json
import re
import subprocess
import tempfile
import threading
import time
import unittest
from concurrent.futures import ThreadPoolExecutor
from unittest.mock import patch
from contextlib import redirect_stdout
from pathlib import Path
from types import SimpleNamespace


REPO_ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from formalize_blueprint import (  # noqa: E402
    AlignmentAuditResult,
    CanonicalModelModule,
    DeclBlock,
    DESIGN_PLAN_SCHEMA_VERSION,
    SEMANTIC_PLAN_SCHEMA_VERSION,
    DesignPlanCandidate,
    PHASE1_STATEMENT_ORDER,
    PHASE2_PROOF_ORDER,
    OPEN_CONJECTURE_TARGET_KIND,
    OBJECT_COMPILE_USABILITY_TIMEOUT,
    OBJECT_IMPLEMENTATION_FAILURE_PREFIX,
    OBJECT_INTERFACE_FAILURE_PREFIX,
    _add_phase1_boilerplate_names,
    _bottom_up_proof_layers,
    _bottom_up_statement_layers,
    _bottom_up_ready_frontier,
    _begin_phase2,
    _create_phase1_checkpoint,
    _restore_phase1_checkpoint,
    _phase1_checkpoint_available,
    _apply_proof_batch,
    _apply_phase1_retry_scheduling,
    _apply_required_dependency_edges,
    _apply_skeleton_replacements,
    _activate_blueprint_direct_generation,
    _transition_phase1_generation_epoch,
    _audit_phase1_design_plan,
    _phase1_frontier_plan_gateway,
    _audit_phase1_layer_candidates,
    _dependency_contract_table,
    _delivered_decl_texts,
    _design_plan_block,
    _evaluate_design_plan_candidate,
    _merge_design_plan_candidates,
    _merge_phase2_repair_followup,
    _design_plan_prompt,
    _design_plan_contract_closure_issues,
    _design_plan_contract_closure_findings,
    _design_plan_dependency_closure_details,
    _design_plan_closure_repair_components,
    _validate_design_plan_contract_closure,
    _ensure_phase1_design_plan,
    _findings_require_plan_revision,
    _generation_feedback_for,
    _active_diagnostic_evidence,
    _clear_generation_feedback,
    _consume_diagnostic_evidence,
    _record_diagnostic_evidence,
    _diagnostic_failure_signature,
    _generation_candidates_for,
    _invalid_mathlib_refusal_mappings,
    _route_lean_generation_failure,
    _invalidate_after_repair,
    _insert_statement_dependencies,
    _initial_plan_admission,
    _initial_plan_repair_admission,
    _initial_plan_repair_costs,
    _initial_design_plan_tournament,
    _lean_error_shape,
    _lean_failure_may_be_fixed_by_broad_mathlib,
    _lean_failure_fingerprint,
    _missing_lean_surface_names,
    _lean_name,
    _lean_compile_findings,
    _lean_declarations,
    _load_state,
    _model_alignment_audit,
    _audit_post_repair_boundary,
    _mark_repair_boundary_pending,
    _post_repair_boundary_prompt,
    _pending_repair_boundary_request,
    _minimal_dependency_interface,
    _partition_phase1_groups_by_dependency_context,
    _coalesce_phase1_semantic_correction_waves,
    _note_frozen_section,
    _next_phase1_group,
    _next_implementation_frontier,
    _parts_around_labels,
    _parse_design_plan_entries,
    _prepare_blueprint_draft,
    _proof_base_round_limit,
    _prove_section,
    _promote_blueprint_draft,
    _prune_stale_generated,
    _prune_stale_blueprint_direct_generation,
    _prune_stale_generation_feedback,
    _prune_stale_diagnostic_evidence,
    _prune_stale_phase1_dependency_observations,
    _prune_stale_generation_candidates,
    _prune_stale_phase1_exchange_history,
    _prune_stale_local_group_partitions,
    _prune_stale_quarantine,
    _prune_stale_retry_lifecycle,
    _parse_module,
    _ingest_model_lean,
    _normalize_theorem_like_keywords,
    _canonicalize_model_lean,
    _closure_blocked_labels,
    _closure_findings_for_scope,
    _planned_helper_owner_by_name,
    _plan_owned_declaration_cycle_findings,
    _plan_realized_semantic_rejections,
    _preserve_plan_entry_progress,
    _phase1_compile_plan_defects,
    _phase1_interface_prompt_rule,
    _phase1_interface_usability_evidence,
    _candidate_is_reusable_uncompiled,
    _candidate_exactly_realizes_plan,
    _candidate_plan_fingerprint,
    _candidate_transition_decision,
    _decomposition_orientation_findings,
    _decomposition_orientation_dependency_edges,
    _isolated_deterministic_failure_labels,
    _quarantine_labels,
    _reactivate_deferred_sections,
    _retry_statement_patch_compile_once,
    _realize_typed_contracts_from_candidate,
    _run_initial_declaration_pass,
    _run_phase1,
    _run_pending_declaration_work,
    _run_phase2_whole_node_repairs,
    _run_phase2_whole_node_transaction,
    _enqueue_phase2_repair_requests,
    _pending_phase2_repair_request,
    _activate_phase2_repair_request,
    _start_phase2_repair_transaction,
    _start_caught_phase2_repair_transaction,
    _begin_phase2_repair_transaction,
    _phase2_repair_transaction_dir,
    _mark_phase2_repair_verifying,
    _complete_phase2_repair_request,
    _discard_phase2_repair_transaction,
    _phase2_repair_context_fingerprint,
    _restore_interrupted_phase2_repair,
    _restore_phase2_repair_transaction_files,
    _restart_active_phase2_repair,
    _reroute_active_phase2_repair_to_provider,
    _phase2_candidate_failure_kind,
    _phase2_complete_node_correction_prompt,
    _phase2_node_candidate_epoch,
    _phase2_node_candidate,
    _store_phase2_node_candidate,
    _refine_statement_group,
    _phase1_repair_scope_violations,
    _phase2_existing_repair_scope_violations,
    _phase2_definition_prerequisites,
    _persist_phase2_section_outcome,
    _phase2_prerequisite_frontier,
    _phase2_prerequisite_request_for_repair,
    _phase2_declaration_work_labels,
    _prioritized_phase2_declaration_work,
    _route_phase2_proof_outcomes,
    _phase1_recompile_environment,
    _section_compile_fingerprint,
    _section_exact_source_fingerprint,
    _migrate_section_compile_fingerprints,
    _phase1_target_kinds,
    _records_conjecture,
    _phase1_target_interface_text,
    _decl_interface_text,
    _planned_target_result_type,
    _generate_uncompiled_phase1_candidate,
    _compile_semantic_phase1_candidate,
    _compile_semantic_phase1_candidates,
    _specific_import_modules_for_missing_names,
    _compile_and_finalize_semantic_candidates,
    _finalize_phase1_accepted_sections,
    _compile_fast_candidate_object,
    _conjecture_policy_prompt,
    _contract_work_stage,
    _correct_phase1_design_plan,
    _repair_phase1_design_plan_closure,
    _reusable_uncompiled_candidate,
    _retained_generation_candidate_code,
    _salvage_partial_phase1_response,
    _semantic_repair_candidate,
    _semantic_first_failure_request,
    _semantic_exhaustion_policy,
    _route_phase1_compile_failure,
    _route_phase1_precompile_deterministic_failure,
    _route_exhausted_phase1_semantics,
    _revise_unusable_interface_plan,
    _revise_semantic_candidates,
    _revise_exhausted_phase1_contracts,
    _revise_decomposition_plans_once,
    _run_validated_contract_phase1_layer,
    _repair_graph_distances,
    _save_state,
    _phase1_exchange_finish,
    _phase1_exchange_start,
    _store_generation_feedback,
    _confirmed_phase1_dependency_observations,
    _record_phase1_dependency_observations,
    _targeted_skeleton_patch_prompt,
    _targeted_patch_skeleton_decls,
    _store_generation_candidates,
    _statement_audit_prompt,
    _statement_surface_probe_code,
    _stuck_state_for,
    _record_retry_failure,
    _retry_next_tier,
    _freeze_parts,
    _freeze_section,
    _freeze_section_from_code,
    _frozen_labels,
    _phase2_body_progress,
    _print_pipeline_progress,
    _recorded_conjecture_labels,
    _verified_node_labels,
    _generate_phase1_statement_group,
    _proved_labels,
    _reserved_labels,
    _requires_initial_declaration_pass,
    _requires_blueprint_transaction,
    _skeleton_code_findings,
    _skeleton_deterministic_findings,
    _format_skeleton_findings,
    _target_components_from_helpers,
    _top_down_statement_layers,
    _SectionNumberAllocator,
    CallResult,
    Ctx,
    RepairRequest,
    Section,
    SectionProofOutcome,
    Phase1LayerCandidate,
    ParsedModule,
    SectionStuckState,
    SkeletonFinding,
    TARGETED_DECL_PATCH_ROUNDS,
)
from refine_blueprint_with_lean import (  # noqa: E402
    LeanAttempt,
    _compile_module_olean,
    _decl_signatures,
    _parse_decomposition_refusal,
)
from validate_blueprint import Node, validate_blueprint  # noqa: E402
from build_classifier_dataset import build_datasets  # noqa: E402
from webui import (  # noqa: E402
    _read_last_refine_settings,
    _write_last_refine_settings,
    build_command as build_webui_command,
)


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
    def test_rejected_theorem_like_candidate_cannot_rewrite_its_contract(self) -> None:
        label = "prop:dyadic-weights"
        original_signature = "theorem prop_dyadic_weights (n : Nat) : n = n"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            semantic_plan_entries={
                label: {"representation": "exact", "obligations": []}
            },
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": original_signature,
                    "helpers": [],
                    "decisions": [],
                    "origin": "phase1_candidate",
                }
            },
        )

        with patch(
            "formalize_blueprint._realize_typed_contracts_from_candidate"
        ) as realize:
            wrong_kind = _skeleton_deterministic_findings(
                "def prop_dyadic_weights (n : Nat) : Prop := sorry\n",
                ctx,
                [label],
            )
            bare_prop = _skeleton_deterministic_findings(
                "theorem prop_dyadic_weights (n : Nat) : Prop := sorry\n",
                ctx,
                [label],
            )

        realize.assert_not_called()
        self.assertTrue(
            any(finding.category == "wrong_kind" for finding in wrong_kind)
        )
        self.assertTrue(
            any("bare proposition sort" in finding.message for finding in bare_prop)
        )
        self.assertEqual(
            ctx.design_plan_entries[label]["target_signature"],
            original_signature,
        )

    def test_failed_semantic_patch_preserves_producing_tier_for_exhaustion(self) -> None:
        label = "prop:dyadic-weights"
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module(
                "theorem prop_dyadic_weights (n : Nat) : n = n := sorry\n"
            ),
            import_modules=[],
            generation_tier="escalation",
        )
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            stmt_fps={label: "dyadic-v1"},
            semantic_plan_entries={
                label: {"representation": "exact", "obligations": []}
            },
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "dyadic-v1",
                    "target_signature": (
                        "theorem prop_dyadic_weights (n : Nat) : n = n"
                    ),
                    "origin": "phase1_candidate",
                    "semantic_revision_count": 0,
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            telemetry=FakeTelemetry(),
            base_timeout=30,
            hard_timeout=60,
        )

        # The candidate came from escalation, so its base attempt has already
        # advanced the same persisted per-node lifecycle.
        _record_retry_failure(
            ctx,
            [label],
            stage="phase1_statement",
            attempted_tier="base",
            evidence="base candidate failed",
            source="historical_setup",
        )

        with patch(
            "formalize_blueprint._targeted_patch_skeleton_decls",
            return_value=(None, "exchange sample limit reached"),
        ):
            with self.assertRaises(RepairRequest) as raised:
                _revise_semantic_candidates(
                    ctx,
                    [candidate],
                    {label},
                    "the declaration does not state the blueprint proposition",
                    [],
                )

        request = raised.exception
        self.assertEqual(request.retry_attempted_tier, "escalation")
        self.assertEqual(request.labels, [label])
        self.assertIn(label, request.evidence_by_label)
        self.assertIn("exchange sample limit", request.evidence_by_label[label])

        with patch(
            "formalize_blueprint._store_generation_feedback"
        ), patch(
            "formalize_blueprint._prune_stale_generation_candidates"
        ), patch(
            "formalize_blueprint._sync_design_plan"
        ):
            routed = _route_phase1_precompile_deterministic_failure(
                ctx, request, layer_no=6
            )

        self.assertEqual(len(routed), 1)
        self.assertTrue(routed[0].plan_revision_required)
        self.assertFalse(routed[0].authorizes_blueprint_repair)
        self.assertIn(label, ctx.blueprint_direct_generation)

    def test_candidate_contract_refresh_preserves_retry_transaction(self) -> None:
        label = "lem:claim"
        retry_key = f"phase1_statement:{label}"
        candidate = {"code": "retained candidate"}
        exchange = {"labels": [label], "status": "failed"}
        ctx = SimpleNamespace(
            name="candidate-refresh-regression",
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            semantic_plan_entries={
                label: {"representation": "exact", "obligations": []}
            },
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "statement-v1",
                    "target_signature": "theorem lem_claim : True",
                    "helpers": [],
                    "decisions": [],
                    "origin": "phase1_candidate",
                }
            },
            design_plan_alternates={},
            design_plan="",
            blueprint_direct_generation={},
            generation_candidates={label: candidate},
            retry_lifecycle={
                retry_key: {
                    "label": label,
                    "stage": "phase1_statement",
                    "statement_fp": "statement-v1",
                    "state": "escalation",
                    "failures": 1,
                }
            },
            phase1_exchange_history={"exchange-v1": exchange},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            telemetry=FakeTelemetry(),
        )
        canonical = CanonicalModelModule(
            ParsedModule(
                [],
                [],
                [
                    DeclBlock(
                        "theorem",
                        "lem_claim",
                        "theorem lem_claim : Nat = Nat := sorry",
                    )
                ],
            ),
            {0: label},
        )

        realized = _realize_typed_contracts_from_candidate(
            ctx, [label], canonical
        )

        self.assertEqual(realized, {label})
        self.assertIs(ctx.generation_candidates[label], candidate)
        self.assertIs(ctx.phase1_exchange_history["exchange-v1"], exchange)
        self.assertEqual(ctx.retry_lifecycle[retry_key]["state"], "escalation")
        self.assertEqual(ctx.retry_lifecycle[retry_key]["failures"], 1)
        self.assertEqual(
            ctx.design_plan_entries[label]["target_signature"],
            "theorem lem_claim : Nat = Nat",
        )
        refresh = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_candidate_contract_refreshed"
        ]
        self.assertEqual(len(refresh), 1)
        self.assertTrue(refresh[0]["retry_lifecycle_preserved"])

    def test_targeted_patch_canonicalizes_against_owner_component(self) -> None:
        accepted = "def:accepted"
        rejected = "lem:rejected"
        labels = [accepted, rejected]
        parsed = _parse_module(
            "def def_accepted : Nat := sorry\n\n"
            "theorem lem_rejected : True := sorry\n"
        )
        corrected = _parse_module(
            "theorem lem_rejected : def_accepted = def_accepted := sorry\n"
        )
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            base_effort="medium",
            escalation_effort="high",
            hard_timeout=60,
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )
        finding = SkeletonFinding(
            "the rejected declaration needs its accepted sibling",
            label=rejected,
            lean_name="lem_rejected",
        )
        canonical = CanonicalModelModule(corrected, {0: rejected})

        with patch(
            "formalize_blueprint._targeted_skeleton_patch_prompt",
            return_value="prompt",
        ), patch(
            "formalize_blueprint._phase1_exchange_start",
            return_value="exchange",
        ), patch(
            "formalize_blueprint._phase1_exchange_finish",
            return_value=False,
        ), patch(
            "formalize_blueprint._call_model",
            return_value=CallResult(status="ok", text="corrected Lean"),
        ), patch(
            "formalize_blueprint._ingest_model_lean",
            return_value=canonical,
        ) as ingest, patch(
            "formalize_blueprint._planned_helper_owner_by_name",
            return_value={},
        ), patch(
            "formalize_blueprint._apply_skeleton_replacements",
            return_value=parsed,
        ):
            patched, note = _targeted_patch_skeleton_decls(
                ctx,
                labels,
                [],
                [],
                parsed,
                "existing module",
                [finding],
                timeout=30,
            )

        self.assertIs(patched, parsed)
        self.assertEqual(note, "patched")
        self.assertEqual(ingest.call_args.args[1], labels)

    def test_empty_skeleton_findings_do_not_emit_empty_bullet_feedback(self) -> None:
        self.assertEqual(_format_skeleton_findings([]), "")

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

    def test_phase2_is_a_one_way_milestone_for_contract_repairs(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"def:a": node("def:a"), "lem:b": node("lem:b")},
            telemetry=telemetry,
            phase2_started=False,
            phase1_baseline_labels=set(),
        )
        section = Section(
            1,
            ["def:a", "lem:b"],
            Path("Skeleton01.lean"),
            "AutoBlueprint.Generated.Paper.Skeleton01",
            [],
        )

        self.assertTrue(_begin_phase2(ctx, [section]))
        self.assertEqual(ctx.phase1_baseline_labels, {"def:a", "lem:b"})
        self.assertEqual(_contract_work_stage(ctx), "Phase 2 whole-node repair")

        ctx.nodes["lem:helper"] = node("lem:helper")
        self.assertFalse(_begin_phase2(ctx, [section]))
        self.assertEqual(ctx.phase1_baseline_labels, {"def:a", "lem:b"})
        self.assertEqual(
            [name for name, _fields in telemetry.events], ["phase2_started"]
        )

    def test_phase2_whole_node_repair_does_not_regress_phase1_progress(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={
                "def:a": node("def:a"),
                "lem:b": node("lem:b"),
                "lem:new-helper": node("lem:new-helper"),
            },
            telemetry=telemetry,
            phase2_started=True,
            phase1_baseline_labels={"def:a", "lem:b"},
        )
        with patch(
            "formalize_blueprint._frozen_labels", return_value={"def:a", "lem:b"}
        ), patch(
            "formalize_blueprint._phase2_body_progress", return_value=(set(), {"lem:b"})
        ), patch(
            "formalize_blueprint._verified_node_labels", return_value={"def:a"}
        ), patch(
            "formalize_blueprint._recorded_conjecture_labels", return_value=set()
        ):
            output = io.StringIO()
            with redirect_stdout(output):
                _print_pipeline_progress(ctx, [], 4, 100)

        self.assertIn("Phase 1 contracts 2/2 frozen", output.getvalue())
        event, fields = telemetry.events[-1]
        self.assertEqual(event, "pipeline_progress")
        self.assertEqual(fields["workflow_phase"], "phase2")
        self.assertEqual(
            fields["phase2_whole_node_pending_labels"], ["lem:new-helper"]
        )

    def test_phase2_pending_work_cannot_reopen_phase1(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["whole_node_repair_regression"]
        ctx = SimpleNamespace(phase2_started=fixture["phase2_started"])
        sections: list[Section] = []
        pending = set(fixture["pending_labels"])
        with patch(
            "formalize_blueprint._run_phase2_whole_node_repairs",
            return_value=sections,
        ) as whole_node, patch(
            "formalize_blueprint._run_phase1"
        ) as phase1:
            result = _run_pending_declaration_work(
                ctx, sections, pending
            )

        self.assertIs(result, sections)
        whole_node.assert_called_once_with(
            ctx, sections, pending
        )
        phase1.assert_not_called()

        with self.assertRaisesRegex(RuntimeError, "cannot run after Phase 2"):
            _run_phase1(ctx, sections, pending, PHASE1_STATEMENT_ORDER)

    def test_phase2_whole_node_transaction_keeps_complete_body(self) -> None:
        label = "lem:changed"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement"},
            contract_fps={label: "contract"},
            base_timeout=120,
            hard_timeout=300,
            base_effort=None,
            escalation_effort=None,
            telemetry=FakeTelemetry(),
        )
        completed = Section(
            2,
            [label],
            Path("Skeleton02.lean"),
            "AutoBlueprint.Generated.Paper.Skeleton02",
            [],
        )
        response = "```lean\ntheorem lem_changed : True := by trivial\n```"
        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._generation_feedback_for", return_value=""
        ), patch(
            "formalize_blueprint._phase2_whole_node_prompt", return_value="prompt"
        ), patch(
            "formalize_blueprint._call_model",
            return_value=CallResult(status="ok", text=response),
        ), patch(
            "formalize_blueprint._freeze_section_from_code",
            return_value=[completed],
        ) as freeze:
            result = _run_phase2_whole_node_transaction(
                ctx, label, [], _SectionNumberAllocator(2)
            )

        self.assertEqual(result, [completed])
        self.assertTrue(freeze.call_args.kwargs["complete_bodies"])
        self.assertFalse(freeze.call_args.kwargs["allow_patch"])

    def test_phase2_reject_keeps_candidate_and_corrects_complete_node(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "simplex_complete_node_candidate_loop.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement"},
            contract_fps={label: "contract"},
            tex_blocks={label: "blueprint proof"},
            base_timeout=300,
            hard_timeout=600,
            base_effort="medium",
            escalation_effort="high",
            runner_spec="codex:gpt-5.5",
            escalation_runner_spec="codex:gpt-5.5",
            telemetry=telemetry,
            phase2_node_candidates={},
            generation_feedback={},
        )
        completed = Section(
            2,
            [label],
            Path("Skeleton02.lean"),
            "AutoBlueprint.Generated.Paper.Skeleton02",
            [],
        )
        first = "```lean\ntheorem lem_changed : True := by simp\n```"
        corrected = "```lean\ntheorem lem_changed : True := by trivial\n```"
        exact_error = fixture["exact_lean_failure"]

        def freeze_side_effect(*_args, **kwargs):
            if freeze.call_count == 1:
                kwargs["failure_evidence"].append(exact_error)
                kwargs["failure_candidate_code"].append(
                    "theorem lem_changed : True := by simp"
                )
                return None
            return [completed]

        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._generation_feedback_for", return_value=""
        ), patch(
            "formalize_blueprint._phase2_whole_node_prompt", return_value="generate"
        ), patch(
            "formalize_blueprint._phase2_complete_node_correction_prompt",
            return_value="correct exact candidate",
        ), patch(
            "formalize_blueprint._call_model",
            side_effect=[
                CallResult(status="ok", text=first),
                CallResult(status="ok", text=corrected),
            ],
        ) as call_model, patch(
            "formalize_blueprint._freeze_section_from_code",
            side_effect=freeze_side_effect,
        ) as freeze:
            result = _run_phase2_whole_node_transaction(
                ctx, label, [], _SectionNumberAllocator(2)
            )

        self.assertEqual(result, [completed])
        self.assertEqual(call_model.call_count, 2)
        self.assertEqual(
            [call.kwargs["purpose"] for call in call_model.call_args_list],
            ["phase2_whole_node_repair", "phase2_complete_node_correction"],
        )
        self.assertNotIn("sessions", call_model.call_args_list[1].kwargs)
        self.assertIsNone(_phase2_node_candidate(ctx, label))
        self.assertTrue(
            any(
                name == "phase2_complete_candidate_saved"
                and fields["failure_kind"] == "lean_compile"
                for name, fields in telemetry.events
            )
        )

    def test_phase2_outer_retry_starts_from_retained_complete_candidate(self) -> None:
        label = "lem:changed"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement"},
            contract_fps={label: "contract"},
            tex_blocks={label: "blueprint proof"},
            base_timeout=300,
            hard_timeout=600,
            base_effort="medium",
            escalation_effort="high",
            runner_spec="codex:gpt-5.5",
            escalation_runner_spec="codex:gpt-5.5",
            telemetry=telemetry,
            phase2_node_candidates={},
            generation_feedback={},
        )
        _store_phase2_node_candidate(
            ctx,
            label,
            "theorem lem_changed : True := by simp",
            evidence="Lean rejected delivered statements:\nexact local error",
            failure_kind="lean_compile",
            tier="base",
            source="historical_replay",
        )
        completed = Section(
            2,
            [label],
            Path("Skeleton02.lean"),
            "AutoBlueprint.Generated.Paper.Skeleton02",
            [],
        )
        corrected = "```lean\ntheorem lem_changed : True := by trivial\n```"
        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._phase2_complete_node_correction_prompt",
            return_value="correct retained candidate",
        ) as correction_prompt, patch(
            "formalize_blueprint._phase2_whole_node_prompt"
        ) as generation_prompt, patch(
            "formalize_blueprint._call_model",
            return_value=CallResult(status="ok", text=corrected),
        ) as call_model, patch(
            "formalize_blueprint._freeze_section_from_code",
            return_value=[completed],
        ):
            result = _run_phase2_whole_node_transaction(
                ctx, label, [], _SectionNumberAllocator(2)
            )

        self.assertEqual(result, [completed])
        correction_prompt.assert_called_once()
        generation_prompt.assert_not_called()
        self.assertEqual(
            call_model.call_args.kwargs["purpose"],
            "phase2_complete_node_correction",
        )
        self.assertEqual(call_model.call_args.kwargs["timeout"], 300)

    def test_broad_mathlib_retry_is_limited_to_missing_names(self) -> None:
        self.assertTrue(
            _lean_failure_may_be_fixed_by_broad_mathlib(
                "error: unknown identifier 'Continuous.min'"
            )
        )
        for diagnostic in (
            "error: type mismatch",
            "error: maximum heartbeats exceeded",
            "error: no goals to be solved",
        ):
            self.assertFalse(
                _lean_failure_may_be_fixed_by_broad_mathlib(diagnostic)
            )

    def test_missing_lean_surface_names_preserve_qualified_identifiers(self) -> None:
        self.assertEqual(
            _missing_lean_surface_names(
                "error: unknown identifier 'Continuous.min'\n"
                "error: Unknown constant `Real.logb`"
            ),
            ["Continuous.min", "Real.logb"],
        )

    def test_specific_import_resolution_prefixes_library_source_root(self) -> None:
        ctx = SimpleNamespace(name="paper")
        candidate = SimpleNamespace(
            library="CSLib",
            module="Data.Graph.Basic",
            declaration="reachable",
        )
        with patch(
            "formalize_blueprint._blueprint_library_preference",
            return_value=["cslib"],
        ), patch(
            "formalize_blueprint._library_roots", return_value=[]
        ), patch(
            "formalize_blueprint._rg_library_candidates",
            return_value=[candidate],
        ):
            modules = _specific_import_modules_for_missing_names(
                ctx, "error: unknown identifier 'Graph.reachable'"
            )

        self.assertEqual(modules, ["CSLib.Data.Graph.Basic"])

    def test_successful_broad_diagnosis_persists_specific_imports(self) -> None:
        label = "def:logarithm"
        missing = "error: unknown identifier 'Real.logb'"
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "Skeleton01.lean"
            ctx = SimpleNamespace(
                name="paper",
                nodes={label: node(label)},
                lean_command=["lean"],
                telemetry=FakeTelemetry(),
                unavailable_imports=set(),
                defer_phase1_alignment=True,
                design_plan_entries={},
                semantic_plan_entries={},
                stmt_fps={label: "statement"},
                retry_lifecycle={},
            )
            with patch(
                "formalize_blueprint._section_module",
                return_value=("Generated.Skeleton01", path),
            ), patch(
                "formalize_blueprint._sections_for_deps", return_value=[]
            ), patch(
                "formalize_blueprint._skeleton_code_findings",
                return_value=[],
            ), patch(
                "formalize_blueprint._skeleton_deterministic_findings",
                return_value=[],
            ), patch(
                "formalize_blueprint._compile_module_olean",
                side_effect=[
                    LeanAttempt(ok=False, command=["lean"], reason=missing),
                    LeanAttempt(ok=True, command=["lean"]),
                    LeanAttempt(ok=True, command=["lean"]),
                ],
            ) as check, patch(
                "formalize_blueprint._section_objects_exist",
                return_value=True,
            ), patch(
                "formalize_blueprint._specific_import_modules_for_missing_names",
                return_value=["Mathlib.Analysis.SpecialFunctions.Log.Base"],
            ):
                frozen = _freeze_section_from_code(
                    ctx,
                    [label],
                    [],
                    _SectionNumberAllocator(1),
                    ["def def_logarithm : Real := Real.logb 2 8"],
                    [],
                    [],
                    defer_object_gate=True,
                )

            persisted = path.read_text(encoding="utf-8")

        self.assertIsNotNone(frozen)
        self.assertEqual(check.call_count, 3)
        self.assertIn(
            "import Mathlib.Analysis.SpecialFunctions.Log.Base", persisted
        )
        self.assertNotIn("import Mathlib\n", persisted)
        events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_environment_fallback"
        ]
        self.assertEqual(events[-1]["status"], "narrowed_without_model")

    def test_phase2_whole_node_decomposition_routes_without_escalated_generation(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["whole_node_decomposition_signal_regression"]
        label = fixture["label"]
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement"},
            contract_fps={label: "contract"},
            base_timeout=300,
            hard_timeout=600,
            base_effort="medium",
            escalation_effort="high",
            telemetry=FakeTelemetry(),
        )
        refusal = (
            "NEEDS-DECOMPOSITION: "
            + json.dumps(
                {
                    "label": label,
                    "missing_helpers": fixture["missing_helpers"],
                    "reason": "the canonical package interface is absent",
                }
            )
        )
        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._generation_feedback_for", return_value=""
        ), patch(
            "formalize_blueprint._phase2_whole_node_prompt", return_value="prompt"
        ), patch(
            "formalize_blueprint._call_model",
            return_value=CallResult(status="ok", text=refusal),
        ) as call_model:
            with self.assertRaises(RepairRequest) as raised:
                _run_phase2_whole_node_transaction(
                    ctx, label, [], _SectionNumberAllocator(2)
                )

        self.assertTrue(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(raised.exception.labels, [label])
        self.assertEqual(
            raised.exception.decomposition_helpers,
            fixture["missing_helpers"],
        )
        self.assertEqual(call_model.call_count, 1)
        event, fields = ctx.telemetry.events[-1]
        self.assertEqual(event, "phase2_whole_node_decomposition")
        self.assertTrue(fields["routed_immediately"])

    def test_phase2_generation_exhaustion_does_not_authorize_blueprint_repair(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["generation_exhaustion_classification_regression"]
        label = fixture["label"]
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement"},
            contract_fps={label: "contract"},
            base_timeout=300,
            hard_timeout=600,
            base_effort="medium",
            escalation_effort="high",
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._generation_feedback_for", return_value=""
        ), patch(
            "formalize_blueprint._phase2_whole_node_prompt", return_value="prompt"
        ), patch(
            "formalize_blueprint._call_model",
            side_effect=[
                CallResult(status="timeout", error="base call timed out"),
                CallResult(status="timeout", error=fixture["evidence"]),
            ],
        ) as call_model:
            with self.assertRaises(RepairRequest) as raised:
                _run_phase2_whole_node_transaction(
                    ctx, label, [], _SectionNumberAllocator(2)
                )

        request = raised.exception
        self.assertFalse(request.authorizes_blueprint_repair)
        self.assertFalse(
            _requires_blueprint_transaction(
                request.authorizes_blueprint_repair,
                request.required_dependencies,
            )
        )
        self.assertEqual(request.labels, [label])
        self.assertEqual(request.model_repair_labels, [])
        self.assertIn(fixture["evidence"], request.evidence_by_label[label])
        self.assertEqual(call_model.call_count, 2)
        event, fields = ctx.telemetry.events[-1]
        self.assertEqual(event, "phase2_whole_node_transaction")
        self.assertEqual(fields["route"], "bounded_generation_retry")
        self.assertFalse(fields["blueprint_edit_authorized"])

    def test_phase2_parallel_whole_node_repair_routes_authorized_failure(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["authorized_parallel_repair_regression"]
        accepted_labels = fixture["accepted_labels"]
        repair_label = fixture["repair_label"]
        accepted_sections = {
            label: Section(
                index,
                [label],
                Path(f"Skeleton{index:02d}.lean"),
                f"AutoBlueprint.Generated.Paper.Skeleton{index:02d}",
                [],
            )
            for index, label in enumerate(accepted_labels, 2)
        }
        ctx = SimpleNamespace(
            nodes={
                **{label: node(label) for label in accepted_labels},
                repair_label: node(repair_label),
            },
            workers=3,
        )
        sections: list[Section] = []

        def complete_or_repair(_ctx, label, _sections, _alloc):
            if label in accepted_sections:
                return [accepted_sections[label]]
            raise RepairRequest(
                "the blueprint proof needs an additional helper",
                [repair_label],
                section_labels=[repair_label],
                authorizes_blueprint_repair=True,
            )

        with patch(
            "formalize_blueprint._run_phase2_whole_node_transaction",
            side_effect=complete_or_repair,
        ), patch("formalize_blueprint._save_ctx_state"):
            with self.assertRaises(RepairRequest) as raised:
                _run_phase2_whole_node_repairs(
                    ctx,
                    sections,
                    {*accepted_labels, repair_label},
                )

        self.assertTrue(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(raised.exception.labels, [repair_label])
        self.assertEqual(
            {label for section in sections for label in section.labels},
            set(accepted_labels),
        )

    def test_phase2_parallel_authorized_failures_remain_independent(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["independent_repair_queue_regression"]
        accepted_labels = fixture["accepted_labels"]
        failed_labels = fixture["independent_failure_labels"]
        all_labels = [*accepted_labels, *failed_labels]
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in all_labels},
            stmt_fps={label: f"fp:{label}" for label in all_labels},
            workers=3,
            telemetry=telemetry,
            phase2_repair_queue=[],
        )
        sections: list[Section] = []

        def complete_or_repair(_ctx, label, _sections, _alloc):
            if label in accepted_labels:
                index = accepted_labels.index(label) + 2
                return [
                    Section(
                        index,
                        [label],
                        Path(f"Skeleton{index:02d}.lean"),
                        f"Generated.Skeleton{index:02d}",
                        [],
                    )
                ]
            raise RepairRequest(
                f"exact independent evidence for {label}",
                [label],
                section_labels=[label],
                authorizes_blueprint_repair=True,
            )

        with patch(
            "formalize_blueprint._run_phase2_whole_node_transaction",
            side_effect=complete_or_repair,
        ), patch("formalize_blueprint._save_ctx_state"):
            with self.assertRaises(RepairRequest) as raised:
                _run_phase2_whole_node_repairs(ctx, sections, set(all_labels))

        self.assertEqual(
            [payload["labels"] for payload in ctx.phase2_repair_queue],
            fixture["expected_queue_scopes"],
        )
        self.assertEqual(raised.exception.labels, fixture["expected_queue_scopes"][0])
        self.assertEqual(
            {label for section in sections for label in section.labels},
            set(accepted_labels),
        )
        first_id = raised.exception.queue_id
        _complete_phase2_repair_request(ctx, first_id)
        self.assertEqual(
            _pending_phase2_repair_request(ctx).labels,
            fixture["expected_queue_scopes"][1],
        )
        queued_event = next(
            fields
            for name, fields in telemetry.events
            if name == "phase2_repair_queue_enqueued"
        )
        self.assertEqual(queued_event["aggregation"], "independent")

    def test_phase2_repair_queue_waits_for_active_lean_verification(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["transactional_repair_verification_regression"]
        labels = fixture["queued_labels"]
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            name="phase2-queue-verification-regression",
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp:{label}" for label in labels},
            telemetry=telemetry,
            phase2_repair_queue=[],
            phase2_repair_active={},
        )
        requests = [
            RepairRequest(
                f"exact evidence for {label}",
                [label],
                authorizes_blueprint_repair=True,
            )
            for label in labels
        ]
        with tempfile.TemporaryDirectory() as tmp, patch(
            "formalize_blueprint.SCRATCH_DIR", Path(tmp)
        ), patch("formalize_blueprint._call_model") as model_call:
            _enqueue_phase2_repair_requests(ctx, requests)
            first = _pending_phase2_repair_request(ctx)
            self.assertIsNotNone(first)
            _activate_phase2_repair_request(ctx, first.queue_id)
            snapshot = _phase2_repair_transaction_dir(ctx.name, first.queue_id)
            snapshot.mkdir(parents=True)
            (snapshot / "manifest.json").write_text("{}\n", encoding="utf-8")
            _mark_phase2_repair_verifying(ctx, first.queue_id, [labels[0]])

            # No later blueprint edit becomes eligible while replacement Lean
            # for the first edit is still pending.
            self.assertIsNone(_pending_phase2_repair_request(ctx))
            self.assertEqual(
                ctx.phase2_repair_active["stage"], fixture["blocked_stage"]
            )
            self.assertEqual(len(ctx.phase2_repair_queue), len(labels))

            _complete_phase2_repair_request(ctx, first.queue_id)
            second = _pending_phase2_repair_request(ctx)
            self.assertIsNotNone(second)
            self.assertEqual(second.labels, [labels[1]])
            self.assertEqual(ctx.phase2_repair_active, {})
            model_call.assert_not_called()

    def test_phase2_repair_snapshot_restores_every_mutable_artifact(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scratch = root / "scratch"
            draft = root / "draft"
            content = draft / "blueprint" / "src" / "content.tex"
            generated = root / "generated"
            lake_generated = root / "lake-generated"
            content.parent.mkdir(parents=True)
            content.write_text("baseline blueprint\n", encoding="utf-8")
            generated.mkdir()
            (generated / "Skeleton01.lean").write_text(
                "baseline Lean\n", encoding="utf-8"
            )
            lake_generated.mkdir()
            (lake_generated / "Skeleton01.olean").write_bytes(b"baseline object")
            state = scratch / "sample" / "skeleton_state.json"
            state.parent.mkdir(parents=True)
            state.write_text('{"baseline": true}\n', encoding="utf-8")
            ctx = SimpleNamespace(
                name="sample",
                blueprint_dir=draft,
                content_path=content,
                telemetry=FakeTelemetry(),
                phase2_repair_active={
                    "request_id": "a" * 64,
                    "labels": ["lem:root"],
                },
            )

            with patch("formalize_blueprint.SCRATCH_DIR", scratch), patch(
                "formalize_blueprint._generated_module_dir",
                return_value=generated,
            ), patch(
                "formalize_blueprint._generated_lake_module_dir",
                return_value=lake_generated,
            ):
                _begin_phase2_repair_transaction(ctx, "a" * 64)
                content.write_text("unverified helper forest\n", encoding="utf-8")
                (generated / "Skeleton01.lean").write_text(
                    "unverified Lean\n", encoding="utf-8"
                )
                (generated / "Skeleton99.lean").write_text(
                    "provisional helper\n", encoding="utf-8"
                )
                (lake_generated / "Skeleton99.olean").write_bytes(b"provisional")
                state.write_text('{"mutated": true}\n', encoding="utf-8")

                _restore_phase2_repair_transaction_files(ctx, "a" * 64)

                self.assertEqual(content.read_text(encoding="utf-8"), "baseline blueprint\n")
                self.assertEqual(
                    (generated / "Skeleton01.lean").read_text(encoding="utf-8"),
                    "baseline Lean\n",
                )
                self.assertFalse((generated / "Skeleton99.lean").exists())
                self.assertFalse((lake_generated / "Skeleton99.olean").exists())
                self.assertEqual(
                    state.read_text(encoding="utf-8"), '{"baseline": true}\n'
                )
                live_state = {
                    "new_evidence": "retain me",
                    "scheduler": {
                        "phase2_repair_active": {
                            "request_id": "a" * 64,
                            "stage": "repair",
                        }
                    },
                }
                state.write_text(json.dumps(live_state), encoding="utf-8")
                content.write_text("partial agent edit\n", encoding="utf-8")
                self.assertEqual(
                    _restore_interrupted_phase2_repair("sample", draft),
                    "a" * 64,
                )
                self.assertEqual(
                    content.read_text(encoding="utf-8"), "baseline blueprint\n"
                )
                self.assertEqual(
                    json.loads(state.read_text(encoding="utf-8"))["new_evidence"],
                    "retain me",
                )
                _discard_phase2_repair_transaction("sample", "a" * 64)

    def test_direct_phase2_decomposition_snapshots_before_repair(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "simplex_direct_repair_snapshot.json"
            ).read_text(encoding="utf-8")
        )
        root_label = fixture["root_label"]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scratch = root / "scratch"
            draft = root / "draft"
            content = draft / "blueprint" / "src" / "content.tex"
            content.parent.mkdir(parents=True)
            content.write_text(fixture["baseline_blueprint"], encoding="utf-8")
            generated = root / "generated"
            generated.mkdir()
            (generated / "Skeleton01.lean").write_text(
                "theorem root : True := by sorry\n", encoding="utf-8"
            )
            lake_generated = root / "lake-generated"
            lake_generated.mkdir()
            telemetry = FakeTelemetry()
            ctx = SimpleNamespace(
                name="simplex-direct-transaction-regression",
                blueprint_dir=draft,
                content_path=content,
                nodes={root_label: node(root_label)},
                stmt_fps={root_label: "root-v1"},
                stmt_blocks={root_label: fixture["blueprint_statement"]},
                telemetry=telemetry,
                phase2_repair_queue=[],
                phase2_repair_active={},
                generation_feedback={},
            )
            outcome = SectionProofOutcome(
                section=Section(
                    1,
                    [root_label],
                    generated / "Skeleton01.lean",
                    "Generated.Skeleton01",
                    [],
                ),
                decomposition={root_label: fixture["decomposition_helpers"]},
                decomposition_evidence={
                    root_label: fixture["decomposition_evidence"]
                },
            )
            request = _route_phase2_proof_outcomes(ctx, [outcome])
            self.assertIsNotNone(request)

            state = scratch / ctx.name / "skeleton_state.json"

            def persist_active_state(_ctx, _sections):
                state.parent.mkdir(parents=True, exist_ok=True)
                state.write_text(
                    json.dumps(
                        {
                            "scheduler": {
                                "phase2_repair_active": copy.deepcopy(
                                    ctx.phase2_repair_active
                                ),
                                "phase2_repair_queue": copy.deepcopy(
                                    ctx.phase2_repair_queue
                                ),
                            }
                        }
                    ),
                    encoding="utf-8",
                )

            with patch("formalize_blueprint.SCRATCH_DIR", scratch), patch(
                "formalize_blueprint._generated_module_dir",
                return_value=generated,
            ), patch(
                "formalize_blueprint._generated_lake_module_dir",
                return_value=lake_generated,
            ), patch(
                "formalize_blueprint._save_ctx_state",
                side_effect=persist_active_state,
            ):
                request_id = _start_phase2_repair_transaction(ctx, [], request)
                snapshot = _phase2_repair_transaction_dir(ctx.name, request_id)
                self.assertTrue((snapshot / "manifest.json").is_file())

                content.write_text(
                    fixture["provisional_blueprint"], encoding="utf-8"
                )
                _mark_phase2_repair_verifying(
                    ctx, request_id, fixture["provisional_labels"]
                )
                _restore_phase2_repair_transaction_files(ctx, request_id)

                self.assertEqual(
                    content.read_text(encoding="utf-8"),
                    fixture["baseline_blueprint"],
                )
                snapshot_event = [
                    fields
                    for event, fields in telemetry.events
                    if event == "phase2_repair_transaction_snapshot"
                ]
                self.assertEqual(len(snapshot_event), 1)
                self.assertEqual(snapshot_event[0]["request_id"], request_id)

    def test_reactivated_phase2_request_replaces_stale_snapshot(self) -> None:
        """A reused diagnosis ID must snapshot its new activation baseline."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scratch = root / "scratch"
            draft = root / "draft"
            content = draft / "blueprint" / "src" / "content.tex"
            content.parent.mkdir(parents=True)
            content.write_text("old lifecycle baseline\n", encoding="utf-8")
            generated = root / "generated"
            generated.mkdir()
            lake_generated = root / "lake-generated"
            lake_generated.mkdir()
            telemetry = FakeTelemetry()
            label = "lem:root"
            ctx = SimpleNamespace(
                name="simplex-reactivated-transaction-regression",
                blueprint_dir=draft,
                content_path=content,
                nodes={label: node(label)},
                stmt_fps={label: "root-v1"},
                telemetry=telemetry,
                phase2_repair_queue=[],
                phase2_repair_active={},
            )
            request = RepairRequest(
                "the node requires decomposition",
                [label],
                authorizes_blueprint_repair=True,
            )
            _enqueue_phase2_repair_requests(ctx, [request])
            queued = _pending_phase2_repair_request(ctx)
            self.assertIsNotNone(queued)
            state = scratch / ctx.name / "skeleton_state.json"

            def persist_active_state(_ctx, _sections):
                state.parent.mkdir(parents=True, exist_ok=True)
                state.write_text(
                    json.dumps(
                        {
                            "scheduler": {
                                "phase2_repair_active": copy.deepcopy(
                                    ctx.phase2_repair_active
                                ),
                                "phase2_repair_queue": copy.deepcopy(
                                    ctx.phase2_repair_queue
                                ),
                            }
                        }
                    ),
                    encoding="utf-8",
                )

            with patch("formalize_blueprint.SCRATCH_DIR", scratch), patch(
                "formalize_blueprint._generated_module_dir",
                return_value=generated,
            ), patch(
                "formalize_blueprint._generated_lake_module_dir",
                return_value=lake_generated,
            ), patch(
                "formalize_blueprint._save_ctx_state",
                side_effect=persist_active_state,
            ):
                # Reproduce a content-derived request ID whose directory
                # survived an earlier lifecycle.
                persist_active_state(ctx, [])
                ctx.phase2_repair_active = {
                    "request_id": queued.queue_id,
                    "stage": "repair",
                    "labels": [label],
                    "verification_labels": [],
                }
                _begin_phase2_repair_transaction(ctx, queued.queue_id)
                ctx.phase2_repair_active = {}

                content.write_text("new activation baseline\n", encoding="utf-8")
                request_id = _start_phase2_repair_transaction(ctx, [], queued)
                content.write_text("rejected provisional edit\n", encoding="utf-8")
                _mark_phase2_repair_verifying(ctx, request_id, [label])
                _restore_phase2_repair_transaction_files(ctx, request_id)

                self.assertEqual(
                    content.read_text(encoding="utf-8"),
                    "new activation baseline\n",
                )
                snapshots = [
                    fields
                    for event, fields in telemetry.events
                    if event == "phase2_repair_transaction_snapshot"
                    and fields["request_id"] == request_id
                ]
                self.assertEqual(len(snapshots), 2)

    def test_phase2_verification_rejects_missing_transaction_snapshot(self) -> None:
        label = "lem:root"
        request_id = "b" * 64
        ctx = SimpleNamespace(
            name="simplex-missing-transaction-regression",
            nodes={label: node(label)},
            telemetry=FakeTelemetry(),
            phase2_repair_queue=[
                {"request_id": request_id, "labels": [label]}
            ],
            phase2_repair_active={
                "request_id": request_id,
                "stage": "repair",
                "labels": [label],
                "verification_labels": [],
            },
        )
        with tempfile.TemporaryDirectory() as tmp, patch(
            "formalize_blueprint.SCRATCH_DIR", Path(tmp)
        ):
            with self.assertRaisesRegex(
                RuntimeError, "without its pre-edit transaction snapshot"
            ):
                _mark_phase2_repair_verifying(ctx, request_id, [label])

    def test_caught_phase2_request_creates_snapshot_before_activation_returns(self) -> None:
        case = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "provider_contract_ownership.json"
            ).read_text(encoding="utf-8")
        )["cases"][0]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            scratch = root / "scratch"
            draft = root / "draft"
            content = draft / "blueprint" / "src" / "content.tex"
            content.parent.mkdir(parents=True)
            content.write_text("baseline blueprint\n", encoding="utf-8")
            generated = root / "generated"
            generated.mkdir()
            lake_generated = root / "lake-generated"
            lake_generated.mkdir()
            label = case["repair_labels"][0]
            ctx = SimpleNamespace(
                name="caught-request-snapshot-regression",
                blueprint_dir=draft,
                content_path=content,
                nodes={label: node(label)},
                stmt_fps={label: "caught-v1"},
                telemetry=FakeTelemetry(),
                phase2_repair_queue=[],
                phase2_repair_active={},
            )
            request = RepairRequest(
                "exact Phase 2 repair evidence",
                [label],
                authorizes_blueprint_repair=True,
            )
            _enqueue_phase2_repair_requests(ctx, [request])
            queued = _pending_phase2_repair_request(ctx)
            self.assertIsNotNone(queued)
            assert queued is not None

            def persist_active_state(_ctx, _sections):
                state = scratch / ctx.name / "skeleton_state.json"
                state.parent.mkdir(parents=True, exist_ok=True)
                state.write_text(
                    json.dumps(
                        {
                            "scheduler": {
                                "phase2_repair_active": copy.deepcopy(
                                    ctx.phase2_repair_active
                                ),
                                "phase2_repair_queue": copy.deepcopy(
                                    ctx.phase2_repair_queue
                                ),
                            }
                        }
                    ),
                    encoding="utf-8",
                )

            with patch("formalize_blueprint.SCRATCH_DIR", scratch), patch(
                "formalize_blueprint._generated_module_dir",
                return_value=generated,
            ), patch(
                "formalize_blueprint._generated_lake_module_dir",
                return_value=lake_generated,
            ), patch(
                "formalize_blueprint._save_ctx_state",
                side_effect=persist_active_state,
            ):
                request_id = _start_caught_phase2_repair_transaction(
                    ctx, [], queued
                )

            self.assertEqual(request_id, queued.queue_id)
            self.assertEqual(case["expected_activation_gate"], "start_phase2_repair_transaction")
            self.assertTrue(
                (
                    scratch
                    / ctx.name
                    / "phase2-repair-transactions"
                    / request_id
                    / "manifest.json"
                ).is_file()
            )

    def test_provider_contract_defect_rolls_back_consumer_and_queues_provider(self) -> None:
        case = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "provider_contract_ownership.json"
            ).read_text(encoding="utf-8")
        )["cases"][1]
        consumer = case["consumer"]
        provider = case["provider"]
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            name="provider-reroute-regression",
            nodes={
                consumer: node(consumer, uses={provider}),
                provider: node(provider),
            },
            stmt_fps={consumer: "consumer-v1", provider: "provider-v1"},
            telemetry=telemetry,
            phase2_repair_queue=[],
            phase2_repair_active={},
            repair_boundary_pending={"mode": "repair"},
            lean_command=["lake", "env", "lean"],
        )
        original = RepairRequest(
            "consumer repair evidence",
            [consumer],
            authorizes_blueprint_repair=True,
        )
        _enqueue_phase2_repair_requests(ctx, [original])
        queued = _pending_phase2_repair_request(ctx)
        self.assertIsNotNone(queued)
        assert queued is not None
        _activate_phase2_repair_request(ctx, queued.queue_id)
        ctx.phase2_repair_active["stage"] = "verify"
        snapshotted_queue = copy.deepcopy(ctx.phase2_repair_queue)
        diagnosis = RepairRequest(
            "The provider lacks the affine-independent cell contract.",
            [provider],
            authorizes_blueprint_repair=True,
            model_repair_labels=[provider],
            provider_contract_labels=[provider],
            reschedule_labels=[consumer],
        )
        baseline_sections = [
            Section(1, [provider], Path("Skeleton01.lean"), "Generated.S01", [])
        ]

        def refresh_nodes(nodes):
            ctx.nodes = nodes
            ctx.stmt_fps = {consumer: "consumer-v1", provider: "provider-v1"}

        def load_snapshot(_ctx, _lean_command):
            ctx.phase2_repair_queue = copy.deepcopy(snapshotted_queue)
            ctx.phase2_repair_active = {
                "request_id": queued.queue_id,
                "stage": "repair",
                "labels": [consumer],
                "verification_labels": [],
            }
            return baseline_sections

        ctx.refresh_nodes = refresh_nodes
        with patch(
            "formalize_blueprint._restore_phase2_repair_transaction_files"
        ) as restore, patch(
            "formalize_blueprint._validate_draft",
            return_value=SimpleNamespace(
                ok=True,
                nodes={
                    consumer: node(consumer, uses={provider}),
                    provider: node(provider),
                },
            ),
        ), patch(
            "formalize_blueprint._load_state", side_effect=load_snapshot
        ), patch(
            "formalize_blueprint._save_ctx_state"
        ), patch(
            "formalize_blueprint._discard_phase2_repair_transaction"
        ):
            restored = _reroute_active_phase2_repair_to_provider(
                ctx, [], diagnosis
            )

        restore.assert_called_once_with(ctx, queued.queue_id)
        self.assertEqual(restored, baseline_sections)
        self.assertEqual(ctx.phase2_repair_active, {})
        self.assertEqual(len(ctx.phase2_repair_queue), 1)
        self.assertEqual(ctx.phase2_repair_queue[0]["labels"], [provider])
        self.assertEqual(ctx.repair_boundary_pending, {})
        rerouted = [
            fields
            for event, fields in telemetry.events
            if event == "phase2_repair_rerouted_to_provider"
        ]
        self.assertEqual(len(rerouted), 1)
        self.assertEqual(rerouted[0]["provider_labels"], [provider])
        self.assertEqual(rerouted[0]["rescheduled_consumer_labels"], [consumer])
        self.assertEqual(
            case["expected_action"],
            "rollback_consumer_then_queue_provider_transaction",
        )

    def test_failed_phase2_component_retries_original_roots_from_snapshot(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["provisional_component_rollback_regression"]
        root_label = fixture["original_root"]
        provisional_label = fixture["provisional_helper_labels"][0]
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            name="simplex-transaction-regression",
            nodes={root_label: node(root_label)},
            stmt_fps={root_label: "root-v1"},
            telemetry=telemetry,
            phase2_repair_queue=[],
            phase2_repair_active={},
            lean_command=["lake", "env", "lean"],
        )
        original = RepairRequest(
            fixture["original_evidence"],
            [root_label],
            decomposition_helpers=fixture["original_helpers"],
            authorizes_blueprint_repair=True,
        )
        _enqueue_phase2_repair_requests(ctx, [original])
        queued = _pending_phase2_repair_request(ctx)
        self.assertIsNotNone(queued)
        _activate_phase2_repair_request(ctx, queued.queue_id)
        snapshotted_queue = copy.deepcopy(ctx.phase2_repair_queue)
        ctx.phase2_repair_queue[0]["evidence"] += (
            "\n\n" + fixture["prior_followup_evidence"]
        )
        ctx.phase2_repair_queue[0]["verification_owned_labels"] = [
            provisional_label
        ]
        ctx.phase2_repair_queue[0]["verification_recheck_labels"] = []
        ctx.phase2_repair_active["stage"] = "verify"
        ctx.phase2_repair_active["verification_labels"] = [provisional_label]
        followup = RepairRequest(
            fixture["followup_evidence"],
            [provisional_label],
            decomposition_helpers=fixture["followup_helpers"],
            authorizes_blueprint_repair=True,
        )
        baseline_sections = [
            Section(1, [root_label], Path("Skeleton01.lean"), "Generated.S01", [])
        ]

        def restore_nodes(nodes):
            ctx.nodes = nodes
            ctx.stmt_fps = {root_label: "root-v1"}

        def load_snapshot(_ctx, _lean_command):
            ctx.phase2_repair_queue = copy.deepcopy(snapshotted_queue)
            ctx.phase2_repair_active = {
                "request_id": queued.queue_id,
                "stage": "repair",
                "labels": [root_label],
                "verification_labels": [],
            }
            return baseline_sections

        ctx.refresh_nodes = restore_nodes
        with patch(
            "formalize_blueprint._restore_phase2_repair_transaction_files"
        ) as restore, patch(
            "formalize_blueprint._validate_draft",
            return_value=SimpleNamespace(ok=True, nodes={root_label: node(root_label)}),
        ), patch(
            "formalize_blueprint._load_state", side_effect=load_snapshot
        ), patch("formalize_blueprint._save_ctx_state"):
            restored, retry = _restart_active_phase2_repair(
                ctx, [], followup
            )

        restore.assert_called_once_with(ctx, queued.queue_id)
        self.assertEqual(restored, baseline_sections)
        self.assertEqual(retry.labels, [root_label])
        self.assertNotIn(provisional_label, retry.labels)
        self.assertEqual(
            retry.decomposition_helpers,
            [*fixture["original_helpers"], *fixture["followup_helpers"]],
        )
        self.assertIn(fixture["followup_evidence"], retry.evidence)
        self.assertIn(fixture["prior_followup_evidence"], retry.evidence)
        self.assertEqual(ctx.phase2_repair_active["stage"], "repair")
        restarted = [
            fields
            for event, fields in telemetry.events
            if event == "phase2_repair_transaction_restarted"
        ]
        self.assertEqual(len(restarted), 1)

    def test_phase2_recheck_cannot_contribute_repair_helpers(self) -> None:
        root = "lem:repair-root"
        recheck = "lem:cached-recheck"
        request_id = "repair-request"
        telemetry = FakeTelemetry()
        payload = {
            "request_id": request_id,
            "labels": [root],
            "evidence": "original repair evidence",
            "decomposition_helpers": ["original owned helper"],
            "evidence_by_label": {root: "original repair evidence"},
            "model_repair_labels": [root],
            "verification_owned_labels": [root],
            "verification_recheck_labels": [recheck],
        }
        ctx = SimpleNamespace(
            nodes={root: node(root), recheck: node(recheck)},
            stmt_fps={root: "root-v1", recheck: "recheck-v1"},
            telemetry=telemetry,
            phase2_repair_queue=[payload],
            phase2_repair_active={
                "request_id": request_id,
                "stage": "verify",
                "labels": [root],
                "verification_labels": [root, recheck],
            },
        )
        followup = RepairRequest(
            "cached declaration failed re-verification",
            [recheck],
            decomposition_helpers=["unrelated recheck helper"],
            authorizes_blueprint_repair=True,
        )
        expected = RepairRequest(
            "retry original root", [root], authorizes_blueprint_repair=True
        )

        with patch(
            "formalize_blueprint._pending_phase2_repair_request",
            return_value=expected,
        ):
            result = _merge_phase2_repair_followup(ctx, request_id, followup)

        self.assertIs(result, expected)
        self.assertEqual(payload["decomposition_helpers"], ["original owned helper"])
        scoped = [
            fields
            for event, fields in telemetry.events
            if event == "phase2_repair_followup_helpers_scoped_out"
        ]
        self.assertEqual(len(scoped), 1)
        self.assertEqual(scoped[0]["followup_labels"], [recheck])
        self.assertEqual(scoped[0]["owned_verification_labels"], [root])

    def test_phase2_queue_drops_diagnosis_after_dependency_context_changes(self) -> None:
        target = "lem:target"
        dependency = "lem:dependency"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={
                target: node(target, uses={dependency}),
                dependency: node(dependency),
            },
            stmt_fps={target: "target-v1", dependency: "dependency-v1"},
            telemetry=telemetry,
            phase2_repair_queue=[],
            phase2_repair_active={},
        )
        _enqueue_phase2_repair_requests(
            ctx,
            [
                RepairRequest(
                    "the dependency interface is insufficient",
                    [target],
                    authorizes_blueprint_repair=True,
                )
            ],
        )
        original_context = ctx.phase2_repair_queue[0]["context_fp"]
        self.assertEqual(
            original_context,
            _phase2_repair_context_fingerprint(ctx, [target]),
        )

        ctx.stmt_fps[dependency] = "dependency-v2"
        self.assertIsNone(_pending_phase2_repair_request(ctx))
        self.assertEqual(ctx.phase2_repair_queue, [])
        superseded = [
            fields
            for event, fields in telemetry.events
            if event == "phase2_repair_queue_superseded"
        ]
        self.assertEqual(len(superseded), 1)
        self.assertEqual(superseded[0]["labels"], [target])

    def test_decomposition_refusal_requires_exact_targeted_json(self) -> None:
        label = "lem:target"
        valid = (
            "NEEDS-DECOMPOSITION: "
            + json.dumps(
                {
                    "label": label,
                    "missing_helpers": ["an explicit intermediate equality"],
                    "reason": "the blueprint proof skips that equality",
                }
            )
        )
        self.assertEqual(
            _parse_decomposition_refusal(valid, expected_labels={label})["label"],
            label,
        )
        self.assertIsNone(
            _parse_decomposition_refusal(
                valid + "\nReturn Lean code after the JSON.",
                expected_labels={label},
            )
        )
        self.assertIsNone(
            _parse_decomposition_refusal(
                "NEEDS-DECOMPOSITION: {not valid JSON}",
                expected_labels={label},
            )
        )
        self.assertIsNone(
            _parse_decomposition_refusal(
                "NEEDS-DECOMPOSITION: "
                + json.dumps(
                    {
                        "label": "<node label>",
                        "missing_helpers": ["<each needed helper statement>"],
                        "reason": "<why>",
                    }
                ),
                expected_labels={label},
            )
        )
        self.assertIsNone(
            _parse_decomposition_refusal(valid, expected_labels={"lem:sibling"})
        )

    def test_phase2_frontier_decompositions_queue_independent_repairs(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["phase2_proof_frontier_explosion_regression"]
        labels = fixture["independent_failure_labels"]
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp:{label}" for label in labels},
            stmt_blocks={label: f"Blueprint statement for {label}" for label in labels},
            telemetry=telemetry,
            phase2_repair_queue=[],
            generation_feedback={},
        )
        outcomes = [
            SectionProofOutcome(
                section=Section(
                    index,
                    [label],
                    Path(f"Skeleton{index:02d}.lean"),
                    f"Generated.Skeleton{index:02d}",
                    [],
                ),
                decomposition={label: [f"helper for {label}"]},
                decomposition_evidence={label: f"exact refusal for {label}"},
            )
            for index, label in enumerate(labels, 1)
        ]

        request = _route_phase2_proof_outcomes(ctx, outcomes)

        self.assertIsNotNone(request)
        self.assertTrue(request.authorizes_blueprint_repair)
        self.assertEqual(
            [payload["labels"] for payload in ctx.phase2_repair_queue],
            fixture["expected_queue_scopes"],
        )
        self.assertEqual(request.labels, fixture["expected_queue_scopes"][0])
        self.assertTrue(
            all(len(payload["labels"]) == 1 for payload in ctx.phase2_repair_queue)
        )

    def test_phase2_frontier_generation_failure_cannot_edit_blueprint(self) -> None:
        label = "lem:ordinary-lean-failure"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "fp"},
            stmt_blocks={label: "Blueprint statement"},
            telemetry=FakeTelemetry(),
            phase2_repair_queue=[],
            generation_feedback={},
        )
        outcome = SectionProofOutcome(
            section=Section(1, [label], Path("Skeleton01.lean"), "Generated.S01", []),
            failed={label: "unknown identifier in generated Lean"},
        )

        request = _route_phase2_proof_outcomes(ctx, [outcome])

        self.assertIsNotNone(request)
        self.assertFalse(request.authorizes_blueprint_repair)
        self.assertEqual(request.labels, [label])
        self.assertEqual(ctx.phase2_repair_queue, [])

    def test_phase2_opaque_definition_routes_to_local_prerequisite(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "simplex_opaque_definition_prerequisite.json"
            ).read_text(encoding="utf-8")
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton09.lean"
            path.write_text(fixture["generated_module"], encoding="utf-8")
            labels = list(fixture["nodes"])
            section = Section(
                9,
                labels,
                path,
                "AutoBlueprint.Generated.Simplex.Skeleton09",
                [],
                refined_labels=set(labels),
            )
            ctx = SimpleNamespace(
                nodes={
                    label: node(label, uses=set(dependencies))
                    for label, dependencies in fixture["nodes"].items()
                },
                stmt_fps={label: f"fp:{label}" for label in labels},
                stmt_blocks={label: f"Blueprint statement for {label}" for label in labels},
                telemetry=FakeTelemetry(),
                phase2_repair_queue=[],
                phase2_prerequisite_labels=set(),
                generation_feedback={},
            )
            blocked = fixture["failure"]["label"]
            evidence = fixture["failure"]["evidence"]
            outcome = SectionProofOutcome(
                section=section,
                decomposition={blocked: fixture["failure"]["missing_helpers"]},
                decomposition_evidence={blocked: evidence},
            )

            request = _route_phase2_proof_outcomes(ctx, [outcome], [section])

            self.assertIsNotNone(request)
            self.assertTrue(request.scheduling_only)
            self.assertFalse(request.authorizes_blueprint_repair)
            self.assertEqual(
                request.implementation_prerequisites,
                fixture["expected"]["prerequisite_labels"],
            )
            self.assertEqual(
                ctx.phase2_prerequisite_labels,
                set(fixture["expected"]["prerequisite_labels"]),
            )
            self.assertEqual(ctx.phase2_repair_queue, [])
            self.assertEqual(
                _phase2_prerequisite_frontier(ctx, set(labels))[1],
                fixture["expected"]["prerequisite_labels"],
            )
            event_names = [name for name, _fields in ctx.telemetry.events]
            self.assertIn("phase2_definition_prerequisite_routed", event_names)

    def test_phase2_boundary_repair_uses_existing_provider_section(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "def def_provider : Nat := sorry\n\n"
                "theorem lem_consumer : def_provider = 1 := by sorry\n",
                encoding="utf-8",
            )
            labels = ["def:provider", "lem:consumer"]
            section = Section(
                1,
                labels,
                path,
                "Generated.Skeleton01",
                [],
                refined_labels=set(labels),
            )
            ctx = SimpleNamespace(
                nodes={
                    "def:provider": node("def:provider"),
                    "lem:consumer": node(
                        "lem:consumer", uses={"def:provider"}
                    ),
                },
                stmt_fps={label: f"fp:{label}" for label in labels},
                telemetry=FakeTelemetry(),
                phase2_started=True,
                phase2_prerequisite_labels=set(),
            )
            request = RepairRequest(
                "lem:consumer cannot unfold `def_provider`; its definition body "
                "is still opaque.",
                ["lem:consumer"],
                authorizes_blueprint_repair=True,
            )

            routed = _phase2_prerequisite_request_for_repair(
                ctx, [section], request, source="test_boundary"
            )

            self.assertIsNotNone(routed)
            self.assertTrue(routed.scheduling_only)
            self.assertFalse(routed.authorizes_blueprint_repair)
            self.assertEqual(routed.implementation_prerequisites, ["def:provider"])

            self.assertEqual(
                _phase2_declaration_work_labels(
                    ctx,
                    [section],
                    {"lem:new-helper"},
                ),
                set(),
            )
            self.assertEqual(
                _phase2_prerequisite_frontier(
                    ctx, {"def:provider", "lem:consumer"}
                )[1],
                ["def:provider"],
            )

    def test_phase2_without_prerequisite_keeps_contract_pending_work(self) -> None:
        ctx = SimpleNamespace(
            phase2_started=True,
            phase2_prerequisite_labels=set(),
            nodes={"lem:new-helper": node("lem:new-helper")},
        )
        self.assertEqual(
            _phase2_declaration_work_labels(
                ctx,
                [],
                {"lem:new-helper"},
            ),
            {"lem:new-helper"},
        )

    def test_phase2_historical_pending_helper_waits_for_provider_body(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "simplex_opaque_definition_prerequisite.json"
            ).read_text(encoding="utf-8")
        )["pending_helper_preemption_case"]
        provider = fixture["provider_label"]
        blocked = fixture["blocked_label"]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(fixture["generated_module"], encoding="utf-8")
            section = Section(
                1,
                [provider, blocked],
                path,
                "Generated.Skeleton01",
                [],
                refined_labels={provider, blocked},
            )
            ctx = SimpleNamespace(
                nodes={
                    provider: node(provider),
                    blocked: node(blocked, uses={provider}),
                    fixture["contract_pending_label"]: node(
                        fixture["contract_pending_label"]
                    ),
                },
                phase2_started=True,
                phase2_prerequisite_labels={provider},
            )

            self.assertEqual(
                _phase2_declaration_work_labels(
                    ctx,
                    [section],
                    {fixture["contract_pending_label"]},
                ),
                set(fixture["expected_declaration_work"]),
            )

    def test_phase2_invalidated_provider_routes_to_minimal_whole_node_closure(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "simplex_opaque_definition_prerequisite.json"
            ).read_text(encoding="utf-8")
        )["invalidated_provider_case"]
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(fixture["generated_module"], encoding="utf-8")
            frozen_labels = fixture["frozen_labels"]
            section = Section(
                1,
                frozen_labels,
                path,
                "Generated.Skeleton01",
                [],
                refined_labels=set(frozen_labels),
            )
            ctx = SimpleNamespace(
                nodes={
                    label: node(label, uses=set(dependencies))
                    for label, dependencies in fixture["nodes"].items()
                },
                stmt_fps={label: f"fp:{label}" for label in fixture["nodes"]},
                telemetry=FakeTelemetry(),
                phase2_started=True,
                phase2_prerequisite_labels=set(),
            )
            request = RepairRequest(
                fixture["failure"]["evidence"],
                [fixture["failure"]["label"]],
                authorizes_blueprint_repair=True,
            )

            routed = _phase2_prerequisite_request_for_repair(
                ctx, [section], request, source="historical_resume_boundary"
            )

            expected = fixture["expected"]["prerequisite_labels"]
            self.assertIsNotNone(routed)
            self.assertTrue(routed.scheduling_only)
            self.assertFalse(routed.authorizes_blueprint_repair)
            self.assertEqual(
                set(routed.implementation_prerequisites), set(expected)
            )
            self.assertEqual(ctx.phase2_prerequisite_labels, set(expected))
            self.assertEqual(
                _prioritized_phase2_declaration_work(
                    ctx, set(fixture["pending_declaration_work"])
                ),
                set(expected),
            )
            self.assertEqual(
                _bottom_up_ready_frontier(
                    ctx.nodes, set(expected), set(frozen_labels)
                ),
                ["def:m-public-signed-affine-readout"],
            )
            self.assertEqual(
                _bottom_up_ready_frontier(
                    ctx.nodes,
                    {"def:m-function"},
                    set(frozen_labels) | {"def:m-public-signed-affine-readout"},
                ),
                ["def:m-function"],
            )

    def test_phase2_prerequisite_preserves_unrelated_decomposition(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "def def_provider : Nat := sorry\n\n"
                "theorem lem_blocked : def_provider = 1 := by sorry\n\n"
                "theorem lem_independent : True := by sorry\n",
                encoding="utf-8",
            )
            labels = ["def:provider", "lem:blocked", "lem:independent"]
            section = Section(
                1,
                labels,
                path,
                "Generated.Skeleton01",
                [],
                refined_labels=set(labels),
            )
            ctx = SimpleNamespace(
                nodes={
                    "def:provider": node("def:provider"),
                    "lem:blocked": node(
                        "lem:blocked", uses={"def:provider"}
                    ),
                    "lem:independent": node("lem:independent"),
                },
                stmt_fps={label: f"fp:{label}" for label in labels},
                stmt_blocks={label: f"Blueprint statement for {label}" for label in labels},
                telemetry=FakeTelemetry(),
                phase2_repair_queue=[],
                phase2_prerequisite_labels=set(),
                generation_feedback={},
            )
            outcomes = [
                SectionProofOutcome(
                    section=section,
                    decomposition={
                        "lem:blocked": [],
                        "lem:independent": ["helper for independent node"],
                    },
                    decomposition_evidence={
                        "lem:blocked": (
                            "Cannot prove the result while `def_provider` is an "
                            "opaque incomplete definition body."
                        ),
                        "lem:independent": "The blueprint claim needs a helper lemma.",
                    },
                )
            ]

            request = _route_phase2_proof_outcomes(ctx, outcomes, [section])

            self.assertIsNotNone(request)
            self.assertTrue(request.scheduling_only)
            self.assertEqual(request.implementation_prerequisites, ["def:provider"])
            self.assertEqual(
                [payload["labels"] for payload in ctx.phase2_repair_queue],
                [["lem:independent"]],
            )

    def test_phase2_repair_scope_keeps_existing_context_read_only(self) -> None:
        before = {
            "target": node("target", uses={"dependency"}),
            "dependency": node("dependency"),
            "sibling": node("sibling"),
        }
        self.assertEqual(
            _phase2_existing_repair_scope_violations(
                before,
                ["target"],
                {"target", "dependency", "new-helper"},
            ),
            {"dependency"},
        )
        self.assertEqual(
            _phase2_existing_repair_scope_violations(
                before,
                ["target", "dependency"],
                {"target", "dependency", "new-helper"},
            ),
            set(),
        )

    def test_complete_node_gate_rejects_sorry_but_allows_completed_definition(self) -> None:
        target_kinds = {"def_changed": "definition"}
        labels = {"def_changed": "def:changed"}
        complete = "def def_changed : Nat := 1"
        deferred = "def def_changed : Nat := sorry"

        complete_findings = _skeleton_code_findings(
            complete,
            target_kinds,
            labels,
            allow_deferred_bodies=False,
        )
        deferred_findings = _skeleton_code_findings(
            deferred,
            target_kinds,
            labels,
            allow_deferred_bodies=False,
        )

        self.assertEqual(complete_findings, [])
        self.assertTrue(
            any("whole-node transaction" in item.message for item in deferred_findings)
        )

    def test_complete_body_freezer_does_not_normalize_definition_back_to_sorry(self) -> None:
        label = "def:changed"
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "Skeleton01.lean"
            ctx = SimpleNamespace(
                name="paper",
                nodes={label: node(label)},
                lean_command=["lean"],
                telemetry=FakeTelemetry(),
                unavailable_imports=set(),
                defer_phase1_alignment=False,
                design_plan_entries={},
                semantic_plan_entries={},
                stmt_fps={label: "statement"},
                contract_fps={label: "contract"},
                retry_lifecycle={},
            )
            compiled = SimpleNamespace(ok=True, output="")
            with patch(
                "formalize_blueprint._section_module",
                return_value=("Generated.Skeleton01", path),
            ), patch(
                "formalize_blueprint._sections_for_deps", return_value=[]
            ), patch(
                "formalize_blueprint._skeleton_code_findings", return_value=[]
            ), patch(
                "formalize_blueprint._skeleton_deterministic_findings",
                return_value=[],
            ), patch(
                "formalize_blueprint._model_alignment_audit", return_value=None
            ), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._compile_module_olean", return_value=compiled
            ), patch(
                "formalize_blueprint._mark_section_compiled"
            ):
                frozen = _freeze_section_from_code(
                    ctx,
                    [label],
                    [],
                    _SectionNumberAllocator(1),
                    ["def def_changed : Nat := 1"],
                    [],
                    [],
                    complete_bodies=True,
                )

            self.assertIsNotNone(frozen)
            text = path.read_text(encoding="utf-8")
            self.assertIn("def def_changed : Nat := 1", text)
            self.assertNotIn("sorry", text)

    def test_complete_node_accepts_only_same_node_structural_representation(self) -> None:
        label = "def:changed"
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "Skeleton01.lean"
            ctx = SimpleNamespace(
                name="paper",
                nodes={label: node(label)},
                lean_command=["lean"],
                telemetry=FakeTelemetry(),
                unavailable_imports=set(),
                defer_phase1_alignment=False,
                design_plan_entries={},
                semantic_plan_entries={},
                stmt_fps={label: "statement"},
                contract_fps={label: "contract"},
                retry_lifecycle={},
            )
            compiled = LeanAttempt(ok=True, command=["lean"])
            with patch(
                "formalize_blueprint._section_module",
                return_value=("Generated.Skeleton01", path),
            ), patch(
                "formalize_blueprint._sections_for_deps", return_value=[]
            ), patch(
                "formalize_blueprint._skeleton_deterministic_findings",
                return_value=[],
            ), patch(
                "formalize_blueprint._model_alignment_audit", return_value=None
            ), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._compile_module_olean",
                return_value=compiled,
            ):
                frozen = _freeze_section_from_code(
                    ctx,
                    [label],
                    [],
                    _SectionNumberAllocator(1),
                    [
                        "structure ChangedPackage where\n  value : Nat",
                        "def def_changed : ChangedPackage := { value := 1 }",
                    ],
                    [],
                    [],
                    complete_bodies=True,
                )

            self.assertIsNotNone(frozen)
            text = path.read_text(encoding="utf-8")
            self.assertIn("structure ChangedPackage where", text)
            self.assertIn("def def_changed : ChangedPackage", text)

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

    def test_diagnostic_lifetimes_follow_statement_plan_and_candidate(self) -> None:
        label = "lem:a"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={
                label: {
                    "statement_fp": "statement-v1",
                    "code": "theorem lem_a : True := sorry",
                    "candidate_hash": "candidate-v1",
                }
            },
            phase2_node_candidates={},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "theorem lem_a : True",
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )
        plan_v1 = _candidate_plan_fingerprint(ctx, label)
        _record_diagnostic_evidence(
            ctx,
            label,
            "the blueprint requires the finite-key hypothesis",
            source="statement_alignment",
            kind="semantic",
            lifetime="statement",
        )
        _record_diagnostic_evidence(
            ctx,
            label,
            "unknown identifier in candidate v1",
            source="lean_compile",
            kind="compiler",
            lifetime="candidate",
            candidate_fp="candidate-v1",
        )
        _record_diagnostic_evidence(
            ctx,
            label,
            "the current plan omits the carrier type",
            source="plan_audit",
            kind="plan",
            lifetime="plan",
            plan_fp=plan_v1,
        )

        ctx.generation_candidates[label]["candidate_hash"] = "candidate-v2"
        ctx.generation_candidates[label]["code"] = (
            "theorem lem_a : True := by trivial"
        )
        _prune_stale_diagnostic_evidence(ctx)
        active = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual(
            {entry["kind"] for entry in active}, {"semantic", "plan"}
        )

        ctx.design_plan_entries[label]["target_signature"] = (
            "theorem lem_a (h : True) : True"
        )
        _prune_stale_diagnostic_evidence(ctx)
        active = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual({entry["kind"] for entry in active}, {"semantic"})

        ctx.stmt_fps[label] = "statement-v2"
        self.assertTrue(_prune_stale_diagnostic_evidence(ctx))
        self.assertEqual(_active_diagnostic_evidence(ctx, [label]), [])

    def test_equivalent_structured_feedback_is_one_diagnostic_fact(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "equivalent_failure_feedback.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={},
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )

        first_id = _record_diagnostic_evidence(
            ctx,
            label,
            fixture["first_feedback"],
            source="statement_alignment:first",
            kind="semantic",
            lifetime="statement",
            failure_identity=fixture["same_identity"],
        )
        second_id = _record_diagnostic_evidence(
            ctx,
            label,
            fixture["equivalent_feedback"],
            source="statement_alignment:equivalent",
            kind="semantic",
            lifetime="statement",
            failure_identity=fixture["same_identity"],
        )

        self.assertEqual(first_id, second_id)
        records = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["text"], fixture["first_feedback"])
        self.assertEqual(
            set(records[0]["sources"]),
            {"statement_alignment:first", "statement_alignment:equivalent"},
        )

        different_id = _record_diagnostic_evidence(
            ctx,
            label,
            fixture["different_feedback"],
            source="statement_alignment:different",
            kind="semantic",
            lifetime="statement",
            failure_identity=fixture["different_identity"],
        )
        self.assertNotEqual(first_id, different_id)
        self.assertEqual(len(_active_diagnostic_evidence(ctx, [label])), 2)

    def test_unstructured_feedback_is_not_semantically_guessed_equivalent(self) -> None:
        first = _diagnostic_failure_signature(
            kind="semantic",
            text="The declaration omits a required condition.",
        )
        second = _diagnostic_failure_signature(
            kind="semantic",
            text="A necessary hypothesis is missing from the declaration.",
        )
        self.assertNotEqual(first, second)

    def test_phase2_candidate_reuses_structured_failure_identity(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "equivalent_failure_feedback.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            contract_fps={label: "contract-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={},
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )
        first = _store_phase2_node_candidate(
            ctx,
            label,
            fixture["candidate"],
            evidence=fixture["first_feedback"],
            failure_kind="semantic_alignment",
            tier="base",
            source="historical_replay:first",
            failure_identity=fixture["same_identity"],
        )
        equivalent = _store_phase2_node_candidate(
            ctx,
            label,
            fixture["candidate"],
            evidence=fixture["equivalent_feedback"],
            failure_kind="semantic_alignment",
            tier="escalation",
            source="historical_replay:equivalent",
            failure_identity=fixture["same_identity"],
        )
        self.assertEqual(first["failure_hash"], equivalent["failure_hash"])
        self.assertTrue(equivalent["repeated_state"])

        different = _store_phase2_node_candidate(
            ctx,
            label,
            fixture["candidate"],
            evidence=fixture["different_feedback"],
            failure_kind="semantic_alignment",
            tier="escalation",
            source="historical_replay:different",
            failure_identity=fixture["different_identity"],
        )
        self.assertNotEqual(first["failure_hash"], different["failure_hash"])
        self.assertFalse(different["repeated_state"])

    def test_dependency_evidence_is_consumed_per_edge_not_per_label(self) -> None:
        labels = ["lem:consumer", "def:first", "def:second"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"{label}-v1" for label in labels},
            generation_feedback={},
            diagnostic_evidence={},
            phase1_dependency_observations={},
            generation_candidates={},
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )
        _record_diagnostic_evidence(
            ctx,
            "lem:consumer",
            "",
            source="phase1_generated_dependency_reference",
            kind="dependency_reference",
            lifetime="statement",
            data={
                "dependencies": ["def:first", "def:second"],
                "candidate_hashes": ["candidate-v1"],
            },
        )
        from formalize_blueprint import _clear_phase1_dependency_observations

        _clear_phase1_dependency_observations(
            ctx, {"lem:consumer": {"def:first"}}
        )
        records = _active_diagnostic_evidence(
            ctx, ["lem:consumer"], kinds={"dependency_reference"}
        )
        self.assertEqual(len(records), 1)
        self.assertEqual(
            records[0]["data"]["dependencies"], ["def:second"]
        )
        _clear_phase1_dependency_observations(
            ctx, {"lem:consumer": {"def:second"}}
        )
        self.assertEqual(
            _active_diagnostic_evidence(
                ctx, ["lem:consumer"], kinds={"dependency_reference"}
            ),
            [],
        )

    def test_acceptance_consumes_only_the_accepted_labels_evidence(self) -> None:
        labels = ["lem:a", "lem:b"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"{label}-v1" for label in labels},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={},
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )
        for label in labels:
            _store_generation_feedback(
                ctx,
                [label],
                f"semantic requirement for {label}",
                source="statement_alignment",
            )
        _clear_generation_feedback(ctx, ["lem:a"])
        self.assertEqual(_generation_feedback_for(ctx, ["lem:a"]), "")
        self.assertIn(
            "semantic requirement for lem:b",
            _generation_feedback_for(ctx, ["lem:b"]),
        )

    def test_generation_epoch_keeps_semantics_and_drops_obsolete_mechanics(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "evidence_lifecycle_matrix.json"
            ).read_text(encoding="utf-8")
        )
        case = next(
            item
            for item in fixture["cases"]
            if item["transition"] == "plan_authority_changed"
        )
        label = case["label"]
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: case["statement_fp"]},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={
                label: {
                    "statement_fp": case["statement_fp"],
                    "plan_fp": "old-plan",
                    "code": "theorem lem_target : True := sorry",
                    "candidate_hash": "candidate-v1",
                }
            },
            phase2_node_candidates={},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "theorem lem_target : True",
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            retry_lifecycle={
                "phase1_statement:lem:target": {
                    "label": label,
                    "stage": "phase1_statement",
                    "statement_fp": case["statement_fp"],
                }
            },
            phase1_exchange_history={},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            telemetry=FakeTelemetry(),
            design_plan="",
        )
        _record_diagnostic_evidence(
            ctx,
            label,
            "blueprint statement omits no assumptions",
            source="statement_alignment",
            kind="semantic",
            lifetime="statement",
        )
        _record_diagnostic_evidence(
            ctx,
            label,
            "candidate-v1 has an unknown identifier",
            source="lean_compile",
            kind="compiler",
            lifetime="candidate",
            candidate_fp="candidate-v1",
        )
        ctx.design_plan_entries[label]["target_signature"] = (
            "theorem lem_target (h : True) : True"
        )
        _transition_phase1_generation_epoch(
            ctx, [label], reason="historical_fixture_plan_change"
        )
        active = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual(
            {entry["kind"] for entry in active},
            set(case["expected_active_kinds"]),
        )
        self.assertNotIn(label, ctx.generation_candidates)

    def test_generic_retry_cannot_broaden_exact_candidate_evidence(self) -> None:
        label = "lem:a"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={
                label: {
                    "statement_fp": "statement-v1",
                    "code": "theorem lem_a : True := sorry",
                    "candidate_hash": "candidate-v1",
                }
            },
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )
        evidence = "Lean rejected candidate-v1: unknown identifier `oldName`"
        _record_diagnostic_evidence(
            ctx,
            label,
            evidence,
            source="validated_contract_compile",
            kind="compiler",
            lifetime="candidate",
            candidate_fp="candidate-v1",
        )
        _store_generation_feedback(
            ctx, [label], evidence, source="outer_phase1_retry"
        )
        records = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["lifetime"], "candidate")
        self.assertIn("outer_phase1_retry", records[0]["sources"])

        ctx.generation_candidates[label]["candidate_hash"] = "candidate-v2"
        ctx.generation_candidates[label]["code"] = (
            "theorem lem_a : True := by trivial"
        )
        _prune_stale_diagnostic_evidence(ctx)
        self.assertEqual(_active_diagnostic_evidence(ctx, [label]), [])

    def test_outer_retry_reuses_structured_semantic_fact_without_prompt_growth(
        self,
    ) -> None:
        label = "lem:a"
        identity = {
            "classification": "lean-generation",
            "origin": "lean-generation",
            "missing_plan_requirements": ["preserve the finite-key hypothesis"],
        }
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={},
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )

        _store_generation_feedback(
            ctx,
            [label],
            "The declaration drops the finite-key hypothesis.",
            source="statement_alignment",
            evidence_by_label={
                label: "The declaration drops the finite-key hypothesis."
            },
            evidence_identity_by_label={label: identity},
        )
        _store_generation_feedback(
            ctx,
            [label],
            "Audit rejected: the finite-key assumption is absent.",
            source="outer_phase1_retry",
            evidence_by_label={
                label: "Audit rejected: the finite-key assumption is absent."
            },
            evidence_identity_by_label={label: identity},
        )

        records = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual(len(records), 1)
        self.assertEqual(
            set(records[0]["sources"]),
            {"statement_alignment", "outer_phase1_retry"},
        )
        rendered = _generation_feedback_for(ctx, [label])
        self.assertEqual(rendered.count(f"for {label}:"), 1)
        self.assertNotIn("Audit rejected:", rendered)

    def test_semantic_retry_prompt_does_not_render_persisted_evidence_twice(
        self,
    ) -> None:
        """Historical semantic retries must not recursively embed their ledger."""
        label = "constr:delta-four-cells"
        rejection = (
            "Blueprint contract audit rejected:\n"
            f"- {label} [reject]: the declaration erases the construction data"
        )
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            stmt_blocks={label: "Concrete coning construction."},
            tex_blocks={label: "Concrete coning construction with proof sketch."},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={},
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )
        _store_generation_feedback(
            ctx,
            [label],
            rejection,
            source="statement_alignment",
            evidence_by_label={label: rejection},
        )
        findings = [
            SkeletonFinding(rejection, label=label, lean_name=_lean_name(label))
        ]

        with patch(
            "formalize_blueprint._minimal_dependency_interface",
            return_value="-- dependency interface",
        ), patch(
            "formalize_blueprint._planned_helper_specs", return_value=[]
        ), patch(
            "formalize_blueprint._common_rules", return_value="COMMON RULES"
        ), patch(
            "formalize_blueprint._design_plan_block", return_value="DESIGN PLAN"
        ):
            prompt = _targeted_skeleton_patch_prompt(
                ctx,
                [label],
                [],
                [],
                "def constr_delta_four_cells : Prop := sorry",
                findings,
                timeout_s=300,
                findings_already_persisted=True,
            )

        self.assertEqual(prompt.count("the declaration erases the construction data"), 1)
        self.assertIn("exact active findings", prompt)

    def test_feedback_rendering_deduplicates_typed_fact_across_boundaries(
        self,
    ) -> None:
        label = "lem:a"
        rejection = "The declaration omits the finite-key hypothesis."
        identity = {
            "classification": "lean-generation",
            "missing_plan_requirements": ["finite-key hypothesis"],
        }
        signature = _diagnostic_failure_signature(
            kind="semantic", text=rejection, identity=identity
        )
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={
                "statement-record": {
                    "label": label,
                    "statement_fp": "statement-v1",
                    "kind": "semantic",
                    "lifetime": "statement",
                    "plan_fp": "",
                    "candidate_fp": "",
                    "text": rejection,
                    "failure_signature": signature,
                    "sources": ["statement_alignment"],
                    "consumed": False,
                },
                "transaction-record": {
                    "label": label,
                    "statement_fp": "statement-v1",
                    "kind": "operational",
                    "lifetime": "transaction",
                    "plan_fp": "",
                    "candidate_fp": "",
                    "text": "Outer retry wrapper: " + rejection,
                    "failure_signature": signature,
                    "sources": ["outer_phase1_retry"],
                    "consumed": False,
                },
            },
            generation_candidates={},
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )

        rendered = _generation_feedback_for(ctx, [label, label])
        self.assertEqual(rendered.count(f"for {label}:"), 1)
        injected = [
            payload
            for event, payload in ctx.telemetry.events
            if event == "phase1_retry_feedback_injected"
        ][-1]
        self.assertEqual(injected["labels"], [label])

    def test_concurrent_generic_and_exact_producers_keep_exact_lifetime(self) -> None:
        label = "lem:a"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={
                label: {
                    "statement_fp": "statement-v1",
                    "code": "theorem lem_a : True := sorry",
                    "candidate_hash": "candidate-v1",
                }
            },
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )
        evidence = "Lean rejected candidate-v1: unknown identifier `oldName`"

        def exact() -> None:
            _record_diagnostic_evidence(
                ctx,
                label,
                evidence,
                source="validated_contract_compile",
                kind="compiler",
                lifetime="candidate",
                candidate_fp="candidate-v1",
            )

        def generic() -> None:
            _record_diagnostic_evidence(
                ctx,
                label,
                evidence,
                source="outer_phase1_retry",
            )

        with ThreadPoolExecutor(max_workers=8) as pool:
            futures = [
                pool.submit(exact if index % 2 else generic)
                for index in range(40)
            ]
            for future in futures:
                future.result()

        records = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["kind"], "compiler")
        self.assertEqual(records[0]["lifetime"], "candidate")
        self.assertEqual(records[0]["candidate_fp"], "candidate-v1")

    def test_semantic_first_deterministic_source_is_candidate_scoped(self) -> None:
        label = "lem:a"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={
                label: {
                    "statement_fp": "statement-v1",
                    "code": "theorem lem_a : True := sorry",
                    "candidate_hash": "candidate-v1",
                }
            },
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=FakeTelemetry(),
        )
        _store_generation_feedback(
            ctx,
            [label],
            "candidate omitted its planned helper",
            source="semantic_first_deterministic",
        )
        records = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual(len(records), 1)
        self.assertEqual(records[0]["kind"], "deterministic")
        self.assertEqual(records[0]["lifetime"], "candidate")

    def test_unattached_mechanical_evidence_is_not_widened_to_statement(self) -> None:
        label = "lem:a"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={},
            phase2_node_candidates={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            telemetry=telemetry,
        )

        evidence_id = _record_diagnostic_evidence(
            ctx,
            label,
            "unknown identifier from a discarded candidate",
            source="validated_contract_compile",
            kind="compiler",
            lifetime="candidate",
        )

        self.assertEqual(evidence_id, "")
        self.assertEqual(_active_diagnostic_evidence(ctx, [label]), [])
        self.assertTrue(
            any(
                event == "diagnostic_evidence_unattached_candidate_discarded"
                for event, _payload in telemetry.events
            )
        )

    def test_parallel_generation_feedback_updates_are_not_lost(self) -> None:
        """Overlapping workers must retain every finding for one contract."""

        class SlowFeedback(dict):
            def get(self, key, default=None):
                value = super().get(key, default)
                # Without a state transaction, workers can all observe the old
                # value here and overwrite one another after this pause.
                time.sleep(0.01)
                return value

        label = "lem:a"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback=SlowFeedback(),
            telemetry=FakeTelemetry(),
        )
        worker_count = 6
        start = threading.Barrier(worker_count)

        def save_finding(index: int) -> None:
            start.wait()
            _store_generation_feedback(
                ctx,
                [label],
                f"worker-{index}-finding",
                source=f"worker-{index}",
            )

        threads = [
            threading.Thread(target=save_finding, args=(index,))
            for index in range(worker_count)
        ]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join(timeout=2)

        self.assertTrue(all(not thread.is_alive() for thread in threads))
        combined = _generation_feedback_for(ctx, [label])
        for index in range(worker_count):
            self.assertIn(f"worker-{index}-finding", combined)

    def test_generation_feedback_keeps_sibling_audit_findings_separate(self) -> None:
        labels = ["lem:a", "lem:b"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"{label}-v1" for label in labels},
            generation_feedback={},
            telemetry=FakeTelemetry(),
        )
        evidence = (
            "Blueprint contract audit rejected:\n"
            "- lem:a [reject]: missing the concrete probability equation\n"
            "- lem:b [reject]: dropped the finite-key hypothesis"
        )
        _store_generation_feedback(
            ctx, labels, evidence, source="statement_alignment"
        )

        feedback_a = _generation_feedback_for(ctx, ["lem:a"])
        feedback_b = _generation_feedback_for(ctx, ["lem:b"])
        self.assertIn("probability equation", feedback_a)
        self.assertNotIn("finite-key hypothesis", feedback_a)
        self.assertIn("finite-key hypothesis", feedback_b)
        self.assertNotIn("probability equation", feedback_b)

    def test_blueprint_direct_fingerprint_ignores_sibling_audit_changes(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "blueprint_direct_sibling_evidence.json"
            ).read_text(encoding="utf-8")
        )
        labels = fixture["labels"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps=fixture["statement_fingerprints"],
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": f"def {_lean_name(label)} : Prop",
                    "origin": "phase1_candidate",
                }
                for label in labels
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            telemetry=FakeTelemetry(),
        )

        _activate_blueprint_direct_generation(
            ctx,
            labels,
            fixture["first_audit"],
            source="historical-replay",
        )
        stable_label = fixture["stable_label"]
        sibling_label = fixture["changed_sibling_label"]
        initial_fingerprint = _candidate_plan_fingerprint(ctx, stable_label)
        initial_evidence = ctx.blueprint_direct_generation[stable_label]["evidence"]
        sibling_fingerprint = _candidate_plan_fingerprint(ctx, sibling_label)

        repeated = _activate_blueprint_direct_generation(
            ctx,
            labels,
            fixture["second_audit"],
            source="historical-replay",
        )

        self.assertEqual(repeated, set())
        self.assertEqual(
            _candidate_plan_fingerprint(ctx, stable_label),
            initial_fingerprint,
        )
        self.assertEqual(
            ctx.blueprint_direct_generation[stable_label]["evidence"],
            initial_evidence,
        )
        self.assertNotIn(
            fixture["changed_sibling_marker"],
            ctx.blueprint_direct_generation[stable_label]["evidence"],
        )
        self.assertNotIn(
            fixture["changed_sibling_marker"],
            ctx.blueprint_direct_generation[sibling_label]["evidence"],
        )
        self.assertEqual(
            _candidate_plan_fingerprint(ctx, sibling_label),
            sibling_fingerprint,
        )
        self.assertIn(
            fixture["changed_sibling_marker"],
            _generation_feedback_for(ctx, [sibling_label]),
        )
        self.assertNotIn(
            fixture["changed_sibling_marker"],
            _generation_feedback_for(ctx, [stable_label]),
        )

    def test_latest_run_blueprint_direct_reactivation_preserves_lifecycle(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "blueprint_direct_reactivation.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        ctx = SimpleNamespace(
            name=fixture["blueprint"],
            nodes={label: node(label)},
            stmt_fps={label: fixture["statement_fp"]},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": f"theorem {_lean_name(label)} : True",
                    "origin": "phase1_candidate",
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            phase1_exchange_history={},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            telemetry=FakeTelemetry(),
            design_plan="",
        )

        activated = _activate_blueprint_direct_generation(
            ctx,
            [label],
            fixture["first_evidence"],
            source=fixture["first_source"],
            evidence_by_label={label: fixture["first_evidence"]},
        )
        self.assertEqual(activated, {label})
        direct_fp = _candidate_plan_fingerprint(ctx, label)
        retry_key = f"phase1_statement:{label}"
        ctx.generation_candidates[label] = {
            "statement_fp": fixture["statement_fp"],
            "plan_fp": direct_fp,
            "code": f"theorem {_lean_name(label)} : True := by sorry",
        }
        ctx.retry_lifecycle[retry_key] = {
            "label": label,
            "stage": "phase1_statement",
            "statement_fp": fixture["statement_fp"],
            "state": "base",
            "failures": 0,
        }
        ctx.phase1_exchange_history["recorded-exchange"] = {
            "labels": [label],
            "statement_fps": {label: fixture["statement_fp"]},
            "plan_fps": {label: direct_fp},
        }

        duplicate = _activate_blueprint_direct_generation(
            ctx,
            [label],
            fixture["repeat_evidence"],
            source=fixture["repeat_source"],
            evidence_by_label={label: fixture["repeat_evidence"]},
        )
        self.assertEqual(duplicate, set())
        self.assertIn(label, ctx.generation_candidates)
        self.assertIn(retry_key, ctx.retry_lifecycle)
        self.assertIn("recorded-exchange", ctx.phase1_exchange_history)
        self.assertEqual(_candidate_plan_fingerprint(ctx, label), direct_fp)

        audit = AlignmentAuditResult(
            "lean-generation",
            fixture["repeat_evidence"],
            {label},
            [],
            kinds_by_label={label: "lean-generation"},
            reasons_by_label={label: fixture["repeat_evidence"]},
            origins_by_label={label: "plan"},
            plan_requirements_by_label={
                label: [fixture["missing_requirement"]]
            },
        )
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module(
                f"theorem {_lean_name(label)} : True := by sorry\n"
            ),
            import_modules=[],
            generation_tier="base",
        )
        request = _semantic_first_failure_request(ctx, 0, [candidate], audit, [])

        self.assertEqual(request.labels, [label])
        self.assertEqual(request.failure_route.action, "independent")
        self.assertEqual(_candidate_plan_fingerprint(ctx, label), direct_fp)
        self.assertEqual(ctx.blueprint_direct_generation[label]["activations"], 1)
        self.assertEqual(
            ctx.retry_lifecycle[retry_key]["state"],
            "escalation",
        )
        self.assertIn(
            fixture["missing_requirement"],
            _generation_feedback_for(ctx, [label]),
        )
        activation_events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_blueprint_direct_generation_activated"
        ]
        self.assertEqual(len(activation_events), 1)

        ctx.stmt_fps[label] = fixture["changed_statement_fp"]
        reactivated = _activate_blueprint_direct_generation(
            ctx,
            [label],
            "new statement evidence",
            source="changed_statement",
            evidence_by_label={label: "new statement evidence"},
        )
        self.assertEqual(reactivated, {label})
        self.assertEqual(ctx.blueprint_direct_generation[label]["activations"], 1)
        self.assertNotEqual(_candidate_plan_fingerprint(ctx, label), direct_fp)

    def test_blueprint_direct_activation_returns_activated_labels(self) -> None:
        label = "lem:claim"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "fp-claim-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "theorem lem_claim : True",
                    "origin": "phase1_candidate",
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            phase1_exchange_history={},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            telemetry=FakeTelemetry(),
            design_plan="",
        )

        activated = _activate_blueprint_direct_generation(
            ctx,
            [label],
            "audit evidence",
            source="test",
        )

        self.assertEqual(activated, {label})
        self.assertTrue(ctx.blueprint_direct_generation[label]["evidence"])

    def test_blueprint_direct_freeze_invalidates_only_changed_downstream_plans(
        self,
    ) -> None:
        child = "def:child"
        parent = "thm:parent"
        ctx = SimpleNamespace(
            nodes={
                child: node(child),
                parent: node(parent, uses={child}),
            },
            stmt_fps={
                child: "fp-child-v1",
                parent: "fp-parent-v1",
            },
            design_plan_entries={
                child: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_child : Prop",
                    "origin": "phase1_candidate",
                },
                parent: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "theorem thm_parent : def_child",
                    "origin": "global_plan",
                },
            },
            design_plan_alternates={parent: [{"target_signature": "stale"}]},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={
                parent: {
                    "statement_fp": "fp-parent-v1",
                    "plan_fp": "old-child-surface",
                }
            },
            retry_lifecycle={
                f"phase1_statement:{parent}": {
                    "label": parent,
                    "stage": "phase1_statement",
                    "statement_fp": "fp-parent-v1",
                }
            },
            phase1_exchange_history={},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            telemetry=FakeTelemetry(),
            design_plan="",
            effective_section_size=1,
            section_size=4,
            proven_section_size=0,
            section_clean_streak=0,
        )

        activated = _activate_blueprint_direct_generation(
            ctx,
            [child],
            "child candidate-owned plan omitted required fields",
            source="test",
        )

        self.assertEqual(activated, {child})
        self.assertIn(child, ctx.design_plan_entries)
        self.assertIn(parent, ctx.design_plan_entries)
        self.assertIn(parent, ctx.design_plan_alternates)
        self.assertIn(parent, ctx.generation_candidates)
        self.assertIn(f"phase1_statement:{parent}", ctx.retry_lifecycle)
        self.assertFalse(
            any(
                event == "phase1_descendant_plan_invalidated"
                for event, _fields in ctx.telemetry.events
            )
        )

        _note_frozen_section(ctx, [child])

        self.assertIn(parent, ctx.design_plan_entries)
        self.assertIn(parent, ctx.design_plan_alternates)
        self.assertIn(parent, ctx.generation_candidates)
        self.assertIn(f"phase1_statement:{parent}", ctx.retry_lifecycle)

        ctx.design_plan_entries[child] = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": "fp-child-v1",
            "target_signature": "structure def_child where\n  value : Nat",
            "origin": "phase1_candidate",
        }

        _note_frozen_section(ctx, [child])

        self.assertNotIn(parent, ctx.design_plan_entries)
        self.assertNotIn(parent, ctx.design_plan_alternates)
        self.assertNotIn(parent, ctx.generation_candidates)
        self.assertNotIn(f"phase1_statement:{parent}", ctx.retry_lifecycle)
        self.assertTrue(
            any(
                event == "phase1_descendant_plan_invalidated"
                and fields["labels"] == [parent]
                for event, fields in ctx.telemetry.events
            )
        )

    def test_continued_state_migrates_mixed_blueprint_direct_evidence(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "blueprint_direct_sibling_evidence.json"
            ).read_text(encoding="utf-8")
        )
        labels = fixture["labels"]
        stable_label = fixture["stable_label"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps=fixture["statement_fingerprints"],
            blueprint_direct_generation={
                stable_label: {
                    "statement_fp": fixture["statement_fingerprints"][stable_label],
                    "source": "candidate_semantic_exhaustion",
                    "evidence": fixture["first_audit"],
                    "activations": 1,
                }
            },
            telemetry=FakeTelemetry(),
        )

        self.assertEqual(_prune_stale_blueprint_direct_generation(ctx), set())
        migrated = ctx.blueprint_direct_generation[stable_label]["evidence"]
        self.assertIn("Wang-Sun bound", migrated)
        self.assertNotIn("paper-max-construction", migrated)
        self.assertNotIn("open questions", migrated)
        events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_blueprint_direct_evidence_migrated"
        ]
        self.assertEqual(events[-1]["labels"], [stable_label])

    def test_phase1_exchange_history_survives_outer_retry_context(self) -> None:
        label = "lem:a"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={},
            blueprint_direct_generation={},
            phase1_exchange_history={},
            runner_spec="codex:gpt-base",
            escalation_runner_spec="codex:gpt-escalation",
        )
        kwargs = {
            "prompt": "fix the exact declaration",
            "candidate_code": "theorem lem_a : True := by sorry",
            "purpose": "skeleton_declaration_patch",
            "tier": "base",
        }
        first = _phase1_exchange_start(ctx, [label], **kwargs)
        self.assertFalse(
            _phase1_exchange_finish(
                ctx, first, status="ok", response_text="theorem lem_a : True := by trivial"
            )
        )

        second = _phase1_exchange_start(ctx, [label], **kwargs)
        self.assertEqual(first, second)
        self.assertTrue(
            _phase1_exchange_finish(
                ctx, second, status="ok", response_text="theorem lem_a : True := by trivial"
            )
        )
        self.assertFalse(
            _phase1_exchange_finish(
                ctx, second, status="ok", response_text="theorem lem_a : True := by simp"
            )
        )

        third = _phase1_exchange_start(ctx, [label], **kwargs)
        self.assertEqual(first, third)
        self.assertEqual(_phase1_exchange_start(ctx, [label], **kwargs), "")

        changed_model = SimpleNamespace(
            **{
                **ctx.__dict__,
                "runner_spec": "codex:gpt-base-v2",
            }
        )
        changed_model_key = _phase1_exchange_start(
            changed_model, [label], **kwargs
        )
        self.assertNotEqual(changed_model_key, "")

        ctx.stmt_fps[label] = "statement-v2"
        self.assertEqual(
            _prune_stale_phase1_exchange_history(ctx),
            {first, changed_model_key},
        )

    def test_targeted_compiler_patch_keeps_unresolved_semantic_feedback(self) -> None:
        """Compiler-only retries must not forget an earlier audit rejection."""
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "semantic_compiler_feedback_handoff.json"
            ).read_text(encoding="utf-8")
        )
        case = fixture["cases"][0]
        label = case["label"]
        semantic_evidence = case["semantic_evidence"]
        compiler_evidence = case["compiler_evidence"]
        ctx = SimpleNamespace(
            name=fixture["blueprint"],
            nodes={label: node(label)},
            stmt_blocks={label: "Concrete finite-register operator contract."},
            tex_blocks={
                label: "Concrete finite-register operator contract with its proof sketch."
            },
            stmt_fps={label: case["statement_fingerprint"]},
            generation_feedback={},
            telemetry=FakeTelemetry(),
        )
        _store_generation_feedback(
            ctx,
            [label],
            semantic_evidence,
            source="statement_audit",
        )
        findings = [
            SkeletonFinding(
                compiler_evidence,
                label=label,
                lean_name=_lean_name(label),
                category="lean_compile",
            )
        ]

        with patch(
            "formalize_blueprint._minimal_dependency_interface",
            return_value="-- dependency interface",
        ), patch(
            "formalize_blueprint._planned_helper_specs", return_value=[]
        ), patch(
            "formalize_blueprint._common_rules", return_value="COMMON RULES"
        ), patch(
            "formalize_blueprint._design_plan_block", return_value="DESIGN PLAN"
        ):
            prompt = _targeted_skeleton_patch_prompt(
                ctx,
                [label],
                [],
                [],
                "def unrelated_large_sibling : Nat := 37\n\n"
                "def def_finite_register_operators : RegisterOperator := sorry",
                findings,
                timeout_s=300,
            )

        self.assertIn(compiler_evidence, prompt)
        self.assertIn(semantic_evidence, prompt)
        self.assertIn("def_finite_register_operators", prompt)
        self.assertNotIn("unrelated_large_sibling", prompt)

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

    def test_candidate_store_scopes_semantic_evidence_per_label(self) -> None:
        labels = ["def:left", "def:right"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"{label}-v1" for label in labels},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            telemetry=FakeTelemetry(),
        )
        code = (
            "def def_left : Nat := sorry\n\n"
            "def def_right : Int := sorry"
        )
        evidence = {
            "def:left": "left drops the source dimension",
            "def:right": "right drops the target dimension",
        }
        _store_generation_candidates(
            ctx,
            labels,
            code,
            source="phase1_alignment",
            all_labels=labels,
            semantic_status="rejected",
            semantic_evidence_by_label=evidence,
        )

        self.assertEqual(
            ctx.generation_candidates["def:left"]["semantic_evidence"],
            evidence["def:left"],
        )
        self.assertNotIn(
            "target dimension",
            ctx.generation_candidates["def:left"]["semantic_evidence"],
        )
        self.assertEqual(
            ctx.generation_candidates["def:right"]["semantic_evidence"],
            evidence["def:right"],
        )
        self.assertNotIn(
            "source dimension",
            ctx.generation_candidates["def:right"]["semantic_evidence"],
        )

    def test_semantically_rejected_best_does_not_block_clean_revision(self) -> None:
        label = "def:security-parameter-negligible"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            telemetry=FakeTelemetry(),
        )
        rejected = "def def_security_parameter_negligible : Nat := sorry"
        revision = "def def_security_parameter_negligible : Int := sorry"

        _store_generation_candidates(
            ctx,
            [label],
            rejected,
            source="phase1_layer_0_alignment",
            repair_stage="semantic_rejected",
            lean_status="passed",
            semantic_status="rejected",
            semantic_evidence="the interface weakens the blueprint definition",
        )
        _store_generation_candidates(
            ctx,
            [label],
            revision,
            source="phase1_statement_generation",
            repair_stage="deterministic_valid",
        )

        entry = ctx.generation_candidates[label]
        self.assertEqual(entry["code"], revision)
        self.assertEqual(entry["semantic_status"], "unknown")
        transitions = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_candidate_transition"
        ]
        self.assertEqual(
            transitions[-1]["decision_reasons"],
            ["semantic_rejection_revision"],
        )

        _store_generation_candidates(
            ctx,
            [label],
            revision,
            source="validated_contract_compile",
            lean_status="passed",
        )
        self.assertEqual(ctx.generation_candidates[label]["lean_status"], "passed")

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

    def test_blueprint_direct_transition_cannot_restamp_old_candidate(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "blueprint_direct_candidate_epoch.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["observed_transition"]["label"]
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: fixture["statement_fp"]},
            design_plan_entries={label: fixture["ordinary_plan"]},
            blueprint_direct_generation={},
            generation_candidates={},
            telemetry=telemetry,
        )
        ordinary_fp = _candidate_plan_fingerprint(ctx, label)
        _store_generation_candidates(
            ctx,
            [label],
            fixture["candidate"],
            source="validated_contract_compile",
            lean_status="failed",
            lean_output="synthetic Lean failure",
        )

        # A strategy change invalidates this code as a reusable candidate. It
        # can remain diagnostics, but direct generation must produce new code.
        ctx.blueprint_direct_generation[label] = {
            "statement_fp": fixture["statement_fp"],
            "source": "compile_exhaustion",
            "evidence": fixture["direct_evidence"],
        }
        self.assertEqual(_prune_stale_generation_candidates(ctx), {label})

        stored = _store_generation_candidates(
            ctx,
            [label],
            fixture["candidate"],
            source="phase1_layer_0_incomplete_generation",
            reusable_uncompiled=True,
            expected_plan_fps={label: ordinary_fp},
        )
        self.assertEqual(stored, [])
        self.assertNotIn(label, ctx.generation_candidates)
        rejected = [
            fields
            for event, fields in telemetry.events
            if event == "phase1_retry_candidate_epoch_rejected"
        ]
        self.assertEqual(rejected[-1]["labels"], [label])

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

    def test_lean_rejected_candidate_is_revision_context_not_zero_call_reuse(self) -> None:
        label = "def:uniform-finite-sampling"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={},
            generation_candidates={},
            generation_feedback={},
            unavailable_imports=set(),
            telemetry=telemetry,
        )
        code = (
            "open BigOperators\n\n"
            "def def_uniform_finite_sampling : Nat := 1\n"
        )
        error = (
            "Skeleton06.lean:7:12: error: unknown namespace `BigOperators`\n"
            "Skeleton06.lean:14:16: error: expected token\n"
        )
        _store_generation_candidates(
            ctx,
            [label],
            code,
            source="semantic_first_pre_audit",
            reusable_uncompiled=True,
        )
        self.assertTrue(
            _candidate_is_reusable_uncompiled(ctx.generation_candidates[label])
        )

        # This is the exact transition missed by run-20260731-095949: the
        # compile result describes the same bytes that had been marked as a
        # reusable, deterministic-clean candidate.
        _store_generation_candidates(
            ctx,
            [label],
            code,
            source="validated_contract_compile",
            lean_status="failed",
            lean_output=error,
        )

        entry = ctx.generation_candidates[label]
        self.assertEqual(entry["lean_status"], "failed")
        self.assertFalse(entry["reusable_uncompiled"])
        self.assertFalse(_candidate_is_reusable_uncompiled(entry))
        self.assertIsNone(_reusable_uncompiled_candidate(ctx, [label], []))
        # Failed code is still supplied to the next model as exact revision
        # context; only the unsafe no-call shortcut is disabled.
        self.assertIn(
            "def def_uniform_finite_sampling",
            _generation_candidates_for(ctx, [label]),
        )

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
        self.assertFalse(
            _candidate_is_reusable_uncompiled(
                {
                    "source": "phase1_layer_7_incomplete_generation",
                    "reusable_uncompiled": True,
                    "lean_status": "failed",
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

    def test_minimal_dependency_interface_soft_budget_never_drops_required_context(self) -> None:
        ctx = SimpleNamespace(
            nodes={
                "def:dependency": node("def:dependency"),
                "lem:target": node("lem:target", uses={"def:dependency"}),
            }
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            fields = "\n".join(f"  field_{index} : Nat" for index in range(80))
            path.write_text(
                "structure def_dependency where\n" + fields + "\n",
                encoding="utf-8",
            )
            section = Section(
                number=1,
                labels=["def:dependency"],
                path=path,
                module="AutoBlueprint.Generated.Paper.Skeleton01",
                import_modules=[],
            )
            interface = _minimal_dependency_interface(
                ctx,
                ["lem:target"],
                [section],
                [section.module],
                budget=100,
            )

        self.assertGreater(len(interface), 100)
        self.assertIn("field_79", interface)

    def test_historical_uue_context_overflow_partitions_without_failing(self) -> None:
        fixture_path = (
            REPO_ROOT
            / "tests"
            / "fixtures"
            / "phase1_context_budget_replay"
            / "uue_20260802.json"
        )
        fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
        labels = fixture["labels"]
        measured = {
            tuple(key.split("|")): value
            for key, value in fixture["contiguous_interface_chars"].items()
        }
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp:{label}" for label in labels},
            generation_candidates={},
            telemetry=FakeTelemetry(),
        )

        def measured_chars(_ctx, part, _sections):
            return measured[tuple(part)]

        with patch(
            "formalize_blueprint._phase1_dependency_interface_chars",
            side_effect=measured_chars,
        ):
            parts = _partition_phase1_groups_by_dependency_context(
                ctx,
                [labels],
                [],
                budget=fixture["soft_budget"],
            )

        self.assertEqual(parts, fixture["expected_groups"])
        self.assertEqual(
            [
                fields
                for event, fields in ctx.telemetry.events
                if event == "phase1_dependency_context_partitioned"
            ][0]["interface_chars"],
            fixture["expected_group_interface_chars"],
        )

    def test_dependency_context_keeps_oversized_candidate_component_atomic(self) -> None:
        labels = ["def:provider", "lem:consumer"]
        shared_code = (
            "structure SharedSurface where\n  value : Nat\n\n"
            "def def_provider : SharedSurface := sorry\n\n"
            "theorem lem_consumer : True := by sorry\n"
        )
        candidates = {
            label: {
                "statement_fp": f"fp:{label}",
                "component_labels": labels,
                "code": shared_code,
            }
            for label in labels
        }
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp:{label}" for label in labels},
            generation_candidates=candidates,
            telemetry=FakeTelemetry(),
        )

        with patch(
            "formalize_blueprint._phase1_dependency_interface_chars",
            return_value=12000,
        ):
            parts = _partition_phase1_groups_by_dependency_context(
                ctx,
                [labels],
                [],
                budget=10000,
            )

        self.assertEqual(parts, [labels])
        overflows = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_dependency_context_soft_overflow"
        ]
        self.assertEqual(len(overflows), 1)
        self.assertEqual(overflows[0]["labels"], labels)
        self.assertEqual(overflows[0]["interface_chars"], 12000)

    def test_dependency_context_partition_defers_when_measurement_is_unavailable(self) -> None:
        labels = ["def:provider", "lem:consumer"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp:{label}" for label in labels},
            generation_candidates={},
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._phase1_dependency_interface_chars",
            side_effect=ValueError("missing frozen provider"),
        ):
            parts = _partition_phase1_groups_by_dependency_context(
                ctx, [labels], []
            )

        self.assertEqual(parts, [labels])
        deferred = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_dependency_context_partition_deferred"
        ]
        self.assertEqual(len(deferred), 1)
        self.assertIn("missing frozen provider", deferred[0]["reason"])

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

    def test_alignment_audit_uses_structured_classification_not_reason_keywords(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "structured_statement_audit_routing.json"
            ).read_text(encoding="utf-8")
        )
        labels = fixture["expected_after_fix"]["routed_labels"]
        dependencies = {
            dependency
            for issue in fixture["audit_response"]["issues"]
            for dependency in issue["required_dependencies"]
        }
        ctx = SimpleNamespace(
            name="simplex",
            nodes={
                label: node(label) for label in labels + sorted(dependencies)
            },
            tex_blocks={
                label: f"Concrete blueprint statement for {label}."
                for label in labels
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
            text=json.dumps(fixture["audit_response"]),
        )
        code = "\n".join(
            f"theorem {_lean_name(label)} : True := by sorry" for label in labels
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(ctx, labels, code)

        self.assertIsNotNone(audit)
        self.assertEqual(audit.kind, "lean-generation")
        self.assertEqual(audit.labels_for("lean-generation"), set(labels))
        self.assertEqual(audit.labels_for("decomposition"), set())
        self.assertEqual(audit.labels_for_origin("plan"), set(labels))
        self.assertEqual(audit.helpers_for(labels), [])
        for issue in fixture["audit_response"]["issues"]:
            label = issue["node"]
            self.assertEqual(
                audit.required_dependencies[label],
                set(issue["required_dependencies"]),
            )
            self.assertEqual(
                audit.plan_requirements_by_label[label],
                issue["missing_plan_requirements"],
            )
        routing = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "statement_audit_routing"
        ]
        self.assertEqual(
            routing[-1]["routed_kinds"],
            {label: "lean-generation" for label in labels},
        )
        self.assertFalse(routing[-1]["blueprint_repair_authorized"])

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

    def test_alignment_audit_defers_predicate_body_without_reshaping_contract(self) -> None:
        label = "def:common-face"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            tex_blocks={
                label: (
                    "F is a common face of Q_i for i in J when a supporting "
                    "functional exposes exactly F in every Q_i."
                )
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
                    "classification": "lean_translation_issue",
                    "issues": [
                        {
                            "node": label,
                            "severity": "reject",
                            "classification": "lean_translation_issue",
                            "reason": (
                                "The deferred body does not yet encode the "
                                "supporting-functional and intersection clauses."
                            ),
                            "interface_defects": [],
                            "deferred_body_obligations": [
                                "require a supporting functional exposing F",
                                "require F to be the exact common intersection",
                            ],
                        }
                    ],
                }
            ),
        )
        code = (
            "def def_polytope (n : Nat) := Set (Fin n -> Real)\n\n"
            "def def_common_face {I : Type} [Fintype I] (n : Nat) "
            "(Q : I -> def_polytope n) (J : Finset I) "
            "(F : def_polytope n) : Prop := sorry\n"
        )

        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(ctx, [label], code)

        self.assertIsNone(audit)
        statement_events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "statement_audit"
        ]
        self.assertEqual(
            statement_events[-1]["deferred_body_obligations"][label],
            [
                "require a supporting functional exposing F",
                "require F to be the exact common intersection",
            ],
        )

    def test_alignment_audit_still_rejects_deferred_definition_interface_defect(self) -> None:
        label = "def:common-face"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            tex_blocks={label: "CommonFace Q J F is a proposition."},
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
                            "node": label,
                            "severity": "reject",
                            "classification": "lean_translation_issue",
                            "reason": "The public predicate omits F.",
                            "interface_defects": [
                                "missing public parameter F : def_polytope n"
                            ],
                            "deferred_body_obligations": [],
                        }
                    ],
                }
            ),
        )
        code = (
            "def def_polytope (n : Nat) := Set (Fin n -> Real)\n\n"
            "def def_common_face {I : Type} [Fintype I] (n : Nat) "
            "(Q : I -> def_polytope n) (J : Finset I) : Prop := sorry\n"
        )

        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(ctx, [label], code)

        self.assertIsNotNone(audit)
        self.assertEqual(audit.kind, "lean-generation")
        self.assertEqual(audit.rejected, {label})

    def test_alignment_audit_does_not_defer_unstructured_definition_rejection(self) -> None:
        label = "def:common-face"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            tex_blocks={label: "CommonFace Q J F is a proposition."},
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
                            "node": label,
                            "severity": "reject",
                            "reason": "The declaration is not faithful.",
                            "interface_defects": [],
                            "deferred_body_obligations": [],
                        }
                    ],
                }
            ),
        )
        code = (
            "def def_common_face {I : Type} [Fintype I] "
            "(J : Finset I) : Prop := sorry\n"
        )

        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(ctx, [label], code)

        self.assertIsNotNone(audit)
        self.assertEqual(audit.rejected, {label})

    def test_alignment_audit_reports_plan_and_combined_origins_with_evidence(self) -> None:
        plan_only = "def:plan-only"
        combined = "def:combined"
        ctx = SimpleNamespace(
            name="paper",
            nodes={plan_only: node(plan_only), combined: node(combined)},
            tex_blocks={
                plan_only: "Keys are exactly coordinate pairs satisfying P.",
                combined: "The operator is the concrete tensor product.",
            },
            design_plan_entries={
                plan_only: {
                    "target_signature": "def def_plan_only : Type",
                    "decisions": ["Use an abstract key type."],
                },
                combined: {
                    "target_signature": "def def_combined : Type",
                    "decisions": ["Use an abstract operator type."],
                },
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
                    "classification": "lean_translation_issue",
                    "issues": [
                        {
                            "node": plan_only,
                            "severity": "reject",
                            "classification": "lean_translation_issue",
                            "reason": "The plan permits duplicate abstract keys.",
                            "failure_origin": "plan",
                            "missing_plan_requirements": [
                                "keys are extensionally exactly the valid coordinate pairs"
                            ],
                        },
                        {
                            "node": combined,
                            "severity": "reject",
                            "classification": "lean_translation_issue",
                            "reason": "The plan is abstract and Lean returns identity.",
                            "failure_origin": "both",
                            "missing_plan_requirements": [
                                "the operator is the indexed tensor product"
                            ],
                        },
                    ],
                }
            ),
        )
        code = (
            "def def_plan_only : Type := Nat\n\n"
            "def def_combined : Type := Nat\n"
        )
        with patch("formalize_blueprint._call_model", return_value=response) as call:
            audit = _model_alignment_audit(ctx, [plan_only, combined], code)

        self.assertIsNotNone(audit)
        self.assertEqual(audit.labels_for_origin("plan"), {plan_only})
        self.assertEqual(audit.labels_for_origin("both"), {combined})
        self.assertEqual(
            audit.plan_requirements_for({plan_only, combined}),
            [
                "keys are extensionally exactly the valid coordinate pairs",
                "the operator is the indexed tensor product",
            ],
        )
        prompt = call.call_args.args[1]
        self.assertIn("Current Phase-1 design-plan contract", prompt)
        self.assertIn("Use an abstract key type.", prompt)

    def test_alignment_audit_ignores_unsupported_plan_origin(self) -> None:
        label = "def:claim"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            tex_blocks={label: "A concrete definition."},
            design_plan_entries={label: {"target_signature": "def def_claim : Type"}},
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
                            "node": label,
                            "severity": "reject",
                            "reason": "The statement is wrong.",
                            "failure_origin": "plan",
                            "missing_plan_requirements": [],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(
                ctx, [label], "def def_claim : Type := Nat\n"
            )

        self.assertEqual(audit.labels_for_origin("lean"), {label})
        self.assertEqual(audit.plan_requirements_for({label}), [])

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

    def test_alignment_audit_distinguishes_dependency_addition_from_removal(self) -> None:
        target = "lem:recursive-schedule-data"
        required = "lem:public-transition-interface"
        internal = "lem:internal-construction-detail"
        ctx = SimpleNamespace(
            name="paper",
            nodes={
                target: node(target),
                required: node(required),
                internal: node(internal),
            },
            tex_blocks={
                target: "A recursive schedule uses the public transition interface.",
                required: "The public transition interface.",
                internal: "An internal construction detail.",
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
                    "classification": "lean_translation_issue",
                    "issues": [
                        {
                            "node": target,
                            "severity": "reject",
                            "classification": "lean_translation_issue",
                            "reason": "Use only the public transition interface.",
                            "required_dependencies": [required],
                            "forbidden_dependencies": [internal],
                            "missing_helpers": [],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(
                ctx,
                [target],
                "theorem lem_recursive_schedule_data : True := by sorry\n",
            )

        self.assertIsNotNone(audit)
        self.assertEqual(audit.required_dependencies, {target: {required}})
        self.assertEqual(audit.forbidden_dependencies, {target: {internal}})
        self.assertIn("Remove generated public references", audit.reason_for([target]))

    def test_alignment_audit_never_adds_a_contradictory_dependency(self) -> None:
        target = "def:consumer"
        dependency = "def:provider"
        ctx = SimpleNamespace(
            name="paper",
            nodes={target: node(target), dependency: node(dependency)},
            tex_blocks={target: "A consumer.", dependency: "A provider."},
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
                            "classification": "lean_translation_issue",
                            "reason": "Conflicting audit response.",
                            "required_dependencies": [dependency],
                            "forbidden_dependencies": [dependency],
                            "missing_helpers": [],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _model_alignment_audit(
                ctx, [target], "def def_consumer : Prop := sorry\n"
            )

        self.assertIsNotNone(audit)
        self.assertEqual(audit.required_dependencies, {})
        self.assertEqual(audit.forbidden_dependencies, {target: {dependency}})
        self.assertIn("no dependency edge was added", audit.reason_for([target]))

    def test_post_repair_boundary_routes_missing_edge_before_lean(self) -> None:
        target = "lem:key-generation-support"
        dependency = "def:key-generation-free-coordinate-sampler"
        nodes = {
            target: node(target),
            dependency: node(dependency),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_blocks={
                target: "Every supported key has a unique free-coordinate preimage.",
                dependency: "The free-coordinate sampler assembles keys.",
            },
            tex_blocks={
                target: "Every supported key has a unique free-coordinate preimage.",
                dependency: "The free-coordinate sampler assembles keys.",
            },
            stmt_fps={target: "target-v2", dependency: "dependency-v1"},
            paper_text="Key generation samples free coordinates and assembles a supported key.",
            telemetry=FakeTelemetry(),
            base_timeout=30,
            base_effort="medium",
            repair_boundary_pending={
                "mode": "audit",
                "labels": [target],
                "statement_fps": {target: "target-v2"},
                "previous_statements": {target: "Every generated key is supported."},
                "evidence": "",
                "repair_labels": [],
                "required_dependencies": {},
                "decomposition_helpers": [],
            },
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "issues": [
                        {
                            "node": target,
                            "severity": "reject",
                            "classification": "missing_statement_dependency",
                            "reason": "The repaired support claim uses the sampler's assembly map.",
                            "required_dependencies": [dependency],
                            "missing_helpers": [],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            request = _pending_repair_boundary_request(ctx)

        self.assertIsNotNone(request)
        assert request is not None
        self.assertEqual(request.required_dependencies, {target: {dependency}})
        self.assertEqual(request.model_repair_labels, [])
        self.assertEqual(request.labels, [target])
        self.assertEqual(ctx.repair_boundary_pending["mode"], "repair")

    def test_post_repair_boundary_routes_unchanged_provider_separately(self) -> None:
        consumer = "cor:geometric-signed-simplex"
        provider = "thm:polytope-triangulation"
        ctx = SimpleNamespace(
            name="simplex-provider-boundary-regression",
            nodes={
                consumer: node(consumer, uses={provider}),
                provider: node(provider),
            },
            stmt_blocks={
                consumer: "The repaired signed-simplex corollary.",
                provider: "A triangulation into convex-hull ranges exists.",
            },
            tex_blocks={
                consumer: "Use the triangulation theorem to obtain the signed cells.",
                provider: "A triangulation into convex-hull ranges exists.",
            },
            stmt_fps={consumer: "consumer-v2", provider: "provider-v1"},
            paper_text="The cells must also have the required affine independence.",
            telemetry=FakeTelemetry(),
            base_timeout=30,
            base_effort="medium",
            repair_boundary_pending={
                "mode": "audit",
                "labels": [consumer],
                "statement_fps": {consumer: "consumer-v2"},
                "previous_statements": {consumer: "The old corollary."},
                "repair_roots": [consumer],
                "component_changed_labels": [consumer],
                "require_component_closure": True,
                "evidence": "The consumer proof cannot obtain affine-independent cells.",
            },
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "issues": [
                        {
                            "node": provider,
                            "severity": "reject",
                            "classification": "provider_contract_defect",
                            "reason": (
                                "The provider exposes convex-hull ranges but not the "
                                "affine-independent cell property required by the proof."
                            ),
                            "required_dependencies": [],
                            "missing_helpers": [],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            request = _pending_repair_boundary_request(ctx)

        self.assertIsNotNone(request)
        assert request is not None
        self.assertEqual(request.labels, [provider])
        self.assertEqual(request.provider_contract_labels, [provider])
        self.assertEqual(request.reschedule_labels, [consumer])
        self.assertEqual(request.model_repair_labels, [provider])
        event = next(
            fields
            for name, fields in ctx.telemetry.events
            if name == "post_repair_boundary_audit"
        )
        self.assertEqual(event["provider_repair_labels"], [provider])

    def test_post_repair_boundary_rejects_provider_outside_dependency_closure(self) -> None:
        consumer = "lem:consumer"
        unrelated = "lem:unrelated"
        ctx = SimpleNamespace(
            name="provider-scope-regression",
            nodes={consumer: node(consumer), unrelated: node(unrelated)},
            stmt_blocks={consumer: "A repaired claim.", unrelated: "Another claim."},
            tex_blocks={consumer: "A repaired proof.", unrelated: "Another proof."},
            stmt_fps={consumer: "consumer-v2", unrelated: "unrelated-v1"},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=30,
            base_effort="medium",
            repair_boundary_pending={
                "mode": "audit",
                "labels": [consumer],
                "statement_fps": {consumer: "consumer-v2"},
                "previous_statements": {consumer: "Old claim."},
                "repair_roots": [consumer],
                "component_changed_labels": [consumer],
                "require_component_closure": True,
            },
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "issues": [
                        {
                            "node": unrelated,
                            "severity": "reject",
                            "classification": "provider_contract_defect",
                            "reason": "Rewrite this unrelated theorem.",
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            request = _pending_repair_boundary_request(ctx)

        self.assertIsNotNone(request)
        assert request is not None
        self.assertEqual(request.labels, [consumer])
        self.assertEqual(request.provider_contract_labels, [])

    def test_post_repair_boundary_consumes_an_already_applied_edge(self) -> None:
        target = "def:reduced-operator"
        dependency = "def:density-operator-interface"
        sibling = "def:finite-register-interface"
        ctx = SimpleNamespace(
            nodes={
                target: node(target, uses={dependency}),
                dependency: node(dependency),
                sibling: node(sibling),
            },
            stmt_fps={
                target: "target-after-edge",
                dependency: "dependency-v1",
                sibling: "sibling-v1",
            },
            telemetry=FakeTelemetry(),
            repair_boundary_pending={
                "mode": "repair",
                "labels": [target, dependency, sibling],
                "statement_fps": {
                    target: "target-before-edge",
                    dependency: "dependency-v1",
                    sibling: "sibling-v1",
                },
                "previous_statements": {},
                "evidence": "The reduced operator requires its density interface.",
                "repair_labels": [],
                "required_dependencies": {target: {dependency}},
                "decomposition_helpers": [],
            },
        )

        request = _pending_repair_boundary_request(ctx)

        self.assertIsNone(request)
        self.assertEqual(ctx.repair_boundary_pending, {})
        self.assertEqual(
            ctx.telemetry.events[-1][0], "post_repair_boundary_completed"
        )

    def test_post_repair_boundary_preserves_model_action_after_edge(self) -> None:
        target = "def:reduced-operator"
        dependency = "def:density-operator-interface"
        ctx = SimpleNamespace(
            nodes={
                target: node(target, uses={dependency}),
                dependency: node(dependency),
            },
            stmt_fps={
                target: "target-after-edge",
                dependency: "dependency-v1",
            },
            telemetry=FakeTelemetry(),
            repair_boundary_pending={
                "mode": "repair",
                "labels": [target],
                "statement_fps": {target: "target-before-edge"},
                "previous_statements": {},
                "evidence": "The edge and the target statement both need correction.",
                "repair_labels": [target],
                "required_dependencies": {target: {dependency}},
                "decomposition_helpers": ["a normalized reduced-state helper"],
            },
        )

        request = _pending_repair_boundary_request(ctx)

        self.assertIsNotNone(request)
        assert request is not None
        self.assertEqual(request.labels, [target])
        self.assertEqual(request.model_repair_labels, [target])
        self.assertEqual(request.required_dependencies, {})
        self.assertTrue(request.authorizes_blueprint_repair)

    def test_post_repair_boundary_acceptance_adds_no_repair(self) -> None:
        label = "lem:repaired"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            stmt_blocks={label: "The repaired statement."},
            tex_blocks={label: "The repaired statement."},
            stmt_fps={label: "statement-v2"},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=30,
            base_effort="medium",
            repair_boundary_pending={
                "mode": "audit",
                "labels": [label],
                "statement_fps": {label: "statement-v2"},
                "previous_statements": {label: "The old statement."},
            },
        )
        response = CallResult(
            status="ok", text=json.dumps({"accepted": True, "issues": []})
        )
        with patch("formalize_blueprint._call_model", return_value=response) as call:
            request = _pending_repair_boundary_request(ctx)

        self.assertIsNone(request)
        self.assertEqual(call.call_count, 1)
        self.assertEqual(ctx.repair_boundary_pending, {})

    def test_post_repair_boundary_unavailable_falls_through_once(self) -> None:
        label = "lem:repaired"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            stmt_blocks={label: "The repaired statement."},
            tex_blocks={label: "The repaired statement."},
            stmt_fps={label: "statement-v2"},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=30,
            base_effort="medium",
            repair_boundary_pending={
                "mode": "audit",
                "labels": [label],
                "statement_fps": {label: "statement-v2"},
                "previous_statements": {label: "The old statement."},
            },
        )
        with patch(
            "formalize_blueprint._call_model",
            return_value=CallResult(status="timeout", error="timed out"),
        ) as call:
            self.assertIsNone(_pending_repair_boundary_request(ctx))
            self.assertIsNone(_pending_repair_boundary_request(ctx))

        self.assertEqual(call.call_count, 1)
        self.assertEqual(ctx.repair_boundary_pending, {})

    def test_proof_prose_only_repair_does_not_queue_boundary_call(self) -> None:
        label = "lem:proof-only"
        before = {label: node(label)}
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "same-public-statement"},
            telemetry=FakeTelemetry(),
            repair_boundary_pending={},
        )
        with patch("formalize_blueprint._call_model") as call:
            queued = _mark_repair_boundary_pending(
                ctx,
                {label},
                before,
                previous_statement_blocks={label: "unchanged statement"},
                previous_statement_fps={label: "same-public-statement"},
            )
            request = _pending_repair_boundary_request(ctx)

        self.assertEqual(queued, set())
        self.assertIsNone(request)
        call.assert_not_called()

    def test_existing_statement_repair_uses_immutable_pre_edit_snapshot(self) -> None:
        """Regression for Simplex run-20260814-043118 events 2898-2904.

        A repaired existing node must be audited again even though both the old
        and current ``Node`` objects point at the same already-modified file.
        """
        label = "def:newton-cell-affine-identification"
        before = {label: node(label)}
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            phase2_started=False,
            stmt_fps={label: "statement-after-repair"},
            telemetry=FakeTelemetry(),
            repair_boundary_pending={
                "mode": "repair",
                "labels": ["lem:newton-p-coefficient-hulls"],
                "statement_fps": {
                    "lem:newton-p-coefficient-hulls": "edge-before"
                },
                "required_dependencies": {
                    "lem:newton-p-coefficient-hulls": {label}
                },
            },
        )

        queued = _mark_repair_boundary_pending(
            ctx,
            {label},
            before,
            previous_statement_blocks={label: "invalid affine map statement"},
            previous_statement_fps={label: "statement-before-repair"},
            repair_roots=[label],
            failure_evidence="The affine map is not well-defined on all of H2.",
        )

        self.assertEqual(queued, {label})
        self.assertEqual(ctx.repair_boundary_pending["mode"], "audit")
        self.assertEqual(ctx.repair_boundary_pending["labels"], [label])
        self.assertEqual(
            ctx.repair_boundary_pending["statement_fps"],
            {label: "statement-after-repair"},
        )
        self.assertEqual(
            ctx.repair_boundary_pending["previous_statements"],
            {label: "invalid affine map statement"},
        )

    def test_phase2_repair_boundary_keeps_root_and_complete_helper_component(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["serial_helper_discovery_regression"]
        root = fixture["original_root"]
        helpers = fixture["observed_helper_chain"]
        before = {root: node(root)}
        current_nodes = {
            root: node(root, uses={helpers[0]}),
            helpers[0]: node(helpers[0], uses={helpers[1]}),
            helpers[1]: node(helpers[1]),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=current_nodes,
            phase2_started=True,
            stmt_fps={label: f"{label}-v2" for label in current_nodes},
            stmt_blocks={label: f"Statement for {label}." for label in current_nodes},
            tex_blocks={
                label: f"Statement and complete proof for {label}."
                for label in current_nodes
            },
            paper_text="",
            telemetry=FakeTelemetry(),
            repair_boundary_pending={},
        )
        with patch(
            "formalize_blueprint._statement_blocks",
            return_value={root: f"Statement for {root}."},
        ), patch(
            "formalize_blueprint._statement_fingerprints",
            return_value={root: f"{root}-v2"},
        ):
            queued = _mark_repair_boundary_pending(
                ctx,
                set(current_nodes),
                before,
                previous_statement_blocks={
                    root: f"Statement for {root}."
                },
                previous_statement_fps={root: f"{root}-v1"},
                repair_roots=[root],
                failure_evidence=fixture["original_evidence"],
            )

        self.assertEqual(queued, set(current_nodes))
        pending = ctx.repair_boundary_pending
        self.assertEqual(pending["repair_roots"], [root])
        self.assertEqual(pending["component_changed_labels"], sorted(current_nodes))
        self.assertTrue(pending["require_component_closure"])
        prompt = _post_repair_boundary_prompt(ctx, pending["labels"])
        self.assertIn(fixture["original_evidence"], prompt)
        self.assertIn(root, prompt)
        for helper in helpers:
            self.assertIn(helper, prompt)
        self.assertIn("dependency-closed", prompt)
        self.assertIn("all foreseeable missing", prompt)

    def test_phase2_component_rejection_preserves_root_evidence_and_all_helpers(self) -> None:
        root = "lem:security-winning-probability-transport"
        helper = "lem:security-concrete-package-final-bound"
        ctx = SimpleNamespace(
            name="paper",
            nodes={root: node(root, uses={helper}), helper: node(helper)},
            stmt_fps={root: "root-v2", helper: "helper-v1"},
            stmt_blocks={root: "Root statement.", helper: "Helper statement."},
            tex_blocks={root: "Root proof.", helper: "Helper proof."},
            paper_text="",
            telemetry=FakeTelemetry(),
            base_timeout=30,
            base_effort="medium",
            repair_boundary_pending={
                "mode": "audit",
                "labels": [root, helper],
                "statement_fps": {root: "root-v2", helper: "helper-v1"},
                "previous_statements": {root: "Root statement.", helper: ""},
                "evidence": "original alignment rejection",
                "repair_roots": [root],
                "component_changed_labels": [root, helper],
                "require_component_closure": True,
            },
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "accepted": False,
                    "issues": [
                        {
                            "node": root,
                            "severity": "reject",
                            "classification": "needs_decomposition",
                            "reason": "the helper still postpones two obligations",
                            "required_dependencies": [],
                            "missing_helpers": [
                                "unpack the final-reduction package",
                                "transport the concrete probability bound",
                            ],
                        }
                    ],
                }
            ),
        )
        with patch("formalize_blueprint._call_model", return_value=response):
            request = _pending_repair_boundary_request(ctx)

        self.assertIsNotNone(request)
        assert request is not None
        self.assertTrue(request.authorizes_blueprint_repair)
        self.assertEqual(request.model_repair_labels, [root])
        self.assertEqual(
            request.decomposition_helpers,
            [
                "unpack the final-reduction package",
                "transport the concrete probability bound",
            ],
        )
        self.assertIn("original alignment rejection", request.evidence)
        self.assertIn("still postpones two obligations", request.evidence)

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

    def test_dependency_evidence_survives_plan_epoch_until_critic_confirms(self) -> None:
        target = "lem:consumer"
        dependency = "def:provider"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={target: node(target), dependency: node(dependency)},
            stmt_fps={target: "consumer-v1", dependency: "provider-v1"},
            contract_fps={},
            tex_blocks={},
            semantic_plan_entries={},
            design_plan_entries={},
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={
                target: {
                    "statement_fp": "consumer-v1",
                    "component_labels": [target],
                    "code": "theorem lem_consumer : True := sorry",
                }
            },
            phase1_dependency_observations={},
            phase1_exchange_history={},
            retry_lifecycle={},
            quarantine={},
            quarantined_labels=set(),
            local_group_partitions={},
            telemetry=telemetry,
            conjecture_policy="attempt",
        )
        candidate = (
            "theorem lem_consumer : def_provider = def_provider := sorry"
        )
        findings = _skeleton_deterministic_findings(candidate, ctx, [target])
        self.assertTrue(
            any(
                finding.category == "outside_dependency_closure"
                and finding.dependencies == (dependency,)
                for finding in findings
            )
        )

        _transition_phase1_generation_epoch(
            ctx, [target], reason="candidate_plan_defect"
        )
        self.assertNotIn(target, ctx.generation_candidates)
        self.assertEqual(
            ctx.phase1_dependency_observations[target]["dependencies"],
            [dependency],
        )
        self.assertEqual(
            _confirmed_phase1_dependency_observations(
                ctx, {target: {dependency}}
            ),
            {target: {dependency}},
        )

        ctx.stmt_fps[target] = "consumer-v2"
        self.assertEqual(
            _confirmed_phase1_dependency_observations(
                ctx, {target: {dependency}}
            ),
            {},
        )
        self.assertNotIn(target, ctx.phase1_dependency_observations)

    def test_historical_helper_reference_authorizes_dependency_edge(self) -> None:
        case = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "immediate_dependency_edge.json"
            ).read_text(encoding="utf-8")
        )["cases"][0]
        target = case["label"]
        dependency = next(iter(case["required_dependencies"][target]))
        ctx = SimpleNamespace(
            name="historical-uue-dependency-edge",
            nodes={target: node(target), dependency: node(dependency)},
            stmt_fps={target: "target-v1", dependency: "dependency-v1"},
            design_plan_entries={},
            semantic_plan_entries={},
            phase1_dependency_observations={},
            telemetry=FakeTelemetry(),
            conjecture_policy="attempt",
        )

        findings = _skeleton_deterministic_findings(
            case["candidate_code"], ctx, [target]
        )

        self.assertTrue(
            any(
                finding.category == "outside_dependency_closure"
                and finding.label == target
                and finding.dependencies == (dependency,)
                for finding in findings
            )
        )
        self.assertEqual(
            _confirmed_phase1_dependency_observations(
                ctx,
                {target: set(case["required_dependencies"][target])},
            ),
            {target: {dependency}},
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
        self.assertEqual(
            _decomposition_orientation_dependency_edges(
                before, reversed_after, [target]
            ),
            {},
        )

    def test_decomposition_orientation_missing_edge_can_be_repaired(self) -> None:
        target = "cor:geometric-signed-simplex"
        helper = "lem:tetrahedron-cut-cells-rhombic"
        before = {target: node(target)}
        after = {
            target: node(target),
            helper: node(helper),
        }

        findings = _decomposition_orientation_findings(before, after, [target])
        self.assertEqual(len(findings), 1)
        self.assertIn("not in the dependency closure", findings[0])
        self.assertEqual(
            _decomposition_orientation_dependency_edges(before, after, [target]),
            {target: {helper}},
        )

    def test_decomposition_orientation_multi_root_is_not_guessed(self) -> None:
        target_a = "cor:geometric-signed-simplex"
        target_b = "cor:other"
        helper = "lem:tetrahedron-cut-cells-rhombic"
        before = {target_a: node(target_a), target_b: node(target_b)}
        after = {
            target_a: node(target_a),
            target_b: node(target_b),
            helper: node(helper),
        }

        self.assertEqual(
            _decomposition_orientation_dependency_edges(
                before, after, [target_a, target_b]
            ),
            {},
        )

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
            stmt_fps={target: "claim-v1", dependency: "dependency-v1"},
            phase1_dependency_observations={
                target: {
                    "statement_fp": "claim-v1",
                    "dependencies": [dependency],
                    "candidate_hashes": ["prior-candidate"],
                }
            },
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
            ) as retry_failure, patch(
                "formalize_blueprint._revise_audit_reported_plan_defects"
            ) as revise_plan, patch(
                "formalize_blueprint._activate_audit_reported_candidate_plan_defects"
            ) as activate_direct, patch(
                "formalize_blueprint._plan_realized_semantic_rejections",
                return_value=set(),
            ), patch(
                "formalize_blueprint._store_generation_feedback"
            ), patch(
                "formalize_blueprint._quarantine_labels"
            ), patch(
                "formalize_blueprint._discard_section_artifacts"
            ):
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(ctx, 0, [section])

        retry_failure.assert_not_called()
        self.assertEqual(
            set(revise_plan.call_args.kwargs["skip_labels"]), {target}
        )
        self.assertEqual(
            set(activate_direct.call_args.kwargs["skip_labels"]), {target}
        )

        self.assertEqual(
            raised.exception.required_dependencies,
            {target: {dependency}},
        )
        self.assertFalse(raised.exception.authorizes_blueprint_repair)
        self.assertTrue(
            _requires_blueprint_transaction(
                raised.exception.authorizes_blueprint_repair,
                raised.exception.required_dependencies,
            )
        )

    def test_integrated_audit_candidate_plan_defect_uses_blueprint_direct_generation(
        self,
    ) -> None:
        target = "def:relu-network"
        audit = AlignmentAuditResult(
            "lean-generation",
            "candidate-owned contract omitted affine layer semantics",
            {target},
            [],
            kinds_by_label={target: "lean-generation"},
            reasons_by_label={
                target: (
                    "def:relu-network [reject]: layer maps must be affine and "
                    "the computed function must be the alternating composition"
                )
            },
            origins_by_label={target: "plan"},
            plan_requirements_by_label={
                target: [
                    "each layer map must be affine",
                    "computed function must be the alternating composition",
                ]
            },
        )
        ctx = SimpleNamespace(
            name="paper",
            nodes={target: node(target)},
            stmt_fps={target: "fp-relu-network"},
            design_plan_entries={
                target: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "structure def_relu_network where",
                    "origin": "phase1_candidate",
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            phase1_exchange_history={},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            telemetry=FakeTelemetry(),
            lean_command=["lean"],
            design_plan="",
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "structure def_relu_network where\n"
                "  affine_maps : Nat -> Nat\n",
                encoding="utf-8",
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
                "formalize_blueprint._discard_section_artifacts"
            ), patch(
                "formalize_blueprint._finalize_phase1_accepted_sections",
                return_value=[],
            ):
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(ctx, 0, [section])

        request = raised.exception
        self.assertFalse(request.authorizes_blueprint_repair)
        self.assertEqual(request.labels, [target])
        self.assertEqual(request.failure_route.action, "independent")
        self.assertIn(target, ctx.blueprint_direct_generation)
        self.assertIn(
            "alternating composition",
            ctx.blueprint_direct_generation[target]["evidence"],
        )
        self.assertNotIn(f"phase1_statement:{target}", ctx.retry_lifecycle)
        self.assertTrue(
            any(
                event == "phase1_audit_origin_candidate_plan_direct"
                for event, _fields in ctx.telemetry.events
            )
        )

    def test_generation_retry_without_dependency_evidence_stays_out_of_blueprint_transaction(
        self,
    ) -> None:
        self.assertFalse(_requires_blueprint_transaction(False, {}))
        self.assertTrue(_requires_blueprint_transaction(True, {}))

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

    def test_semantic_first_candidate_plan_defect_uses_blueprint_direct_generation(
        self,
    ) -> None:
        target = "def:relu-network"
        audit = AlignmentAuditResult(
            "lean-generation",
            "candidate-owned contract omitted affine layer semantics",
            {target},
            [],
            kinds_by_label={target: "lean-generation"},
            reasons_by_label={
                target: (
                    "def:relu-network [reject]: layer maps must be affine and "
                    "the computed function must be the alternating composition"
                )
            },
            origins_by_label={target: "plan"},
            plan_requirements_by_label={
                target: ["computed function must be the alternating composition"]
            },
        )
        candidate = Phase1LayerCandidate(
            labels=[target],
            parsed=_parse_module(
                "structure def_relu_network where\n"
                "  affine_maps : Nat -> Nat\n"
            ),
            import_modules=[],
            generation_tier="base",
        )
        ctx = SimpleNamespace(
            name="paper",
            nodes={target: node(target)},
            stmt_fps={target: "fp-relu-network"},
            design_plan_entries={
                target: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "structure def_relu_network where",
                    "origin": "phase1_candidate",
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            phase1_exchange_history={},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            telemetry=FakeTelemetry(),
            design_plan="",
        )

        request = _semantic_first_failure_request(ctx, 0, [candidate], audit, [])

        self.assertFalse(request.authorizes_blueprint_repair)
        self.assertEqual(request.labels, [target])
        self.assertEqual(request.failure_route.action, "independent")
        self.assertIn(target, ctx.blueprint_direct_generation)
        self.assertNotIn(f"phase1_statement:{target}", ctx.retry_lifecycle)

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

    def test_alignment_cache_invalidates_when_design_plan_changes(self) -> None:
        label = "lem:cached"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            tex_blocks={label: "The cached statement."},
            design_plan_entries={
                label: {"target_signature": "theorem lem_cached : True"}
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
                {"accepted": True, "classification": "accepted", "issues": []}
            ),
        )
        code = "theorem lem_cached : True := by sorry\n"
        with patch("formalize_blueprint._call_model", return_value=response) as call:
            self.assertIsNone(_model_alignment_audit(ctx, [label], code))
            self.assertIsNone(_model_alignment_audit(ctx, [label], code))
            ctx.design_plan_entries[label]["decisions"] = [
                "Expose an additional blueprint obligation."
            ]
            self.assertIsNone(_model_alignment_audit(ctx, [label], code))
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

    def test_plan_parser_normalizes_exact_mathlib_aliases(self) -> None:
        label = "def:consumer"
        ctx = SimpleNamespace(
            nodes={
                "def:affine-map": node(
                    "def:affine-map", mathlibok=True, lean_decl="AffineMap"
                ),
                label: node(label, uses={"def:affine-map"}),
            },
            stmt_fps={label: "consumer-v1"},
        )
        response = json.dumps(
            {
                "contracts": [
                    {
                        "label": label,
                        "target_signature": "def def_consumer : def_affine_map",
                        "helpers": [
                            {
                                "name": "ConsumerInterface",
                                "kind": "structure",
                                "members": [
                                    {"name": "map", "type": "def_affine_map"}
                                ],
                                "purpose": "consumer interface",
                            }
                        ],
                        "decisions": [],
                    }
                ]
            }
        )

        parsed = _parse_design_plan_entries(ctx, [label], response)

        self.assertEqual(
            parsed[label]["target_signature"], "def def_consumer : AffineMap"
        )
        self.assertEqual(
            parsed[label]["helpers"][0]["members"][0]["type"], "AffineMap"
        )

    def test_plan_closure_rejects_mathlib_alias_in_target_signature(self) -> None:
        label = "def:consumer"
        ctx = SimpleNamespace(
            nodes={
                "def:affine-map": node(
                    "def:affine-map", mathlibok=True, lean_decl="AffineMap"
                ),
                label: node(label, uses={"def:affine-map"}),
            },
            stmt_fps={label: "consumer-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "consumer-v1",
                    "target_signature": "def def_consumer : def_affine_map",
                    "helpers": [],
                    "decisions": [],
                }
            },
            design_plan="",
            paper_text="",
            telemetry=FakeTelemetry(),
        )

        findings = _validate_design_plan_contract_closure(ctx, [label])

        self.assertIn(label, findings)
        self.assertIn("Mathlib-owned def:affine-map", findings[label][0])
        self.assertIn("`AffineMap`", findings[label][0])
        self.assertNotIn("closure_fp", ctx.design_plan_entries[label])

    def test_plan_closure_checks_mathlib_alias_in_helper_member_type(self) -> None:
        label = "def:consumer"
        ctx = SimpleNamespace(
            nodes={
                "def:affine-map": node(
                    "def:affine-map", mathlibok=True, lean_decl="AffineMap"
                ),
                label: node(label, uses={"def:affine-map"}),
            },
            stmt_fps={label: "consumer-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "consumer-v1",
                    "target_signature": "def def_consumer : ConsumerInterface",
                    "helpers": [
                        {
                            "name": "ConsumerInterface",
                            "kind": "structure",
                            "members": [
                                {"name": "map", "type": "def_affine_map"}
                            ],
                            "required_members": ["map"],
                            "purpose": "consumer interface",
                        }
                    ],
                    "decisions": [],
                }
            },
            design_plan="",
            paper_text="",
            telemetry=FakeTelemetry(),
        )

        findings = _validate_design_plan_contract_closure(ctx, [label])

        self.assertIn(label, findings)
        self.assertIn("generated alias `def_affine_map`", findings[label][0])
        self.assertNotIn("closure_fp", ctx.design_plan_entries[label])

    def test_plan_closure_accepts_settled_mathlib_name(self) -> None:
        label = "def:consumer"
        ctx = SimpleNamespace(
            nodes={
                "def:affine-map": node(
                    "def:affine-map", mathlibok=True, lean_decl="AffineMap"
                ),
                label: node(label, uses={"def:affine-map"}),
            },
            stmt_fps={label: "consumer-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "consumer-v1",
                    "target_signature": "def def_consumer : AffineMap",
                    "helpers": [],
                    "decisions": [],
                }
            },
            design_plan="",
            paper_text="",
            telemetry=FakeTelemetry(),
        )

        self.assertEqual(
            _validate_design_plan_contract_closure(ctx, [label]),
            {},
        )
        self.assertIn("closure_fp", ctx.design_plan_entries[label])

    def test_plan_closure_observes_missing_dependencies_without_blocking(self) -> None:
        left = "def:left"
        right = "def:right"
        consumer = "lem:consumer"
        ctx = SimpleNamespace(
            nodes={
                left: node(left),
                right: node(right),
                consumer: node(consumer, uses={left, right}),
            },
            design_plan_entries={
                left: {"target_signature": "def def_left : Nat", "helpers": []},
                right: {"target_signature": "def def_right : Nat", "helpers": []},
                consumer: {
                    "target_signature": "theorem lem_consumer : True",
                    "helpers": [],
                },
            },
        )

        details = _design_plan_dependency_closure_details(ctx, consumer)

        self.assertEqual(
            set(details["missing"]),
            {f"{left} -> `def_left`", f"{right} -> `def_right`"},
        )
        self.assertEqual(set(details["generated_providers"]), {left, right})
        self.assertEqual(
            _design_plan_contract_closure_findings(ctx, [consumer]),
            {},
        )

    def test_missing_dependency_observation_blocks_neither_contract(self) -> None:
        provider = "def:provider"
        consumer = "lem:consumer"
        ctx = SimpleNamespace(
            nodes={
                provider: node(provider),
                consumer: node(consumer, uses={provider}),
            },
            design_plan_entries={
                provider: {
                    "target_signature": "def def_provider : Nat",
                    "helpers": [],
                },
                consumer: {
                    "target_signature": "theorem lem_consumer : True",
                    "helpers": [],
                },
            },
        )

        findings = _design_plan_contract_closure_findings(ctx, [consumer])
        components = _design_plan_closure_repair_components(ctx, findings)

        self.assertEqual(findings, {})
        self.assertEqual(components, [])
        self.assertEqual(_closure_blocked_labels(ctx, findings), set())

    def test_missing_member_still_repairs_provider_and_consumer_atomically(self) -> None:
        provider = "def:provider"
        consumer = "lem:consumer"
        ctx = SimpleNamespace(
            nodes={
                provider: node(provider),
                consumer: node(consumer, uses={provider}),
            },
            design_plan_entries={
                provider: {
                    "target_signature": "structure def_provider where\n  value : Nat",
                    "helpers": [],
                },
                consumer: {
                    "target_signature": (
                        "theorem lem_consumer : "
                        "def_provider.missing = def_provider.missing"
                    ),
                    "helpers": [],
                },
            },
        )

        findings = _design_plan_contract_closure_findings(ctx, [consumer])
        components = _design_plan_closure_repair_components(ctx, findings)

        self.assertEqual(set(components[0]), {provider, consumer})
        self.assertEqual(
            _closure_blocked_labels(ctx, findings), {provider, consumer}
        )

    def test_unauthorized_missing_member_does_not_block_provider(self) -> None:
        provider = "def:provider"
        consumer = "lem:consumer"
        ctx = SimpleNamespace(
            nodes={
                provider: node(provider),
                consumer: node(consumer),
            },
            design_plan_entries={
                provider: {
                    "target_signature": "structure def_provider where\n  value : Nat",
                    "helpers": [],
                },
                consumer: {
                    "target_signature": (
                        "theorem lem_consumer : "
                        "def_provider.invented = def_provider.invented"
                    ),
                    "helpers": [],
                },
            },
        )

        findings = _design_plan_contract_closure_findings(ctx, [consumer])
        components = _design_plan_closure_repair_components(ctx, findings)

        self.assertIn(consumer, findings)
        self.assertNotIn("exposes no such member", "\n".join(findings[consumer]))
        self.assertEqual(components, [[consumer]])
        self.assertEqual(_closure_blocked_labels(ctx, findings), {consumer})

    def test_plan_closure_ignores_proof_only_dependencies(self) -> None:
        dependency = "def:proof-tool"
        consumer = "lem:consumer"
        proof_node = node(consumer, uses={dependency})
        proof_node.statement_uses = set()
        proof_node.proof_uses = {dependency}
        ctx = SimpleNamespace(
            nodes={dependency: node(dependency), consumer: proof_node},
            design_plan_entries={
                dependency: {
                    "target_signature": "def def_proof_tool : Nat",
                    "helpers": [],
                },
                consumer: {
                    "target_signature": "theorem lem_consumer : True",
                    "helpers": [],
                },
            },
        )

        self.assertEqual(
            _design_plan_contract_closure_findings(ctx, [consumer]),
            {},
        )

    def test_plan_closure_counts_typed_helper_member_dependencies(self) -> None:
        dependency = "def:network"
        consumer = "def:consumer"
        ctx = SimpleNamespace(
            nodes={
                dependency: node(dependency),
                consumer: node(consumer, uses={dependency}),
            },
            design_plan_entries={
                dependency: {
                    "target_signature": "def def_network : Nat",
                    "helpers": [],
                },
                consumer: {
                    "target_signature": "def def_consumer : ConsumerInterface",
                    "helpers": [
                        {
                            "name": "ConsumerInterface",
                            "kind": "structure",
                            "members": [
                                {"name": "network", "type": "def_network = 0"}
                            ],
                            "required_members": ["network"],
                        }
                    ],
                },
            },
        )

        self.assertEqual(
            _design_plan_contract_closure_findings(ctx, [consumer]),
            {},
        )

    def test_plan_closure_rejects_target_helper_cycle_before_generation(self) -> None:
        label = "def:network"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "target_signature": "def def_network : NetworkInterface",
                    "helpers": [
                        {
                            "name": "NetworkInterface",
                            "kind": "structure",
                            "members": [
                                {"name": "owner", "type": "def_network = def_network"}
                            ],
                            "required_members": ["owner"],
                        }
                    ],
                }
            },
        )

        findings = _design_plan_contract_closure_findings(ctx, [label])

        self.assertIn(label, findings)
        self.assertIn(
            "def_network -> NetworkInterface -> def_network",
            "\n".join(findings[label]),
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

    def test_statement_replacement_filters_unavailable_import_after_merge(self) -> None:
        original = _parse_module(
            "import Mathlib.Data.Nat.Basic\n\n"
            "theorem lem_target : True := by sorry\n"
        )
        replacement = (
            "import Mathlib.Data.Polynomial.Basic\n\n"
            "theorem lem_target : True := by trivial\n"
        )
        unavailable: set[str] = set()

        with patch(
            "formalize_blueprint._missing_olean_imports",
            return_value=["import Mathlib.Data.Polynomial.Basic"],
        ):
            patched = _apply_skeleton_replacements(
                original,
                ["lem:target"],
                ["lem:target"],
                replacement,
                unavailable_imports=unavailable,
            )

        self.assertIsNotNone(patched)
        assert patched is not None
        self.assertEqual(patched.imports, ["import Mathlib.Data.Nat.Basic"])
        self.assertEqual(
            unavailable, {"import Mathlib.Data.Polynomial.Basic"}
        )
        self.assertIn("by trivial", patched.decls[0].text)

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

    def test_multi_line_docstring_is_one_declaration_prefix(self) -> None:
        """Historical shape from simplex `run-20260807-102400`.

        The `def:support-newton` patch at `+4191s` was discarded with
        "unsupported module-level command(s)" naming the continuation lines of
        its own docstring, because `_DECL_PREFIX_RE` only matched a single-line
        `/-- ... -/`.
        """
        nodes = {"def:support-newton": node("def:support-newton")}
        ctx = SimpleNamespace(nodes=nodes)
        canonical = _canonicalize_model_lean(
            ctx,
            nodes,
            """import Mathlib.Data.Real.Basic

/-- Public interface: for a CPWL function `f` (see `def_cpwl`) on `R^n` and a
polytope `P` (see `def_polytope`), this is the proposition that `f` is convex
and positively homogeneous with `f = h_P`, and that `P` is the unique such
polytope. -/
def def_support_newton (n : Nat) : Prop := sorry
""",
        )
        parsed = canonical.parsed
        self.assertEqual(parsed.preamble, [])
        self.assertEqual([decl.name for decl in parsed.decls], ["def_support_newton"])
        self.assertIn("Public interface", parsed.decls[0].text)

    def test_single_line_docstring_prefix_still_parses(self) -> None:
        parsed = _parse_module(
            "/-- One-line doc. -/\ndef def_base : Nat := sorry\n"
        )
        self.assertEqual(parsed.preamble, [])
        self.assertEqual([decl.name for decl in parsed.decls], ["def_base"])

    def test_nested_block_comment_does_not_split_a_declaration(self) -> None:
        parsed = _parse_module(
            "/-- outer /- inner -/ still outer\nmore text -/\n"
            "def def_base : Nat := sorry\n"
        )
        self.assertEqual(parsed.preamble, [])
        self.assertEqual([decl.name for decl in parsed.decls], ["def_base"])

    def test_declaration_keyword_inside_docstring_is_not_a_declaration(self) -> None:
        parsed = _parse_module(
            "/-- We explain why\ndef bogus is only prose here\n-/\n"
            "def def_base : Nat := sorry\n"
        )
        self.assertEqual([decl.name for decl in parsed.decls], ["def_base"])

    def test_non_comment_module_prose_remains_invalid_preamble(self) -> None:
        nodes = {"def:base": node("def:base")}
        ctx = SimpleNamespace(nodes=nodes)
        with self.assertRaises(ValueError) as caught:
            _canonicalize_model_lean(
                ctx,
                nodes,
                "Here is the declaration you asked for:\n"
                "def def_base : Nat := sorry\n",
            )
        self.assertIn("unsupported module-level command", str(caught.exception))

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

    def test_unique_bare_planned_helper_is_canonicalized_downstream(self) -> None:
        provider = "def:maxn"
        consumer = "def:p1"
        ctx = SimpleNamespace(
            name="simplex",
            nodes={
                provider: node(provider),
                consumer: node(consumer, uses={provider}),
            },
            design_plan_entries={
                provider: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_maxn : MaxNInterface",
                    "helpers": [
                        {
                            "name": "MaxNInterface",
                            "kind": "structure",
                            "members": [{"name": "MAX", "type": "Nat"}],
                        }
                    ],
                },
                consumer: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "def def_p1 (m : MaxNInterface) : P1Interface m"
                    ),
                    "helpers": [
                        {
                            "name": "P1Interface",
                            "kind": "structure",
                            "members": [{"name": "value", "type": "Nat"}],
                        }
                    ],
                },
            },
        )
        canonical_provider = _canonicalize_model_lean(
            ctx,
            [provider],
            "structure MaxNInterface where\n"
            "  MAX : Nat\n\n"
            "def def_maxn : MaxNInterface := sorry\n",
        ).parsed
        maxn_helper = canonical_provider.decls[0].name or ""
        canonical_consumer = _canonicalize_model_lean(
            ctx,
            [consumer],
            "structure P1Interface (m : MaxNInterface) where\n"
            "  value : Nat\n\n"
            "def def_p1 (m : MaxNInterface) : P1Interface m := sorry\n",
        ).parsed
        downstream_code = "\n".join(
            declaration.text for declaration in canonical_consumer.decls
        )
        self.assertIn(maxn_helper, downstream_code)
        self.assertNotRegex(downstream_code, r"(?<!_)\bMaxNInterface\b")

    def test_helper_alias_does_not_rename_same_named_class_field(self) -> None:
        """Regression for simplex run-20260731-025106's weightOf loop."""
        label = "lem:ahm-lower-bound"
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "theorem lem_ahm_lower_bound : True",
                    "helpers": [
                        {
                            "name": "weightOf",
                            "kind": "class",
                            "members": [
                                {
                                    "name": "weightOf",
                                    "type": "Nat -> Nat -> Prop",
                                }
                            ],
                            "required_members": ["weightOf"],
                        }
                    ],
                }
            },
        )
        canonical = _canonicalize_model_lean(
            ctx,
            [label],
            "class weightOf where\n"
            "  weightOf : Nat -> Nat -> Prop\n\n"
            "theorem lem_ahm_lower_bound : True := sorry\n",
        )
        code = "\n\n".join(decl.text for decl in canonical.parsed.decls)
        helper_name = canonical.parsed.decls[0].name or ""

        self.assertRegex(helper_name, r"^_autobp_[0-9a-f]{12}_weightOf$")
        self.assertIn(f"class {helper_name} where", code)
        self.assertIn("\n  weightOf : Nat -> Nat -> Prop", code)
        self.assertNotIn(f"\n  {helper_name} :", code)
        self.assertEqual(
            _skeleton_deterministic_findings(code, ctx, [label]), []
        )

    def test_helper_alias_respects_dependent_member_shadowing(self) -> None:
        """Regression for run-20260801-074355's density-interface loop."""
        label = "def:positive-loewner-density"
        ctx = SimpleNamespace(
            name="unconditional-unclonable-encryption",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "def def_positive_loewner_density : "
                        "PositiveLoewnerDensityInterface"
                    ),
                    "helpers": [
                        {
                            "name": "DensityOperator",
                            "kind": "structure",
                            "members": [
                                {"name": "space", "type": "Nat"},
                            ],
                        },
                        {
                            "name": "PositiveLoewnerDensityInterface",
                            "kind": "structure",
                            "members": [
                                {
                                    "name": "DensityOperator",
                                    "type": "Nat -> Type",
                                },
                                {
                                    "name": "density_to_value",
                                    "type": "forall n, DensityOperator n -> Nat",
                                },
                            ],
                        },
                    ],
                }
            },
        )
        canonical = _canonicalize_model_lean(
            ctx,
            [label],
            "structure DensityOperator (n : Nat) where\n"
            "  space : Nat\n\n"
            "structure PositiveLoewnerDensityInterface where\n"
            "  DensityOperator : Nat -> Type\n"
            "  density_to_value : forall n, DensityOperator n -> Nat\n\n"
            "def def_positive_loewner_density : "
            "PositiveLoewnerDensityInterface := sorry\n",
        ).parsed

        density_helper = next(
            decl for decl in canonical.decls
            if (decl.name or "").endswith("_DensityOperator")
        )
        interface = next(
            decl for decl in canonical.decls
            if (decl.name or "").endswith("_PositiveLoewnerDensityInterface")
        )
        target = next(
            decl for decl in canonical.decls
            if decl.name == "def_positive_loewner_density"
        )

        self.assertNotEqual(density_helper.name, "DensityOperator")
        self.assertIn("DensityOperator : Nat -> Type", interface.text)
        self.assertIn(
            "forall n, DensityOperator n -> Nat", interface.text
        )
        self.assertNotIn(density_helper.name or "", interface.text)
        self.assertIn(interface.name or "", target.text)

    def test_ambiguous_bare_planned_helper_is_not_guessed(self) -> None:
        labels = ["def:left", "def:right", "def:consumer"]
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label) for label in labels},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "helpers": (
                        [{"name": "Interface", "kind": "structure", "members": []}]
                        if label != "def:consumer"
                        else []
                    ),
                }
                for label in labels
            },
        )
        parsed = _canonicalize_model_lean(
            ctx,
            ["def:consumer"],
            "def def_consumer (_x : Interface) : Type := sorry\n",
        ).parsed
        self.assertIn("Interface", parsed.decls[0].text)

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

    def test_phase1_preserves_inferred_abbrev_to_owned_structural_contract(self) -> None:
        label = "def:chain"
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={},
            semantic_plan_entries={
                label: {
                    "representation": "A chain packaged by a named structure.",
                    "obligations": ["Expose every stored stage."],
                }
            },
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )
        response = """structure ChainInterface (n : Nat) where
  stage : Fin n -> Nat

abbrev def_chain (n : Nat) := ChainInterface n
"""

        canonical = _ingest_model_lean(
            ctx,
            [label],
            response,
            realize_contracts=True,
            defer_phase1_bodies=True,
        )
        target = next(
            decl for decl in canonical.parsed.decls if decl.name == _lean_name(label)
        )

        self.assertIn(":=", target.text)
        self.assertNotIn(":= sorry", target.text)
        self.assertIn("ChainInterface", target.text)
        self.assertIn("ChainInterface", ctx.design_plan_entries[label]["target_signature"])

    def test_phase1_still_defers_inferred_ordinary_abbrev_body(self) -> None:
        label = "def:value"
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            design_plan_entries={},
            semantic_plan_entries={},
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )

        canonical = _ingest_model_lean(
            ctx,
            [label],
            "abbrev def_value := Nat\n",
            defer_phase1_bodies=True,
        )
        target = canonical.parsed.decls[0]

        self.assertEqual(target.text, "abbrev def_value := sorry")

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

    def test_phase1_ingestion_defers_historical_cpwl_predicate_body(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "cpwl_predicate_body_deferral.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            design_plan_entries={},
            semantic_plan_entries={
                label: {
                    "representation": "predicate: continuous and affine on pieces"
                }
            },
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )

        canonical = _ingest_model_lean(
            ctx,
            [label],
            "```lean\n" + fixture["completed_predicate"] + "\n```",
            defer_phase1_bodies=True,
        )
        target = next(
            decl
            for decl in canonical.parsed.decls
            if decl.name == _lean_name(label)
        )

        self.assertEqual(target.text, fixture["expected_deferred"])
        self.assertEqual(
            _phase1_target_interface_text(target), fixture["expected_header"]
        )
        self.assertNotIn("Continuous f", target.text)
        events = [
            payload
            for event, payload in ctx.telemetry.events
            if event == "phase1_model_body_deferred"
        ]
        self.assertEqual(len(events), 1)
        self.assertEqual(events[0]["declarations"], [_lean_name(label)])

    def test_phase1_preserves_terminal_sorry_contracts_with_outer_let(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "terminal_sorry_outer_let.json"
            ).read_text(encoding="utf-8")
        )
        for case in fixture["cases"]:
            with self.subTest(label=case["label"]):
                ctx = SimpleNamespace(
                    name="outer-let-replay",
                    nodes={case["label"]: node(case["label"])},
                    design_plan_entries={},
                    semantic_plan_entries={},
                    unavailable_imports=set(),
                    telemetry=FakeTelemetry(),
                )

                canonical = _ingest_model_lean(
                    ctx,
                    [case["label"]],
                    "```lean\n" + case["declaration"] + "\n```",
                    defer_phase1_bodies=True,
                )
                target = next(
                    decl
                    for decl in canonical.parsed.decls
                    if decl.name == _lean_name(case["label"])
                )

                self.assertEqual(target.text, case["declaration"])
                self.assertEqual(
                    _phase1_target_interface_text(target), case["expected_header"]
                )
                self.assertEqual(_decl_interface_text(target), case["expected_header"])
                self.assertEqual(
                    _decl_signatures(case["declaration"]), case["expected_header"]
                )
                self.assertIn("let", _planned_target_result_type(
                    target.text, _lean_name(case["label"])
                ))
                self.assertFalse(
                    any(
                        event == "phase1_model_body_deferred"
                        for event, _payload in ctx.telemetry.events
                    )
                )

    def test_phase1_still_defers_a_completed_definition_body(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "terminal_sorry_outer_let.json"
            ).read_text(encoding="utf-8")
        )["completed_body_control"]
        ctx = SimpleNamespace(
            name="completed-body-control",
            nodes={fixture["label"]: node(fixture["label"])},
            design_plan_entries={},
            semantic_plan_entries={},
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )

        canonical = _ingest_model_lean(
            ctx,
            [fixture["label"]],
            "```lean\n" + fixture["declaration"] + "\n```",
            defer_phase1_bodies=True,
        )
        target = next(
            decl
            for decl in canonical.parsed.decls
            if decl.name == _lean_name(fixture["label"])
        )

        self.assertEqual(target.text, fixture["expected_deferred"])

    def test_phase1_ingestion_normalizes_historical_prop_structure(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "cpwl_predicate_body_deferral.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            design_plan_entries={},
            semantic_plan_entries={label: {"representation": "predicate"}},
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )

        canonical = _ingest_model_lean(
            ctx,
            [label],
            "```lean\n" + fixture["malformed_predicate_structure"] + "\n```",
            defer_phase1_bodies=True,
        )
        target = next(
            decl
            for decl in canonical.parsed.decls
            if decl.name == _lean_name(label)
        )

        self.assertEqual(target.kind, "def")
        self.assertEqual(target.text, fixture["expected_deferred"])
        self.assertNotIn("continuous :", target.text)

    def test_phase1_ingestion_preserves_transparent_structural_alias(self) -> None:
        label = "def:finite-subdivision"
        helper = "FiniteSubdivisionInterface"
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "helpers": [
                        {
                            "name": helper,
                            "kind": "structure",
                            "members": [{"name": "cells", "type": "Finset Nat"}],
                            "required_members": ["cells"],
                        }
                    ],
                }
            },
            semantic_plan_entries={},
            unavailable_imports=set(),
            telemetry=FakeTelemetry(),
        )
        canonical = _ingest_model_lean(
            ctx,
            [label],
            "```lean\n"
            f"structure {helper} (n : Nat) where\n"
            "  cells : Finset Nat\n\n"
            f"def {_lean_name(label)} (n : Nat) : Type := {helper} n\n"
            "```",
            defer_phase1_bodies=True,
        )
        target = next(
            decl
            for decl in canonical.parsed.decls
            if decl.name == _lean_name(label)
        )

        self.assertNotIn(":= sorry", target.text)
        self.assertIn(": Type :=", target.text)

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
            retry_attempted_tier="base",
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
        self.assertEqual(
            _retry_next_tier(ctx, label, "phase1_statement"),
            "escalation",
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

    def test_exact_plan_realization_detects_current_semantic_plan_defect(self) -> None:
        label = "def:polyhedral-cell"
        ctx = SimpleNamespace(
            name="simplex",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": (
                        "def def_polyhedral_cell (n : ℕ) (C : Set ℝ) : Prop"
                    ),
                    "helpers": [],
                    "decisions": [
                        "Full-dimensionality is intentionally separate."
                    ],
                }
            },
        )
        code = "def def_polyhedral_cell (n : ℕ) (C : Set ℝ) : Prop := sorry"

        self.assertTrue(_candidate_exactly_realizes_plan(ctx, label, code))
        self.assertEqual(
            _plan_realized_semantic_rejections(ctx, [label], code), {label}
        )

    def test_plan_realization_rejects_changed_target_or_helper_type(self) -> None:
        label = "def:join"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_join : Prop",
                    "helpers": [{
                        "name": "JoinInterface",
                        "kind": "structure",
                        "members": [{"name": "join", "type": "Nat → Nat"}],
                        "required_members": ["join"],
                    }],
                }
            },
        )
        canonical = next(iter(_planned_helper_owner_by_name(ctx, [label])))
        wrong_target = (
            f"structure {canonical} where\n  join : Nat → Nat\n\n"
            "def def_join : True := sorry"
        )
        wrong_helper = (
            f"structure {canonical} where\n  join : Nat → Int\n\n"
            "def def_join : Prop := sorry"
        )
        exact_helper = (
            f"structure {canonical} where\n  join : Nat → Nat\n\n"
            "def def_join : Prop := sorry"
        )

        self.assertTrue(
            _candidate_exactly_realizes_plan(ctx, label, exact_helper)
        )
        self.assertFalse(
            _candidate_exactly_realizes_plan(ctx, label, wrong_target)
        )
        self.assertFalse(
            _candidate_exactly_realizes_plan(ctx, label, wrong_helper)
        )

    def test_revised_plan_does_not_take_immediate_revision_route_twice(self) -> None:
        label = "lem:claim"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "semantic_revision_count": 1,
                    "target_signature": "theorem lem_claim : True",
                    "helpers": [],
                }
            },
        )

        self.assertFalse(
            _candidate_exactly_realizes_plan(
                ctx, label, "theorem lem_claim : True := sorry"
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

    def test_bisection_partitions_only_the_failed_group(self) -> None:
        labels = ["failed-a", "failed-b"]
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            telemetry=telemetry,
            section_size=12,
            effective_section_size=6,
            section_clean_streak=1,
            stmt_fps={label: f"fp-{label}" for label in labels},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
        )
        route = _route_lean_generation_failure(labels)
        request = RepairRequest(
            "unattributed two-node failure",
            labels,
            failure_route=route,
            authorizes_blueprint_repair=False,
        )

        _apply_phase1_retry_scheduling(ctx, request)

        self.assertEqual(ctx.effective_section_size, 6)
        self.assertEqual(ctx.section_clean_streak, 1)
        self.assertEqual(
            ctx.local_group_partitions["failed-a"]["group"], ["failed-a"]
        )
        self.assertEqual(
            ctx.local_group_partitions["failed-b"]["group"], ["failed-b"]
        )
        order = ["easy-a", "easy-b", "failed-a", "failed-b", "easy-c", "easy-d"]
        self.assertEqual(
            _next_phase1_group(
                order, 0, 6, set(), ctx.local_group_partitions
            ),
            ["easy-a", "easy-b"],
        )
        self.assertEqual(
            _next_phase1_group(
                order, 2, 6, set(), ctx.local_group_partitions
            ),
            ["failed-a"],
        )
        self.assertEqual(
            _next_phase1_group(
                order, 3, 6, set(), ctx.local_group_partitions
            ),
            ["failed-b"],
        )
        self.assertEqual(
            _next_phase1_group(
                order, 4, 6, set(), ctx.local_group_partitions
            ),
            ["easy-c", "easy-d"],
        )

    def test_local_bisection_expires_when_a_statement_changes(self) -> None:
        labels = ["failed-a", "failed-b"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            telemetry=FakeTelemetry(),
            section_size=12,
            effective_section_size=6,
            section_clean_streak=0,
            stmt_fps={label: f"fp-{label}" for label in labels},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
        )
        request = RepairRequest(
            "unattributed two-node failure",
            labels,
            failure_route=_route_lean_generation_failure(labels),
            authorizes_blueprint_repair=False,
        )
        _apply_phase1_retry_scheduling(ctx, request)

        ctx.stmt_fps["failed-a"] = "changed"
        stale = _prune_stale_local_group_partitions(ctx)

        self.assertIn("failed-a", stale)
        self.assertNotIn("failed-a", ctx.local_group_partitions)
        self.assertIn("failed-b", ctx.local_group_partitions)

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

    def test_phase1_allows_placeholder_word_in_required_target_name(self) -> None:
        target = "remark_geometric_recursion_gap"
        findings = _skeleton_code_findings(
            f"theorem {target} (n : Nat) : n = n := by sorry\n",
            {target: "remark"},
            {target: "remark:geometric-recursion-gap"},
        )

        self.assertFalse(
            any(finding.category == "placeholder_name" for finding in findings)
        )
        self.assertFalse(
            any("placeholder declaration name" in finding.message for finding in findings)
        )

    def test_phase1_still_rejects_placeholder_word_in_planned_helper_name(self) -> None:
        helper = "local_gap_helper"
        findings = _skeleton_code_findings(
            f"structure {helper} where\n"
            "  value : Nat\n\n"
            "theorem lem_root : True := by sorry\n",
            {"lem_root": "lemma"},
            {"lem_root": "lem:root"},
            {helper: "lem:root"},
        )

        self.assertTrue(
            any(
                finding.lean_name == helper
                and "placeholder declaration name" in finding.message
                for finding in findings
            )
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

    def test_phase2_definition_body_refreshes_importable_object(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"def:object": node("def:object")},
            telemetry=telemetry,
            lean_command=["lean"],
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            source = "def def_object : Nat := by exact 1\n"
            path.write_text(source, encoding="utf-8")
            section = Section(
                1,
                ["def:object"],
                path,
                "Generated.Skeleton01",
                [],
                compile_fingerprint="phase1-object",
            )
            outcome = SectionProofOutcome(
                section=section, proved=["def:object"]
            )
            attempt = LeanAttempt(
                ok=True,
                command=["lean"],
                stdout="",
                stderr="",
                duration_s=0.25,
            )
            with patch(
                "formalize_blueprint._compile_section_olean",
                return_value=attempt,
            ) as compile_object, patch(
                "formalize_blueprint._save_ctx_state"
            ) as save_state:
                _persist_phase2_section_outcome(
                    ctx,
                    outcome,
                    [section],
                    original_source="def def_object : Nat := sorry\n",
                    original_compile_fingerprint="phase1-object",
                )

            compile_object.assert_called_once_with(
                section, ["lean"], [section]
            )
            save_state.assert_called_once_with(ctx, [section])
            self.assertEqual(outcome.proved, ["def:object"])
            self.assertTrue(
                any(
                    event == "phase2_definition_object_refresh"
                    and fields["status"] == "success"
                    for event, fields in telemetry.events
                )
            )

    def test_phase2_theorem_proof_keeps_frozen_object_fast_path(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"lem:result": node("lem:result")},
            telemetry=telemetry,
            lean_command=["lean"],
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            source = "theorem lem_result : True := by trivial\n"
            path.write_text(source, encoding="utf-8")
            section = Section(
                1,
                ["lem:result"],
                path,
                "Generated.Skeleton01",
                [],
                compile_fingerprint="phase1-object",
            )
            outcome = SectionProofOutcome(
                section=section, proved=["lem:result"]
            )
            with patch(
                "formalize_blueprint._compile_section_olean"
            ) as compile_object, patch(
                "formalize_blueprint._save_ctx_state"
            ) as save_state:
                _persist_phase2_section_outcome(
                    ctx,
                    outcome,
                    [section],
                    original_source=source,
                    original_compile_fingerprint="phase1-object",
                )

            compile_object.assert_not_called()
            save_state.assert_called_once_with(ctx, [section])

    def test_theorem_proof_edit_preserves_object_fingerprint(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "set_option autoImplicit false\n"
                "theorem lem_result (n : Nat) : n = n := sorry\n",
                encoding="utf-8",
            )
            section = Section(1, ["lem:result"], path, "Generated.S1", [])
            with patch(
                "formalize_blueprint._lean_environment_fingerprint",
                return_value="environment",
            ):
                phase1_object = _section_compile_fingerprint(
                    section, ["lean"], [section]
                )
                exact_phase1 = _section_exact_source_fingerprint(path)
                path.write_text(
                    "set_option autoImplicit false\n"
                    "theorem lem_result (n : Nat) : n = n := by rfl\n",
                    encoding="utf-8",
                )
                phase2_object = _section_compile_fingerprint(
                    section, ["lean"], [section]
                )

            self.assertEqual(phase2_object, phase1_object)
            self.assertNotEqual(_section_exact_source_fingerprint(path), exact_phase1)

    def test_statement_and_definition_body_edits_invalidate_object_fingerprint(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            theorem_path = root / "Theorem.lean"
            definition_path = root / "Definition.lean"
            theorem_path.write_text(
                "theorem lem_result (n : Nat) : n = n := sorry\n",
                encoding="utf-8",
            )
            definition_path.write_text(
                "def def_value : Nat := sorry\n", encoding="utf-8"
            )
            theorem = Section(1, ["lem:result"], theorem_path, "Generated.T", [])
            definition = Section(2, ["def:value"], definition_path, "Generated.D", [])
            with patch(
                "formalize_blueprint._lean_environment_fingerprint",
                return_value="environment",
            ):
                theorem_before = _section_compile_fingerprint(theorem, ["lean"])
                definition_before = _section_compile_fingerprint(definition, ["lean"])
                theorem_path.write_text(
                    "theorem lem_result (n : Nat) : n + 0 = n := by simp\n",
                    encoding="utf-8",
                )
                definition_path.write_text(
                    "def def_value : Nat := 1\n", encoding="utf-8"
                )
                theorem_after = _section_compile_fingerprint(theorem, ["lean"])
                definition_after = _section_compile_fingerprint(definition, ["lean"])

            self.assertNotEqual(theorem_after, theorem_before)
            self.assertNotEqual(definition_after, definition_before)

    def test_legacy_object_fingerprints_migrate_without_compilation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            provider_path = root / "Provider.lean"
            importer_path = root / "Importer.lean"
            provider_path.write_text(
                "theorem provider : True := by trivial\n", encoding="utf-8"
            )
            importer_path.write_text(
                "import Generated.Provider\n"
                "theorem importer : True := by trivial\n",
                encoding="utf-8",
            )
            provider = Section(
                1, ["lem:provider"], provider_path, "Generated.Provider", [],
                compile_fingerprint="legacy-provider",
            )
            importer = Section(
                2, ["lem:importer"], importer_path, "Generated.Importer",
                ["Generated.Provider"], compile_fingerprint="legacy-importer",
            )
            with patch(
                "formalize_blueprint._section_objects_exist", return_value=True
            ), patch(
                "formalize_blueprint._lean_environment_fingerprint",
                return_value="environment",
            ), patch(
                "formalize_blueprint._compile_module_olean"
            ) as compile_object:
                migrated = _migrate_section_compile_fingerprints(
                    [importer, provider], ["lean"]
                )

            self.assertEqual(migrated, 2)
            self.assertTrue(provider.compile_fingerprint.startswith("opaque-theorem-v2:"))
            self.assertTrue(importer.compile_fingerprint.startswith("opaque-theorem-v2:"))
            compile_object.assert_not_called()

    def test_phase2_definition_object_failure_rolls_back_section(self) -> None:
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={"def:object": node("def:object")},
            telemetry=telemetry,
            lean_command=["lean"],
        )
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            old_source = "def def_object : Nat := sorry\n"
            path.write_text(
                "def def_object : Nat := by exact 1\n", encoding="utf-8"
            )
            section = Section(
                1,
                ["def:object"],
                path,
                "Generated.Skeleton01",
                [],
                compile_fingerprint="phase1-object",
            )
            outcome = SectionProofOutcome(
                section=section, proved=["def:object"]
            )
            failed = LeanAttempt(
                ok=False,
                command=["lean"],
                stdout="",
                stderr="object failed",
                duration_s=0.25,
            )
            restored = LeanAttempt(
                ok=True,
                command=["lean"],
                stdout="",
                stderr="",
                duration_s=0.1,
            )
            with patch(
                "formalize_blueprint._compile_section_olean",
                side_effect=[failed, restored],
            ), patch("formalize_blueprint._save_ctx_state"):
                _persist_phase2_section_outcome(
                    ctx,
                    outcome,
                    [section],
                    original_source=old_source,
                    original_compile_fingerprint="phase1-object",
                )

            self.assertEqual(path.read_text(encoding="utf-8"), old_source)
            self.assertEqual(outcome.proved, [])
            self.assertIn("def:object", outcome.failed)
            self.assertEqual(section.compile_fingerprint, "phase1-object")

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

    def test_phase1_decomposition_refusal_gets_fresh_neutral_adjudication(self) -> None:
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
        refusal = CallResult(
            status="ok",
            text=(
                "NEEDS-DECOMPOSITION: "
                + json.dumps(
                    {
                        "label": "lem:target",
                        "missing_helpers": ["an explicit intermediate equality"],
                        "reason": "the blueprint skips the equality",
                    }
                )
            ),
        )
        accepted = CallResult(
            status="ok",
            text="```lean\ntheorem lem_target : True := by sorry\n```",
        )

        with patch(
            "formalize_blueprint._bulk_skeleton_prompt", return_value="initial prompt"
        ), patch(
            "formalize_blueprint._skeleton_prompt", return_value="neutral adjudication"
        ) as retry_prompt, patch(
            "formalize_blueprint._call_model", side_effect=[refusal, accepted]
        ) as call_model:
            result = _generate_phase1_statement_group(
                ctx, sec, ["lem:target"], [sec], [], parsed
            )

        self.assertEqual(call_model.call_count, 2)
        self.assertFalse(call_model.call_args_list[0].kwargs["force_fresh"])
        self.assertTrue(call_model.call_args_list[1].kwargs["force_fresh"])
        self.assertFalse(call_model.call_args_list[0].kwargs["escalated"])
        self.assertTrue(call_model.call_args_list[1].kwargs["escalated"])
        self.assertEqual(retry_prompt.call_args.kwargs["previous_code"], "")
        feedback = retry_prompt.call_args.kwargs["feedback"]
        self.assertIn("Adjudicate that diagnosis", feedback)
        self.assertIn("Do not assume it is correct", feedback)
        self.assertNotIn("one stronger attempt", feedback)
        declaration = next(
            decl for decl in result.decls if decl.name == "lem_target"
        )
        self.assertIn(": True", declaration.text)
        self.assertTrue(
            any(
                event == "phase1_decomposition_adjudication"
                and fields["forced_fresh_session"]
                for event, fields in telemetry.events
            )
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
        self.assertIn("def def_base : Nat := sorry", generated)
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

    def test_compound_repair_scope_excludes_separately_validated_edge(self) -> None:
        before_transaction = {
            "finite-register": node("finite-register"),
            "single-qubit": node("single-qubit"),
            "local-basis": node("local-basis"),
        }
        before_model = {
            "finite-register": node("finite-register"),
            "single-qubit": node("single-qubit"),
            "local-basis": node("local-basis", uses={"single-qubit"}),
        }
        after_model = {
            "finite-register": node(
                "finite-register",
                uses={"operator-space", "density", "partial-trace"},
            ),
            "operator-space": node("operator-space"),
            "density": node("density", uses={"operator-space"}),
            "partial-trace": node("partial-trace", uses={"operator-space"}),
            "single-qubit": node("single-qubit"),
            "local-basis": node("local-basis", uses={"single-qubit"}),
        }
        model_changed = {
            "finite-register",
            "operator-space",
            "density",
            "partial-trace",
        }
        deterministic_changed = {"local-basis"}

        old_merged_violations = _phase1_repair_scope_violations(
            before_transaction,
            after_model,
            ["finite-register"],
            model_changed | deterministic_changed,
        )

        violations = _phase1_repair_scope_violations(
            before_model,
            after_model,
            ["finite-register"],
            model_changed,
        )

        self.assertEqual(old_merged_violations, {"local-basis"})
        self.assertEqual(violations, set())

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

    def test_validator_marks_explicit_open_claim_without_matching_topology(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "explicit_open_claim.json"
            ).read_text(encoding="utf-8")
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            draft = root / "draft"
            src = draft / "blueprint" / "src"
            src.mkdir(parents=True)
            (src / "web.tex").write_text("", encoding="utf-8")
            content = "".join(
                f"\\begin{{{case['kind']}}}{case['statement']}"
                f"\\label{{{case['label']}}}\\end{{{case['kind']}}}\n"
                for case in fixture["cases"]
            )
            (src / "content.tex").write_text(content, encoding="utf-8")

            result = validate_blueprint(root, "paper", blueprint_dir=draft)

            self.assertTrue(result.ok, result.errors)
            for case in fixture["cases"]:
                with self.subTest(label=case["label"]):
                    self.assertEqual(
                        result.nodes[case["label"]].open_claim,
                        case["expected_open_claim"],
                    )

    def test_validator_preserves_notready_as_source_authority(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            draft = root / "draft"
            src = draft / "blueprint" / "src"
            src.mkdir(parents=True)
            (src / "web.tex").write_text("", encoding="utf-8")
            (src / "content.tex").write_text(
                "\\begin{lemma}Claim\\label{lem:pending}\\notready\\end{lemma}\n",
                encoding="utf-8",
            )

            result = validate_blueprint(root, "paper", blueprint_dir=draft)

            self.assertTrue(result.ok, result.errors)
            self.assertTrue(result.nodes["lem:pending"].notready)

    def test_directly_changed_section_keeps_graph_independent_declarations(self) -> None:
        telemetry = FakeTelemetry()
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "Skeleton01.lean"
            path.write_text(
                "def prefix : Nat := 1\n\n"
                "def changed : Nat := prefix\n\n"
                "def independent : Nat := prefix\n\n"
                "def suffix : Nat := changed\n",
                encoding="utf-8",
            )
            section = Section(
                1,
                ["prefix", "changed", "independent", "suffix"],
                path,
                "AutoBlueprint.Generated.Paper.Skeleton01",
                [],
            )
            ctx = SimpleNamespace(
                name="paper",
                nodes={
                    "prefix": node("prefix"),
                    "changed": node("changed", uses={"prefix"}),
                    "independent": node("independent", uses={"prefix"}),
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
            self.assertEqual(kept[0].labels, ["prefix", "independent"])
            self.assertFalse(kept[0].deferred)
            code = path.read_text(encoding="utf-8")
            self.assertIn("def prefix", code)
            self.assertIn("def independent", code)
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
            state_nodes = {
                "cached": node("cached"),
                "hard": node("hard"),
                "peer": node("peer"),
            }
            state_stmt_fps = {
                "cached": "statement",
                "hard": "hard-v1",
                "peer": "peer-v1",
            }
            state_contract_fps = {"cached": "contract"}
            phase2_epoch = _phase2_node_candidate_epoch(
                SimpleNamespace(
                    nodes=state_nodes,
                    stmt_fps=state_stmt_fps,
                    contract_fps=state_contract_fps,
                ),
                "peer",
            )
            with patch("formalize_blueprint._state_path", return_value=state):
                _save_state(
                    "paper",
                    [section],
                    state_stmt_fps,
                    state_contract_fps,
                    quarantined_labels={"hard"},
                    local_group_partitions={
                        "hard": {
                            "partition_id": "part-a",
                            "statement_fp": "hard-v1",
                            "statement_fps": {
                                "hard": "hard-v1",
                                "peer": "peer-v1",
                            },
                            "group": ["hard", "peer"],
                        },
                        "peer": {
                            "partition_id": "part-a",
                            "statement_fp": "peer-v1",
                            "statement_fps": {
                                "hard": "hard-v1",
                                "peer": "peer-v1",
                            },
                            "group": ["hard", "peer"],
                        },
                    },
                    generation_feedback={
                        "hard": {
                            "statement_fp": "hard-v1",
                            "evidence": "audit rejected the declaration",
                            "source": "deterministic_audit",
                        }
                    },
                    phase1_dependency_observations={
                        "hard": {
                            "statement_fp": "hard-v1",
                            "dependencies": ["peer"],
                            "candidate_hashes": ["candidate-reference-v1"],
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
                    phase2_node_candidates={
                        "peer": {
                            "epoch": phase2_epoch,
                            "code": "theorem peer : True := by trivial",
                            "candidate_hash": "phase2-candidate-hash",
                            "evidence": "exact Phase 2 compiler rejection",
                            "failure_kind": "lean_compile",
                            "failure_hash": "phase2-failure-hash",
                            "tier": "escalation",
                            "source": "phase2_correction_validation",
                            "revision": 2,
                            "seen_states": ["seen-v1"],
                            "attempted_corrections": ["correction-v1"],
                        }
                    },
                    phase1_exchange_history={
                        "exchange-v1": {
                            "labels": ["peer"],
                            "statement_fps": {"peer": "peer-v1"},
                            "plan_fps": {"peer": ""},
                            "candidate_sha256": "candidate-hash",
                            "purpose": "skeleton_declaration_patch",
                            "tier": "base",
                            "runner_spec": "codex:gpt-5.5",
                            "prompt_sha256": "prompt-hash",
                            "launches": 3,
                            "response_sha256s": ["response-hash"],
                            "statuses": ["ok", "ok"],
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
                            "helpers": [
                                {
                                    "name": "HardSurface",
                                    "kind": "structure",
                                    "declaration": (
                                        "structure HardSurface where\n  value : Nat"
                                    ),
                                    "members": [],
                                    "required_members": ["value"],
                                    "purpose": "exact candidate-owned helper",
                                }
                            ],
                            "decisions": ["exact contract"],
                            "semantic_revision_count": 1,
                            "closure_fp": "closed-plan-v1",
                            "origin": "phase1_candidate",
                        }
                    },
                    semantic_plan_entries={
                        "hard": {
                            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
                            "statement_fp": "hard-v1",
                            "representation": "A compact semantic choice.",
                            "vocabulary": [
                                {"name": "HardSurface", "purpose": "public data"}
                            ],
                            "obligations": ["preserve the hard claim"],
                            "provider_requirements": [],
                            "fallback": False,
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
                    blueprint_direct_generation={
                        "hard": {
                            "statement_fp": "hard-v1",
                            "source": "historical_semantic_exhaustion",
                            "evidence": "the corrected plan remained opaque",
                            "activations": 1,
                        }
                    },
                    repair_boundary_pending={
                        "mode": "repair",
                        "labels": ["hard"],
                        "statement_fps": {"hard": "hard-v1"},
                        "previous_statements": {"hard": "old hard statement"},
                        "evidence": "missing dependency",
                        "repair_roots": ["hard"],
                        "component_changed_labels": ["hard", "peer"],
                        "component_added_labels": ["peer"],
                        "require_component_closure": True,
                        "repair_labels": ["hard"],
                        "required_dependencies": {"hard": ["peer"]},
                    },
                    phase2_repair_queue=[
                        {
                            "request_id": "queued-repair-v1",
                            "labels": ["peer"],
                            "statement_fps": {"peer": "peer-before-repair"},
                            "evidence": "independent Phase 2 failure",
                            "decomposition_helpers": [],
                            "section_labels": ["peer"],
                            "context_labels": ["peer"],
                            "authorizes_blueprint_repair": True,
                            "failure_routes": [],
                            "plan_revision_required": False,
                            "required_dependencies": {},
                            "model_repair_labels": ["peer"],
                            "evidence_by_label": {
                                "peer": "independent Phase 2 failure"
                            },
                        }
                    ],
                    phase2_repair_active={
                        "request_id": "queued-repair-v1",
                        "stage": "verify",
                        "labels": ["peer"],
                        "verification_labels": ["peer"],
                    },
                    phase2_prerequisite_labels={"hard"},
                    phase2_started=True,
                    phase1_baseline_labels={"cached", "hard", "peer"},
                    effective_section_size=6,
                    refinement_order="top-down",
                )
            payload = json.loads(state.read_text(encoding="utf-8"))
            self.assertEqual(payload["version"], 29)
            self.assertTrue(payload["scheduler"]["diagnostic_evidence"])
            migrated_evidence = next(
                entry
                for entry in payload["scheduler"]["diagnostic_evidence"].values()
                if entry["kind"] == "deterministic"
            )
            self.assertEqual(migrated_evidence["kind"], "deterministic")
            self.assertEqual(migrated_evidence["lifetime"], "candidate")
            self.assertEqual(
                migrated_evidence["candidate_fp"], "working-hash"
            )
            self.assertEqual(payload["conjecture_policy"], "attempt")
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
                payload["scheduler"]["phase1_dependency_observations"]["hard"],
                {
                    "statement_fp": "hard-v1",
                    "dependencies": ["peer"],
                    "candidate_hashes": ["candidate-reference-v1"],
                },
            )
            self.assertEqual(
                payload["scheduler"]["phase2_node_candidates"]["peer"][
                    "evidence"
                ],
                "exact Phase 2 compiler rejection",
            )
            self.assertTrue(payload["scheduler"]["workflow"]["phase2_started"])
            self.assertEqual(
                payload["scheduler"]["workflow"]["phase1_baseline_labels"],
                ["cached", "hard", "peer"],
            )
            self.assertEqual(
                payload["scheduler"]["workflow"]["phase2_prerequisite_labels"],
                ["hard"],
            )
            self.assertEqual(
                payload["scheduler"]["repair_boundary_pending"]
                ["required_dependencies"],
                {"hard": ["peer"]},
            )
            self.assertEqual(
                payload["scheduler"]["repair_boundary_pending"]["repair_roots"],
                ["hard"],
            )
            self.assertEqual(
                payload["scheduler"]["repair_boundary_pending"]
                ["component_changed_labels"],
                ["hard", "peer"],
            )
            self.assertTrue(
                payload["scheduler"]["repair_boundary_pending"]
                ["require_component_closure"]
            )
            self.assertEqual(
                payload["scheduler"]["phase2_repair_queue"][0]["request_id"],
                "queued-repair-v1",
            )
            self.assertEqual(
                payload["scheduler"]["phase2_repair_active"]["stage"],
                "verify",
            )
            self.assertEqual(
                payload["scheduler"]["local_group_partitions"]["hard"]["group"],
                ["hard", "peer"],
            )
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
                payload["scheduler"]["phase1_exchange_history"]
                ["exchange-v1"]["launches"],
                3,
            )
            self.assertEqual(
                payload["scheduler"]["phase1_exchange_history"]
                ["exchange-v1"]["runner_spec"],
                "codex:gpt-5.5",
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
                payload["scheduler"]["design_plan_entries"]["hard"]["helpers"][0]
                ["declaration"],
                "structure HardSurface where\n  value : Nat",
            )
            self.assertEqual(
                payload["scheduler"]["design_plan_entries"]["hard"]["origin"],
                "phase1_candidate",
            )
            self.assertEqual(
                payload["scheduler"]["semantic_plan_entries"]["hard"]
                ["representation"],
                "A compact semantic choice.",
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
            self.assertEqual(
                payload["scheduler"]["blueprint_direct_generation"]["hard"]
                ["evidence"],
                "the corrected plan remained opaque",
            )
            self.assertTrue(payload["sections"][0]["deferred"])
            self.assertEqual(payload["sections"][0]["refined_labels"], [])

            ctx = SimpleNamespace(
                name="paper",
                nodes=state_nodes,
                stmt_fps=state_stmt_fps,
                contract_fps=state_contract_fps,
                quarantined_labels=set(),
                quarantine={},
                local_group_partitions={},
                generation_feedback={},
                generation_candidates={},
                phase1_exchange_history={},
                retry_lifecycle={},
                design_plan="",
                design_plan_entries={},
                semantic_plan_entries={},
                design_plan_alternates={},
                blueprint_direct_generation={},
                phase2_repair_queue=[],
                phase2_repair_active={},
                phase2_started=False,
                phase1_baseline_labels=set(),
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
            self.assertTrue(ctx.phase2_started)
            self.assertEqual(
                ctx.phase1_baseline_labels, {"cached", "hard", "peer"}
            )
            self.assertEqual(
                ctx.local_group_partitions["peer"]["group"], ["hard", "peer"]
            )
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
                ctx.phase1_exchange_history["exchange-v1"]
                ["response_sha256s"],
                ["response-hash"],
            )
            self.assertEqual(
                ctx.phase1_exchange_history["exchange-v1"]["launches"], 3
            )
            self.assertEqual(
                ctx.phase1_exchange_history["exchange-v1"]["runner_spec"],
                "codex:gpt-5.5",
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
                ctx.design_plan_entries["hard"]["helpers"][0]["declaration"],
                "structure HardSurface where\n  value : Nat",
            )
            self.assertEqual(
                ctx.design_plan_entries["hard"]["origin"], "phase1_candidate"
            )
            self.assertEqual(
                ctx.semantic_plan_entries["hard"]["representation"],
                "A compact semantic choice.",
            )
            self.assertEqual(
                ctx.design_plan_alternates["hard"]["target_signature"],
                "hard : False",
            )
            self.assertEqual(
                ctx.blueprint_direct_generation["hard"]["evidence"],
                "the corrected plan remained opaque",
            )
            self.assertEqual(ctx.repair_boundary_pending["mode"], "repair")
            self.assertEqual(
                ctx.repair_boundary_pending["required_dependencies"],
                {"hard": {"peer"}},
            )
            self.assertEqual(
                ctx.repair_boundary_pending["repair_roots"], ["hard"]
            )
            self.assertEqual(
                ctx.repair_boundary_pending["component_changed_labels"],
                ["hard", "peer"],
            )
            self.assertTrue(
                ctx.repair_boundary_pending["require_component_closure"]
            )
            self.assertEqual(
                ctx.phase2_repair_queue[0]["request_id"],
                "queued-repair-v1",
            )
            self.assertEqual(ctx.phase2_repair_active["stage"], "verify")
            self.assertEqual(
                ctx.phase2_node_candidates["peer"]["evidence"],
                "exact Phase 2 compiler rejection",
            )
            compile_mock.assert_not_called()

    def test_resume_discards_duplicate_phase2_owner_and_defers_importers(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "simplex_opaque_definition_prerequisite.json"
            ).read_text(encoding="utf-8")
        )["duplicate_resume_owner_case"]
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            generated = root / "generated"
            generated.mkdir()
            state = root / "skeleton_state.json"
            telemetry = FakeTelemetry()
            original = fixture["original_section"]
            duplicate = fixture["duplicate_section"]
            importer = fixture["importer_section"]
            original_path = generated / f"Skeleton{original['number']:02d}.lean"
            duplicate_path = generated / f"Skeleton{duplicate['number']:02d}.lean"
            importer_path = generated / f"Skeleton{importer['number']:02d}.lean"
            original_path.write_text(
                "def def_max_function : Nat := sorry\n", encoding="utf-8"
            )
            duplicate_path.write_text(
                "def def_max_function : Nat := 1\n", encoding="utf-8"
            )
            importer_path.write_text(
                "theorem lem_consumer : True := by trivial\n", encoding="utf-8"
            )
            for path in (original_path, duplicate_path, importer_path):
                path.with_suffix(".olean").write_bytes(b"object")
                path.with_suffix(".lake.olean").write_bytes(b"lake object")
            nodes = {
                "def:max-function": node("def:max-function"),
                "lem:consumer": node(
                    "lem:consumer", uses={"def:max-function"}
                ),
            }
            stmt_fps = {label: f"stmt:{label}" for label in nodes}
            contract_fps = {label: f"contract:{label}" for label in nodes}

            def section_entry(number, labels, path, imports=()):
                return {
                    "number": number,
                    "file": path.name,
                    "module": f"AutoBlueprint.Generated.Simplex.Skeleton{number:02d}",
                    "labels": labels,
                    "import_modules": list(imports),
                    "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                    "statement_fps": {
                        label: stmt_fps[label] for label in labels
                    },
                    "contract_fps": {
                        label: contract_fps[label] for label in labels
                    },
                    "deferred": False,
                    "refined_labels": labels,
                    "provisional_environment": False,
                    "generation_tier": "base",
                    "compile_fingerprint": "opaque-theorem-v2:test",
                }

            state.write_text(
                json.dumps(
                    {
                        "version": 29,
                        "refinement_order": PHASE1_STATEMENT_ORDER,
                        "conjecture_policy": "record",
                        "sections": [
                            section_entry(
                                original["number"],
                                original["labels"],
                                original_path,
                            ),
                            section_entry(
                                duplicate["number"],
                                duplicate["labels"],
                                duplicate_path,
                            ),
                            section_entry(
                                importer["number"],
                                importer["labels"],
                                importer_path,
                                importer["imports"],
                            ),
                        ],
                        "scheduler": {
                            "workflow": {
                                "phase2_started": True,
                                "phase1_baseline_labels": sorted(nodes),
                                "phase2_prerequisite_labels": [],
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            ctx = Ctx(
                name="simplex",
                blueprint_dir=root,
                runner_spec="codex",
                escalation_runner_spec="codex",
                base_effort="medium",
                escalation_effort="high",
                base_timeout=300,
                hard_timeout=600,
                lean_command=["lean"],
                telemetry=telemetry,
                paper_text="",
                library_context="",
                section_size=12,
                proof_batch=3,
                workers=3,
                use_ladder=False,
            )
            ctx.nodes = nodes
            ctx.stmt_fps = stmt_fps
            ctx.contract_fps = contract_fps

            with patch("formalize_blueprint._state_path", return_value=state), patch(
                "formalize_blueprint._generated_module_dir",
                return_value=generated,
            ), patch(
                "formalize_blueprint._lake_olean_path",
                side_effect=lambda path: path.with_suffix(".lake.olean"),
            ):
                loaded = _load_state(ctx, ["lean"])

            self.assertEqual(
                [section.number for section in loaded],
                fixture["expected"]["kept_sections"],
            )
            self.assertEqual(
                [section.number for section in loaded if section.deferred],
                fixture["expected"]["deferred_sections"],
            )
            self.assertFalse(duplicate_path.exists())
            self.assertEqual(
                [entry["number"] for entry in json.loads(state.read_text())["sections"]],
                fixture["expected"]["kept_sections"],
            )
            migrations = [
                fields
                for event, fields in telemetry.events
                if event == "resume_duplicate_section_discarded"
            ]
            self.assertEqual(len(migrations), 1)
            self.assertEqual(
                migrations[0]["duplicate_labels"], ["def:max-function"]
            )

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

    def test_serial_freeze_parts_salvages_delivered_declarations(self) -> None:
        ctx = SimpleNamespace(
            defer_phase1_alignment=False,
            nodes={"def:a": node("def:a"), "def:b": node("def:b")},
        )
        delivered = _parse_module(
            "def def_a : Nat := by sorry\n\n"
            "def def_b : Nat := by sorry\n"
        )
        retained = Section(
            number=1,
            labels=["def:a"],
            path=Path("Skeleton01.lean"),
            module="Generated.Skeleton01",
            import_modules=[],
        )
        with patch(
            "formalize_blueprint._planned_helper_owner_by_name",
            return_value={},
        ) as owners, patch(
            "formalize_blueprint._freeze_section_from_code",
            return_value=[retained],
        ) as freeze, patch("formalize_blueprint._save_ctx_state"):
            sections = _freeze_parts(
                ctx,
                [["def:a"]],
                [],
                _SectionNumberAllocator(1),
                delivered=delivered,
            )

        self.assertEqual(sections, [retained])
        owners.assert_called_once_with(ctx, ["def:a"])
        freeze.assert_called_once()

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

    def test_top_down_frontier_does_not_block_independent_lower_branch(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )
        nodes = {
            label: node(label, uses=set(dependencies))
            for label, dependencies in fixture["nodes"].items()
        }

        # The correctness-field consumer has already completed, so its three
        # dependencies can occupy idle workers while the independent root and
        # security branch continue in root-first order.
        self.assertEqual(
            _next_implementation_frontier(
                nodes,
                set(fixture["unresolved"]),
                "top-down",
            ),
            (
                0,
                fixture["expected_dynamic_ready"],
                ["thm:main-construction"],
            ),
        )

    def test_singleton_proof_rounds_do_not_inherit_configured_batch_capacity(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "uue_static_layer_barrier.json"
            ).read_text(encoding="utf-8")
        )["singleton_retry_regression"]

        self.assertEqual(fixture["observed_base_attempts"], 5)
        self.assertEqual(
            _proof_base_round_limit(
                fixture["configured_batch_size"],
                fixture["actual_label_count"],
            ),
            fixture["expected_base_attempts"],
        )
        # Genuine large units retain the original bisection allowance.
        self.assertEqual(_proof_base_round_limit(12, 12), 5)

    def test_singleton_section_escalates_after_two_base_calls(self) -> None:
        label = "lem:singleton"
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "Skeleton01.lean"
            path.write_text(
                "theorem lem_singleton : True := by\n  sorry\n",
                encoding="utf-8",
            )
            section = Section(1, [label], path, "Generated.Skeleton01", [])
            ctx = SimpleNamespace(
                nodes={label: node(label)},
                use_ladder=False,
                proof_batch=12,
                base_timeout=300,
                hard_timeout=600,
                base_effort="medium",
                escalation_effort="high",
                telemetry=FakeTelemetry(),
            )
            purposes: list[str] = []

            def call_model(*_args, **kwargs):
                purposes.append(kwargs["purpose"])
                return CallResult(status="ok", text="candidate")

            with patch(
                "formalize_blueprint._sections_for_deps", return_value=[]
            ), patch(
                "formalize_blueprint._proof_prompt", return_value="prompt"
            ), patch(
                "formalize_blueprint._call_model", side_effect=call_model
            ), patch(
                "formalize_blueprint._apply_proof_batch",
                return_value=([], {label: "Lean rejected candidate"}, {}),
            ), patch(
                "formalize_blueprint._parse_decomposition_refusal",
                side_effect=[
                    None,
                    None,
                    {
                        "label": label,
                        "reason": "missing helper",
                        "missing_helpers": ["helper lemma"],
                    },
                ],
            ), patch(
                "formalize_blueprint._retry_next_tier", return_value="base"
            ), patch(
                "formalize_blueprint._record_retry_failure", return_value=False
            ), patch(
                "formalize_blueprint._save_ctx_state"
            ):
                outcome = _prove_section(ctx, section, [section], [label])

        self.assertEqual(
            purposes,
            ["proof_batch", "proof_batch", "proof_singleton"],
        )
        self.assertEqual(outcome.decomposition[label], ["helper lemma"])

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
                "planner_tier": "escalation",
                "workers": "3",
                "section_size": "12",
                "timeout": "300",
                "hard_timeout": "600",
                "max_trials": "100",
                "continue_run": True,
                "proof_order": "top-down",
                "conjecture_policy": "record",
            },
        )

        self.assertNotIn("--proof-order", command)
        self.assertIn("--planner-tier", command)
        self.assertEqual(command[command.index("--planner-tier") + 1], "escalation")
        self.assertIn("--conjecture-policy", command)
        self.assertEqual(
            command[command.index("--conjecture-policy") + 1], "record"
        )

        default_command = build_webui_command(
            "refine",
            {
                "name": "simplex",
                "fast": True,
                "runner_backend": "codex",
                "runner_model": "gpt-5.5",
                "escalation_runner_backend": "codex",
                "escalation_runner_model": "gpt-5.5",
            },
        )
        self.assertEqual(
            default_command[default_command.index("--planner-tier") + 1],
            "escalation",
        )

    def test_webui_emits_each_refinement_starting_point_explicitly(self) -> None:
        base = {
            "name": "simplex",
            "fast": True,
            "runner_backend": "codex",
            "runner_model": "gpt-5.5",
        }
        for mode, flag in (
            ("latest", "--continue"),
            ("phase1", "--continue-phase1"),
            ("fresh", "--fresh"),
        ):
            with self.subTest(mode=mode):
                command = build_webui_command(
                    "refine", {**base, "resume_mode": mode}
                )
                self.assertIn(flag, command)
                self.assertEqual(
                    len(
                        set(command)
                        & {"--continue", "--continue-phase1", "--fresh"}
                    ),
                    1,
                )

        with self.assertRaisesRegex(ValueError, "fast pipeline"):
            build_webui_command(
                "refine", {**base, "fast": False, "resume_mode": "phase1"}
            )

    def test_webui_last_settings_exclude_target_and_resume_source(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "last-refine-settings.json"
            with patch("webui.LAST_REFINE_SETTINGS", path):
                _write_last_refine_settings(
                    {
                        "name": "wrong-paper",
                        "paper": "/tmp/temporary-upload.pdf",
                        "resume_mode": "fresh",
                        "runner_backend": "codex",
                        "runner_model": "gpt-5.5",
                        "workers": "3",
                        "fast": True,
                    }
                )
                saved = _read_last_refine_settings()

            self.assertEqual(
                saved,
                {
                    "runner_backend": "codex",
                    "runner_model": "gpt-5.5",
                    "workers": "3",
                    "fast": True,
                },
            )
            self.assertNotIn("name", saved)
            self.assertNotIn("paper", saved)
            self.assertNotIn("resume_mode", saved)

    def test_phase1_checkpoint_is_immutable_and_restores_coherent_state(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            scratch = root / ".auto-blueprint" / "formalization"
            draft = scratch / "paper" / "blueprint-draft"
            content = draft / "blueprint" / "src" / "content.tex"
            generated = root / "generated"
            lake_generated = root / "lake-generated"
            state = scratch / "paper" / "skeleton_state.json"
            content.parent.mkdir(parents=True)
            generated.mkdir(parents=True)
            lake_generated.mkdir(parents=True)
            state.parent.mkdir(parents=True, exist_ok=True)
            content.write_text("phase-one-blueprint\n", encoding="utf-8")
            (generated / "Skeleton01.lean").write_text(
                "theorem frozen : True := sorry\n", encoding="utf-8"
            )
            (lake_generated / "Skeleton01.olean").write_bytes(b"phase-one-object")
            state.write_text('{"phase": 1}\n', encoding="utf-8")
            telemetry = FakeTelemetry()
            ctx = SimpleNamespace(
                name="paper",
                blueprint_dir=draft,
                content_path=content,
                telemetry=telemetry,
            )

            with patch("formalize_blueprint.REPO_ROOT", root), patch(
                "formalize_blueprint.SCRATCH_DIR", scratch
            ), patch(
                "formalize_blueprint._generated_module_dir", return_value=generated
            ), patch(
                "formalize_blueprint._generated_lake_module_dir",
                return_value=lake_generated,
            ):
                self.assertTrue(_create_phase1_checkpoint(ctx))
                self.assertTrue(_phase1_checkpoint_available("paper"))

                content.write_text("phase-two-blueprint\n", encoding="utf-8")
                (generated / "Skeleton01.lean").write_text(
                    "theorem frozen : True := by trivial\n", encoding="utf-8"
                )
                (lake_generated / "Skeleton01.olean").write_bytes(b"phase-two-object")
                state.write_text('{"phase": 2}\n', encoding="utf-8")
                transaction = scratch / "paper" / "phase2-repair-transactions" / "r1"
                transaction.mkdir(parents=True)

                self.assertFalse(_create_phase1_checkpoint(ctx))
                _restore_phase1_checkpoint("paper")

            self.assertEqual(content.read_text(encoding="utf-8"), "phase-one-blueprint\n")
            self.assertIn(
                ":= sorry",
                (generated / "Skeleton01.lean").read_text(encoding="utf-8"),
            )
            self.assertEqual(
                (lake_generated / "Skeleton01.olean").read_bytes(),
                b"phase-one-object",
            )
            self.assertEqual(state.read_text(encoding="utf-8"), '{"phase": 1}\n')
            self.assertFalse(transaction.exists())
            self.assertEqual(telemetry.events[0][0], "phase1_checkpoint_created")

    def test_conjecture_policy_changes_phase1_contract_and_proof_obligation(self) -> None:
        conjecture = Node(
            label="conj:open",
            kind="conjecture",
            file=Path("content.tex"),
            line=1,
        )
        ctx = SimpleNamespace(
            nodes={"conj:open": conjecture},
            conjecture_policy="record",
        )
        target_kinds = _phase1_target_kinds(ctx, ["conj:open"])
        self.assertEqual(
            target_kinds,
            {"conj_open": OPEN_CONJECTURE_TARGET_KIND},
        )
        self.assertEqual(
            _skeleton_code_findings(
                "def conj_open : Prop := 1 = 1\n",
                target_kinds,
                {"conj_open": "conj:open"},
            ),
            [],
        )
        rejected = _skeleton_code_findings(
            "theorem conj_open : 1 = 1 := sorry\n",
            target_kinds,
            {"conj_open": "conj:open"},
        )
        self.assertTrue(rejected)

        ctx.conjecture_policy = "attempt"
        self.assertEqual(
            _phase1_target_kinds(ctx, ["conj:open"]),
            {"conj_open": "conjecture"},
        )

    def test_explicit_open_proposition_uses_configured_conjecture_policy(self) -> None:
        label = "remark:open-depth-questions"
        open_proposition = Node(
            label=label,
            kind="proposition",
            file=Path("content.tex"),
            line=1,
            open_claim=True,
        )
        ctx = SimpleNamespace(
            nodes={label: open_proposition},
            conjecture_policy="record",
        )

        self.assertEqual(
            _phase1_target_kinds(ctx, [label]),
            {"remark_open_depth_questions": OPEN_CONJECTURE_TARGET_KIND},
        )
        self.assertTrue(_records_conjecture(ctx, label))
        self.assertIn(
            "exact claim as a proposition-valued definition",
            _conjecture_policy_prompt(ctx, [label]),
        )
        self.assertEqual(
            _skeleton_deterministic_findings(
                "def remark_open_depth_questions : Prop := 1 = 1\n",
                ctx,
                [label],
            ),
            [],
        )

        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "Skeleton01.lean"
            path.write_text(
                "def remark_open_depth_questions : Prop := 1 = 1\n",
                encoding="utf-8",
            )
            section = Section(1, [label], path, "Generated.S1", [])
            self.assertEqual(
                _recorded_conjecture_labels(ctx, [section]), {label}
            )
            self.assertEqual(_verified_node_labels(ctx, [section]), set())
            self.assertEqual(_phase2_body_progress(ctx, [section]), (set(), set()))

        ctx.conjecture_policy = "attempt"
        self.assertEqual(
            _phase1_target_kinds(ctx, [label]),
            {"remark_open_depth_questions": "proposition"},
        )
        self.assertFalse(_records_conjecture(ctx, label))

    def test_recorded_conjecture_prompt_distinguishes_defining_from_proving(self) -> None:
        label = "conj:open"
        ctx = SimpleNamespace(
            nodes={
                label: Node(
                    label=label,
                    kind="conjecture",
                    file=Path("content.tex"),
                    line=1,
                )
            },
            conjecture_policy="record",
        )

        record_prompt = _conjecture_policy_prompt(ctx, [label])
        self.assertIn('"it remains open whether P"', record_prompt)
        self.assertIn("the recorded proposition\n  is P itself", record_prompt)
        self.assertIn("open is pipeline metadata", record_prompt)

        ctx.conjecture_policy = "attempt"
        attempt_prompt = _conjecture_policy_prompt(ctx, [label])
        self.assertNotIn("the recorded proposition", attempt_prompt)
        self.assertIn("Phase 2 may prove it", attempt_prompt)

    def test_recorded_conjecture_alignment_audit_explains_open_whether(self) -> None:
        label = "conj:max6-two-layers"
        ctx = SimpleNamespace(
            name="simplex",
            nodes={
                label: Node(
                    label=label,
                    kind="conjecture",
                    file=Path("content.tex"),
                    line=1,
                )
            },
            tex_blocks={
                label: "It remains open whether MAX_6 can be represented with "
                "two hidden layers."
            },
            paper_text="",
            conjecture_policy="record",
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
        code = (
            "def conj_max6_two_layers : Prop :=\n"
            "  exists width : Nat, width = 6\n"
        )

        with patch(
            "formalize_blueprint._call_model", return_value=response
        ) as call:
            self.assertIsNone(_model_alignment_audit(ctx, [label], code))

        audit_prompt = call.call_args.args[1]
        self.assertIn("the `def` must define P itself", audit_prompt)
        self.assertIn(
            "defining a proposition does not assert or prove it", audit_prompt
        )
        self.assertIn("must not be encoded inside the proposition", audit_prompt)

        ctx.conjecture_policy = "attempt"
        ctx.statement_audit_cache = set()
        with patch(
            "formalize_blueprint._call_model", return_value=response
        ) as call:
            self.assertIsNone(_model_alignment_audit(ctx, [label], code))
        self.assertNotIn(
            "the `def` must define P itself", call.call_args.args[1]
        )

    def test_recorded_conjecture_is_complete_but_not_verified_or_phase2_work(self) -> None:
        conjecture = Node(
            label="conj:open",
            kind="conjecture",
            file=Path("content.tex"),
            line=1,
        )
        with tempfile.TemporaryDirectory() as td:
            path = Path(td) / "Skeleton01.lean"
            path.write_text("def conj_open : Prop := 1 = 1\n", encoding="utf-8")
            section = Section(1, ["conj:open"], path, "Generated.S1", [])
            ctx = SimpleNamespace(
                nodes={"conj:open": conjecture},
                conjecture_policy="record",
            )
            self.assertEqual(
                _recorded_conjecture_labels(ctx, [section]), {"conj:open"}
            )
            self.assertEqual(_verified_node_labels(ctx, [section]), set())
            self.assertEqual(_phase2_body_progress(ctx, [section]), (set(), set()))

    def test_phase1_integration_reuses_matching_objects_and_checks_aggregate(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            path = root / "Skeleton01.lean"
            path.write_text("theorem statement : True := by trivial\n", encoding="utf-8")
            section = Section(
                1,
                ["lem:statement"],
                path,
                "Generated.S1",
                [],
                compile_fingerprint="clean",
            )
            ctx = SimpleNamespace(
                name="fixture",
                lean_command=["lean"],
                telemetry=FakeTelemetry(),
            )
            gate = root / "gate.lean"
            with patch(
                "formalize_blueprint._section_compile_fingerprint",
                return_value="clean",
            ), patch(
                "formalize_blueprint._section_objects_exist", return_value=True
            ), patch(
                "formalize_blueprint._compile_module_olean"
            ) as compile_mock, patch(
                "formalize_blueprint._phase1_integration_gate_path",
                return_value=gate,
            ), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ):
                self.assertEqual(
                    _phase1_recompile_environment(ctx, [section]), set()
                )
            compile_mock.assert_not_called()
            self.assertIn("import Generated.S1", gate.read_text(encoding="utf-8"))

    def test_phase1_integration_rebuilds_only_dirty_section(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            path = root / "Skeleton01.lean"
            path.write_text("theorem statement : True := by trivial\n", encoding="utf-8")
            section = Section(
                1,
                ["lem:statement"],
                path,
                "Generated.S1",
                [],
                compile_fingerprint="old",
            )
            ctx = SimpleNamespace(
                name="fixture",
                lean_command=["lean"],
                telemetry=FakeTelemetry(),
            )
            with patch(
                "formalize_blueprint._section_compile_fingerprint",
                return_value="new",
            ), patch(
                "formalize_blueprint._section_objects_exist", return_value=True
            ), patch(
                "formalize_blueprint._compile_module_olean",
                return_value=SimpleNamespace(ok=True, output=""),
            ) as compile_mock, patch(
                "formalize_blueprint._phase1_integration_gate_path",
                return_value=root / "gate.lean",
            ), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ):
                self.assertEqual(
                    _phase1_recompile_environment(ctx, [section]), set()
                )
            compile_mock.assert_called_once_with(path, ["lean"])
            self.assertEqual(section.compile_fingerprint, "new")

    def test_phase2_integration_ignores_section_with_no_accepted_labels(self) -> None:
        """An invalidated retry file is not an importable Lean module."""
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            accepted_path = root / "Skeleton01.lean"
            accepted_path.write_text(
                "theorem accepted : True := by trivial\n", encoding="utf-8"
            )
            invalid_path = root / "Skeleton02.lean"
            invalid_path.write_text(
                "import Generated.Missing\n"
                "theorem invalidated : True := by trivial\n",
                encoding="utf-8",
            )
            accepted = Section(
                1,
                ["lem:accepted"],
                accepted_path,
                "Generated.S1",
                [],
                refined_labels={"lem:accepted"},
                compile_fingerprint="clean",
            )
            invalidated = Section(
                2,
                ["lem:invalidated"],
                invalid_path,
                "Generated.S2",
                ["Generated.Missing"],
                refined_labels=set(),
                compile_fingerprint="",
            )
            ctx = SimpleNamespace(
                name="fixture",
                lean_command=["lean"],
                telemetry=FakeTelemetry(),
                phase2_started=True,
            )
            gate = root / "gate.lean"
            with patch(
                "formalize_blueprint._section_compile_fingerprint",
                return_value="clean",
            ), patch(
                "formalize_blueprint._section_objects_exist", return_value=True
            ), patch(
                "formalize_blueprint._compile_module_olean"
            ) as compile_mock, patch(
                "formalize_blueprint._phase1_integration_gate_path",
                return_value=gate,
            ), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ):
                self.assertEqual(
                    _phase1_recompile_environment(ctx, [accepted, invalidated]),
                    set(),
                )
            compile_mock.assert_not_called()
            gate_text = gate.read_text(encoding="utf-8")
            self.assertIn("import Generated.S1", gate_text)
            self.assertNotIn("Generated.S2", gate_text)
            event = next(
                fields
                for name, fields in ctx.telemetry.events
                if name == "phase1_integration_gate"
            )
            self.assertEqual(event["checked_modules"], 1)

    def test_historical_phase1_integration_reuses_all_frozen_modules(self) -> None:
        fixture_path = (
            REPO_ROOT
            / "tests"
            / "fixtures"
            / "phase1_orchestration_replay"
            / "integration_gate_reuse.json"
        )
        fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
        self.assertEqual(
            fixture["phase2_start_s"] - fixture["phase1_last_contract_s"],
            fixture["observed_integration_gap_s"],
        )
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            sections: list[Section] = []
            for number in range(1, fixture["module_count"] + 1):
                path = root / f"Skeleton{number:02d}.lean"
                path.write_text(
                    f"theorem statement_{number} : True := by trivial\n",
                    encoding="utf-8",
                )
                sections.append(
                    Section(
                        number,
                        [f"lem:statement-{number}"],
                        path,
                        f"Generated.S{number}",
                        [],
                        compile_fingerprint=f"clean-{number}",
                    )
                )
            telemetry = FakeTelemetry()
            ctx = SimpleNamespace(
                name="historical-integration-fixture",
                lean_command=["lean"],
                telemetry=telemetry,
            )
            fingerprint_by_path = {
                section.path: section.compile_fingerprint for section in sections
            }
            with patch(
                "formalize_blueprint._section_compile_fingerprint",
                side_effect=lambda section, *_args: fingerprint_by_path[section.path],
            ), patch(
                "formalize_blueprint._section_objects_exist", return_value=True
            ), patch(
                "formalize_blueprint._compile_module_olean"
            ) as compile_mock, patch(
                "formalize_blueprint._phase1_integration_gate_path",
                return_value=root / "gate.lean",
            ), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ) as aggregate_mock:
                self.assertEqual(
                    _phase1_recompile_environment(ctx, sections), set()
                )
            compile_mock.assert_not_called()
            self.assertEqual(
                aggregate_mock.call_count, fixture["expected_aggregate_checks"]
            )
            event = next(
                fields
                for name, fields in telemetry.events
                if name == "phase1_integration_gate"
            )
            self.assertEqual(
                event["reused_modules"], fixture["expected_reused_modules"]
            )
            self.assertEqual(
                event["rebuilt_modules"], fixture["expected_rebuilt_modules"]
            )

    def test_historical_phase2_theorem_updates_do_not_rebuild_import_closure(self) -> None:
        fixture_path = (
            REPO_ROOT
            / "tests"
            / "fixtures"
            / "phase2_orchestration_replay"
            / "opaque_theorem_object_reuse.json"
        )
        fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
        with tempfile.TemporaryDirectory() as td, patch(
            "formalize_blueprint._lean_environment_fingerprint",
            return_value="historical-environment",
        ):
            root = Path(td)
            sections: list[Section] = []
            changed = fixture["theorem_body_changes"]
            for number in range(1, fixture["module_count"] + 1):
                path = root / f"Skeleton{number:02d}.lean"
                path.write_text(
                    f"theorem statement_{number} : True := sorry\n",
                    encoding="utf-8",
                )
                imports = ["Generated.S1"] if number == changed + 1 else []
                sections.append(
                    Section(
                        number,
                        [f"lem:statement-{number}"],
                        path,
                        f"Generated.S{number}",
                        imports,
                    )
                )

            for section in sections:
                section.compile_fingerprint = _section_compile_fingerprint(
                    section, ["lean"], sections
                )
            before = {
                section.module: section.compile_fingerprint for section in sections
            }
            legacy_before: dict[str, str] = {}
            for section in sections:
                digest = hashlib.sha256(section.path.read_bytes())
                for module in section.import_modules:
                    digest.update(module.encode("utf-8"))
                    digest.update(legacy_before[module].encode("ascii"))
                legacy_before[section.module] = digest.hexdigest()

            for section in sections[:changed]:
                section.path.write_text(
                    f"theorem statement_{section.number} : True := by trivial\n",
                    encoding="utf-8",
                )

            invalidated = 0
            legacy_after: dict[str, str] = {}
            for section in sections:
                expected = _section_compile_fingerprint(section, ["lean"], sections)
                if expected != before[section.module]:
                    invalidated += 1
                section.compile_fingerprint = expected
                digest = hashlib.sha256(section.path.read_bytes())
                for module in section.import_modules:
                    digest.update(module.encode("utf-8"))
                    digest.update(legacy_after[module].encode("ascii"))
                legacy_after[section.module] = digest.hexdigest()

        self.assertEqual(
            sum(
                legacy_after[module] != legacy_before[module]
                for module in legacy_before
            ),
            fixture["observed_legacy_rebuilt_modules"],
        )
        self.assertEqual(
            invalidated, fixture["expected_object_semantic_rebuilt_modules"]
        )

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
            hard_timeout=120,
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
        # Both lanes are submitted, but an admissible first result may cancel
        # the sibling before its provider call starts.
        self.assertIn(call_model.call_count, {1, 2})
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

    def test_design_plan_prompt_uses_authoritative_scoped_dependency_table(self) -> None:
        statement_dep = "def:statement-input"
        proof_dep = "lem:proof-tool"
        target = "lem:result"
        nodes = {
            statement_dep: node(statement_dep),
            proof_dep: node(proof_dep),
            target: Node(
                label=target,
                kind="lemma",
                file=Path("content.tex"),
                line=1,
                uses={statement_dep, proof_dep},
                statement_uses={statement_dep},
                proof_uses={proof_dep},
            ),
        }
        ctx = SimpleNamespace(
            name="paper",
            nodes=nodes,
            stmt_blocks={
                statement_dep: "Define the input.",
                proof_dep: "Prove the proof tool.",
                target: "The result follows.",
            },
            unavailable_imports=set(),
            library_candidates=[],
            library_context="",
        )

        prompt = _design_plan_prompt(
            ctx,
            [target],
            [],
            [],
            timeout_s=120,
            root_context_labels=[target],
        )

        self.assertIn(
            f"{target} -> {statement_dep} (statement interface)", prompt
        )
        self.assertIn(f"{target} -> {proof_dep} (proof only)", prompt)
        self.assertIn("sole authoritative\nallowed-symbol table", prompt)
        self.assertIn(
            "A `proof only` entry may guide the later\n"
            "Phase-2 implementation, but it MUST NOT appear in `target_signature`",
            prompt,
        )
        self.assertIn(
            "Root context\nmay shape the meaning and strength of an interface, "
            "but it cannot add a\ndependency edge absent from the blueprint graph.",
            prompt,
        )

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

    def test_tournament_admits_first_complete_initial_frontier(self) -> None:
        label = "def:leaf"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "def:leaf-v1"},
            design_plan="",
            design_plan_entries={},
            telemetry=FakeTelemetry(),
            base_timeout=30,
            hard_timeout=60,
        )
        release_sibling = threading.Event()

        accepted = DesignPlanCandidate(
            candidate_id="A",
            entries={label: {"target_signature": "def def_leaf : Nat"}},
            missing=[],
            findings={},
            blocked=set(),
            components=[],
        )

        def generate(*args, **kwargs):
            candidate_id = args[5]
            if candidate_id == "A":
                return accepted
            self.assertEqual(candidate_id, "B")
            release_sibling.wait(1.0)
            return DesignPlanCandidate(
                candidate_id="B",
                entries={},
                missing=[label],
                findings={label: ["missing contract"]},
                blocked={label},
                components=[[label]],
            )

        try:
            with patch(
                "formalize_blueprint._generate_design_plan_candidate",
                side_effect=generate,
            ):
                started = time.monotonic()
                selected, _alternate = _initial_design_plan_tournament(
                    ctx, [label], [], [], [label]
                )
                elapsed = time.monotonic() - started
        finally:
            release_sibling.set()

        self.assertEqual(selected.candidate_id, "A")
        self.assertLess(elapsed, 0.5)

    def test_tournament_rejects_catastrophic_plan_and_requests_full_restart(self) -> None:
        provider = "def:left"
        consumer = "def:right"
        labels = [consumer, provider]
        ctx = SimpleNamespace(
            nodes={
                provider: node(provider),
                consumer: node(consumer, uses={provider}),
            },
            stmt_fps={label: f"{label}-v1" for label in labels},
            design_plan="",
            design_plan_entries={},
            generation_feedback={},
            telemetry=FakeTelemetry(),
            base_timeout=30,
            hard_timeout=60,
        )

        def rejected(candidate_id: str) -> DesignPlanCandidate:
            entries = {
                provider: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": f"{provider}-v1",
                    "target_signature": "structure def_left where\n  existing : Nat",
                    "helpers": [],
                    "decisions": [],
                },
                consumer: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": f"{consumer}-v1",
                    "target_signature": "def def_right : def_left.Missing",
                    "helpers": [],
                    "decisions": [],
                },
            }
            return _evaluate_design_plan_candidate(
                ctx, labels, entries, candidate_id
            )

        with patch(
            "formalize_blueprint._generate_design_plan_candidate",
            side_effect=[rejected("A"), rejected("B")],
        ):
            with self.assertRaises(RepairRequest) as raised:
                _initial_design_plan_tournament(ctx, labels, [], [], labels)

        self.assertFalse(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(set(raised.exception.labels), set(labels))
        self.assertIn("restart the full-context planning tournament", raised.exception.evidence)

    def test_initial_plan_admission_requires_complete_ready_frontier(self) -> None:
        leaves = ["def:left", "def:right"]
        root = "lem:root"
        ctx = SimpleNamespace(
            nodes={
                leaves[0]: node(leaves[0]),
                leaves[1]: node(leaves[1]),
                root: node(root, uses=set(leaves)),
            }
        )
        entries = {
            label: {"target_signature": f"def {_lean_name(label)} : Nat"}
            for label in leaves
        }
        entries[root] = {"target_signature": f"theorem {_lean_name(root)} : True"}
        candidate = DesignPlanCandidate(
            candidate_id="historical-bad-plan",
            entries=entries,
            missing=[],
            findings={leaves[0]: ["invalid leaf interface"]},
            blocked={leaves[0]},
            components=[[leaves[0]]],
        )

        admitted, frontier, blocked = _initial_plan_admission(
            ctx, [root, *leaves], candidate
        )

        self.assertFalse(admitted)
        self.assertEqual(set(frontier), set(leaves))
        self.assertEqual(blocked, [leaves[0]])

    def test_initial_plan_admits_cheaper_scoped_repair_after_both_lanes(self) -> None:
        frontier = [
            "def:security-parameter-negligible",
            "def:finite-register-operators",
            "def:single-qubit-paulis-cliffords",
        ]
        future = [f"lem:future-{index}" for index in range(49)]
        ordered = [*frontier, *future]
        ctx = SimpleNamespace(
            nodes={
                **{label: node(label) for label in frontier},
                **{
                    label: node(label, uses={frontier[index % len(frontier)]})
                    for index, label in enumerate(future)
                },
            }
        )
        entries = {
            label: {"target_signature": f"theorem {_lean_name(label)} : True"}
            for label in ordered
        }
        blocked = {
            "def:finite-register-operators",
            future[0],
            future[1],
            future[2],
        }
        candidate = DesignPlanCandidate(
            candidate_id="historical-tournament-2-b",
            entries=entries,
            missing=[],
            findings={label: [f"closure finding for {label}"] for label in blocked},
            blocked=blocked,
            components=[[label] for label in blocked],
        )

        admitted, ready, blocked_ready, repair_work, tournament_work = (
            _initial_plan_repair_admission(ctx, ordered, candidate)
        )

        self.assertTrue(admitted)
        self.assertEqual(set(ready), set(frontier))
        self.assertEqual(blocked_ready, ["def:finite-register-operators"])
        self.assertEqual((repair_work, tournament_work), (16, 104))

    def test_initial_plan_repair_cost_rejects_catastrophic_candidate(self) -> None:
        labels = [f"def:node-{index}" for index in range(52)]
        candidate = DesignPlanCandidate(
            candidate_id="historical-catastrophic",
            entries={label: {} for label in labels},
            missing=[],
            findings={
                label: [f"finding {index}" for index in range(2)]
                for label in labels
            },
            blocked=set(labels),
            components=[labels[:18], labels[18:35], labels[35:]],
        )

        repair_work, tournament_work = _initial_plan_repair_costs(
            candidate, len(labels)
        )

        self.assertGreater(repair_work, tournament_work)

    def test_tournament_selects_repairable_plan_instead_of_restarting(self) -> None:
        leaves = ["def:left", "def:right"]
        future = ["lem:left-result", "lem:right-result"]
        ordered = [*leaves, *future]
        ctx = SimpleNamespace(
            nodes={
                leaves[0]: node(leaves[0]),
                leaves[1]: node(leaves[1]),
                future[0]: node(future[0], uses={leaves[0]}),
                future[1]: node(future[1], uses={leaves[1]}),
            },
            stmt_fps={label: f"{label}-v1" for label in ordered},
            design_plan="",
            design_plan_entries={},
            generation_feedback={},
            telemetry=FakeTelemetry(),
            base_timeout=30,
            hard_timeout=60,
        )
        entries = {
            label: {"target_signature": f"theorem {_lean_name(label)} : True"}
            for label in ordered
        }
        repairable = DesignPlanCandidate(
            candidate_id="B",
            entries=entries,
            missing=[],
            findings={leaves[0]: ["one isolated closure defect"]},
            blocked={leaves[0]},
            components=[[leaves[0]]],
        )
        catastrophic = DesignPlanCandidate(
            candidate_id="A",
            entries=entries,
            missing=[],
            findings={label: ["bad", "worse"] for label in ordered},
            blocked=set(ordered),
            components=[ordered],
        )

        def generate(*args, **kwargs):
            return catastrophic if args[5] == "A" else repairable

        with patch(
            "formalize_blueprint._generate_design_plan_candidate",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._merge_design_plan_candidates",
            return_value=(repairable, []),
        ):
            selected, _alternate = _initial_design_plan_tournament(
                ctx, ordered, [], [], ordered
            )

        self.assertEqual(selected.candidate_id, "B")
        tournament_events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_design_plan_tournament"
        ]
        self.assertEqual(
            tournament_events[-1]["selection_mode"], "cheaper_scoped_repair"
        )

    def test_tournament_uses_repair_cost_not_lexicographic_plan_score(self) -> None:
        leaves = ["def:left", "def:right"]
        future = ["lem:left-result", "lem:right-result"]
        ordered = [*leaves, *future]
        ctx = SimpleNamespace(
            nodes={
                leaves[0]: node(leaves[0]),
                leaves[1]: node(leaves[1]),
                future[0]: node(future[0], uses={leaves[0]}),
                future[1]: node(future[1], uses={leaves[1]}),
            },
            stmt_fps={label: f"{label}-v1" for label in ordered},
            design_plan="",
            design_plan_entries={},
            generation_feedback={},
            telemetry=FakeTelemetry(),
            base_timeout=30,
            hard_timeout=60,
        )
        entries = {
            label: {"target_signature": f"theorem {_lean_name(label)} : True"}
            for label in ordered
        }
        lexicographic_winner = DesignPlanCandidate(
            candidate_id="A",
            entries=entries,
            missing=[],
            findings={leaves[0]: [f"finding-{index}" for index in range(6)]},
            blocked={leaves[0]},
            components=[[leaves[0]]],
        )
        cheaper_repair = DesignPlanCandidate(
            candidate_id="B",
            entries=entries,
            missing=[],
            findings={leaves[0]: ["one finding"]},
            blocked=set(leaves),
            components=[leaves],
        )
        self.assertLess(lexicographic_winner.score, cheaper_repair.score)
        self.assertGreater(
            _initial_plan_repair_costs(lexicographic_winner, len(ordered))[0],
            _initial_plan_repair_costs(cheaper_repair, len(ordered))[0],
        )

        def generate(*args, **kwargs):
            return lexicographic_winner if args[5] == "A" else cheaper_repair

        with patch(
            "formalize_blueprint._generate_design_plan_candidate",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._merge_design_plan_candidates",
            return_value=(lexicographic_winner, []),
        ):
            selected, _alternate = _initial_design_plan_tournament(
                ctx, ordered, [], [], ordered
            )

        self.assertEqual(selected.candidate_id, "B")

    def test_design_plan_merge_cannot_reduce_ready_frontier(self) -> None:
        leaf = "def:leaf"
        later = "lem:later"
        ctx = SimpleNamespace(
            nodes={leaf: node(leaf), later: node(later, uses={leaf})}
        )
        primary = DesignPlanCandidate(
            candidate_id="B",
            entries={leaf: {"target_signature": "def def_leaf : Nat"}, later: {}},
            missing=[],
            findings={later: ["first defect", "second defect"]},
            blocked={later},
            components=[[later]],
        )
        alternate = DesignPlanCandidate(
            candidate_id="A",
            entries={leaf: {"target_signature": "def def_leaf : Nat"}, later: {}},
            missing=[],
            findings={},
            blocked=set(),
            components=[],
        )
        globally_better_but_frontier_blocking = DesignPlanCandidate(
            candidate_id="merge:B+A",
            entries=copy.deepcopy(primary.entries),
            missing=[],
            findings={leaf: ["replacement blocks the ready leaf"]},
            blocked={leaf},
            components=[[leaf]],
        )

        with patch(
            "formalize_blueprint._evaluate_design_plan_candidate",
            return_value=globally_better_but_frontier_blocking,
        ):
            merged, components = _merge_design_plan_candidates(
                ctx, [leaf, later], primary, alternate
            )

        self.assertIs(merged, primary)
        self.assertEqual(components, [])

    def test_rejected_closed_contract_tries_retained_alternate_without_model(self) -> None:
        label = "def:leaf"
        selected = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": "def:leaf-v1",
            "target_signature": "def def_leaf : Nat",
            "helpers": [],
            "decisions": ["selected"],
            "semantic_revision_count": 1,
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
        self.assertEqual(
            ctx.design_plan_entries[label]["semantic_revision_count"], 1
        )
        self.assertNotIn(label, ctx.design_plan_alternates)

    def test_model_plan_correction_preserves_semantic_revision_count(self) -> None:
        label = "def:leaf"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "def:leaf-v1"},
            tex_blocks={label: r"\begin{definition}\label{def:leaf}Leaf\end{definition}"},
            design_plan="",
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "def:leaf-v1",
                    "target_signature": "def def_leaf : Nat",
                    "helpers": [],
                    "decisions": ["old strategy"],
                    "semantic_revision_count": 1,
                }
            },
            design_plan_alternates={},
            telemetry=FakeTelemetry(),
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
        )
        corrected = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "contracts": [
                        {
                            "label": label,
                            "target_signature": "def def_leaf : Int",
                            "helpers": [],
                            "decisions": ["new strategy"],
                        }
                    ]
                }
            ),
        )

        with patch("formalize_blueprint._call_model", return_value=corrected):
            changed = _correct_phase1_design_plan(
                ctx,
                [label],
                "the previous strategy was semantically rejected",
                escalated=True,
                try_alternate=False,
            )

        self.assertTrue(changed)
        self.assertIn("Int", ctx.design_plan_entries[label]["target_signature"])
        self.assertEqual(
            ctx.design_plan_entries[label]["semantic_revision_count"], 1
        )

    def test_isolated_plan_correction_does_not_transition_live_scheduler(self) -> None:
        label = "def:leaf"
        candidate = {"component_labels": [label], "code": "old candidate"}
        retry = {
            "label": label,
            "stage": "phase1_statement",
            "state": "escalation",
        }
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "def:leaf-v1"},
            tex_blocks={label: r"\begin{definition}\label{def:leaf}Leaf\end{definition}"},
            design_plan="",
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "def:leaf-v1",
                    "target_signature": "def def_leaf : Nat",
                    "helpers": [],
                    "decisions": ["old strategy"],
                }
            },
            design_plan_alternates={},
            generation_candidates={label: candidate},
            retry_lifecycle={f"phase1_statement:{label}": retry},
            telemetry=FakeTelemetry(),
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
        )
        response = CallResult(
            status="ok",
            text=json.dumps(
                {
                    "contracts": [
                        {
                            "label": label,
                            "target_signature": "def def_leaf : Int",
                            "helpers": [],
                            "decisions": ["isolated proposal"],
                        }
                    ]
                }
            ),
        )

        with patch("formalize_blueprint._call_model", return_value=response):
            changed = _correct_phase1_design_plan(
                ctx,
                [label],
                "closure evidence",
                try_alternate=False,
                transition_generation_epoch=False,
            )

        self.assertTrue(changed)
        self.assertIs(ctx.generation_candidates[label], candidate)
        self.assertIs(ctx.retry_lifecycle[f"phase1_statement:{label}"], retry)

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

    def test_invalid_initial_plan_restarts_before_statement_generation(self) -> None:
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
            return_value=True,
        ) as correction:
            with self.assertRaises(RepairRequest) as raised:
                _ensure_phase1_design_plan(ctx, set(nodes), [])

        correction.assert_not_called()
        self.assertFalse(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(ctx.design_plan_entries, {})

    def test_unclosed_initial_plan_is_discarded_without_correction(self) -> None:
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

        correction.assert_not_called()
        self.assertNotIn(provider, ctx.design_plan_entries)
        self.assertNotIn(consumer, ctx.design_plan_entries)
        rejections = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_design_plan_tournament"
            and fields.get("status") == "rejected_no_admissible_plan"
        ]
        self.assertEqual(len(rejections), 1)
        self.assertEqual(rejections[0]["selected_candidate"], "")

    def test_closure_correction_preserves_partial_progress_without_retry(self) -> None:
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
            design_plan_entries={
                provider: {
                    "target_signature": (
                        "structure def_network where\n  realizes : Prop"
                    ),
                    "helpers": [],
                },
                consumer: {
                    "target_signature": (
                        "theorem lem_representable : "
                        "def_network.First ∧ def_network.Second"
                    ),
                    "helpers": [],
                },
            },
            design_plan_alternates={},
            paper_text="",
            telemetry=FakeTelemetry(),
            workers=1,
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
        )
        findings = _validate_design_plan_contract_closure(ctx, list(nodes))
        observed_evidence: list[str] = []

        def correct(isolated, labels, evidence, **_kwargs):
            observed_evidence.append(evidence)
            self.assertEqual(set(labels), {provider, consumer})
            isolated.design_plan_entries[provider]["target_signature"] = (
                "structure def_network where\n"
                "  realizes : Prop\n"
                "  First : Prop"
            )
            return True

        with patch(
            "formalize_blueprint._correct_phase1_design_plan",
            side_effect=correct,
        ) as correction:
            with self.assertRaises(RepairRequest):
                _repair_phase1_design_plan_closure(ctx, list(nodes), findings)

        self.assertEqual(correction.call_count, 1)
        self.assertNotIn(provider, ctx.design_plan_entries)
        self.assertNotIn(consumer, ctx.design_plan_entries)
        self.assertIn(
            "First",
            ctx.design_plan_alternates[provider]["target_signature"],
        )
        self.assertNotIn(
            "Second",
            ctx.design_plan_alternates[provider]["target_signature"],
        )
        attempts = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_design_plan_closure_attempt"
        ]
        self.assertEqual([item["improved"] for item in attempts], [True])

    def test_disjoint_plan_closure_components_correct_concurrently(self) -> None:
        providers = ["def:a", "def:b"]
        consumers = ["lem:a", "lem:b"]
        nodes = {
            providers[0]: node(providers[0]),
            providers[1]: node(providers[1]),
            consumers[0]: node(consumers[0], uses={providers[0]}),
            consumers[1]: node(consumers[1], uses={providers[1]}),
        }
        entries = {
            providers[0]: {
                "target_signature": "structure def_a where\n  value : Nat",
                "helpers": [],
            },
            providers[1]: {
                "target_signature": "structure def_b where\n  value : Nat",
                "helpers": [],
            },
            consumers[0]: {
                "target_signature": "theorem lem_a : def_a.required = 0",
                "helpers": [],
            },
            consumers[1]: {
                "target_signature": "theorem lem_b : def_b.required = 0",
                "helpers": [],
            },
        }
        ctx = SimpleNamespace(
            name="test",
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan="",
            design_plan_entries=copy.deepcopy(entries),
            design_plan_alternates={},
            paper_text="",
            telemetry=FakeTelemetry(),
            workers=2,
        )
        findings = _validate_design_plan_contract_closure(ctx, list(nodes))
        active = 0
        peak = 0
        lock = threading.Lock()

        def correct(isolated, labels, _evidence, **kwargs):
            nonlocal active, peak
            self.assertEqual(len(set(labels) & set(providers)), 1)
            self.assertEqual(len(set(labels) & set(consumers)), 1)
            with lock:
                active += 1
                peak = max(peak, active)
            time.sleep(0.03)
            for consumer, provider in zip(consumers, providers):
                if consumer in labels:
                    isolated.design_plan_entries[provider]["target_signature"] = (
                        f"structure {_lean_name(provider)} where\n"
                        "  value : Nat\n"
                        "  required : Nat"
                    )
            with lock:
                active -= 1
            return True

        with patch(
            "formalize_blueprint._correct_phase1_design_plan",
            side_effect=correct,
        ):
            _repair_phase1_design_plan_closure(
                ctx, list(nodes), findings
            )

        self.assertEqual(peak, 2)
        self.assertIn("required", ctx.design_plan_entries[providers[0]]["target_signature"])
        self.assertIn("required", ctx.design_plan_entries[providers[1]]["target_signature"])
        waves = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_design_plan_closure_wave"
        ]
        self.assertEqual(waves[-1]["worker_count"], 2)
        self.assertEqual(waves[-1]["component_count"], 2)

    def test_failed_closure_component_does_not_discard_successful_sibling(self) -> None:
        good_provider, bad_provider = "def:good", "def:bad"
        good_consumer, bad_consumer = "lem:good", "lem:bad"
        nodes = {
            good_provider: node(good_provider),
            bad_provider: node(bad_provider),
            good_consumer: node(good_consumer, uses={good_provider}),
            bad_consumer: node(bad_consumer, uses={bad_provider}),
        }
        ctx = SimpleNamespace(
            name="test",
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan="",
            design_plan_entries={
                good_provider: {
                    "target_signature": "structure def_good where\n  value : Nat",
                    "helpers": [],
                },
                bad_provider: {
                    "target_signature": "structure def_bad where\n  value : Nat",
                    "helpers": [],
                },
                good_consumer: {
                    "target_signature": "theorem lem_good : def_good.required = 0",
                    "helpers": [],
                },
                bad_consumer: {
                    "target_signature": "theorem lem_bad : def_bad.required = 0",
                    "helpers": [],
                },
            },
            design_plan_alternates={},
            paper_text="",
            telemetry=FakeTelemetry(),
            workers=2,
        )
        findings = _validate_design_plan_contract_closure(ctx, list(nodes))

        def correct(isolated, labels, _evidence, **_kwargs):
            if good_consumer not in labels:
                return False
            isolated.design_plan_entries[good_provider]["target_signature"] = (
                "structure def_good where\n  value : Nat\n  required : Nat"
            )
            return True

        with patch(
            "formalize_blueprint._correct_phase1_design_plan",
            side_effect=correct,
        ):
            with self.assertRaises(RepairRequest):
                _repair_phase1_design_plan_closure(
                    ctx, list(nodes), findings
                )

        self.assertIn(good_provider, ctx.design_plan_entries)
        self.assertIn(good_consumer, ctx.design_plan_entries)
        self.assertIn("required", ctx.design_plan_entries[good_provider]["target_signature"])
        # A true missing-member failure invalidates the provider and consumer
        # together because either public surface may own the mismatch.
        self.assertNotIn(bad_provider, ctx.design_plan_entries)
        self.assertNotIn(bad_consumer, ctx.design_plan_entries)

    def test_deferred_closure_cannot_admit_invalid_initial_plan(self) -> None:
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
            with self.assertRaises(RepairRequest) as raised:
                _ensure_phase1_design_plan(
                    ctx,
                    set(nodes),
                    [],
                    defer_closure_repair=True,
                )

        correction.assert_not_called()
        self.assertFalse(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(ctx.design_plan_entries, {})

    def test_bottom_up_phase1_does_not_block_provider_for_future_consumer(self) -> None:
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

        self.assertEqual(events[0], ("generate", {provider, unrelated}))
        self.assertEqual(events[1], ("generate", {consumer}))
        self.assertFalse(any(kind == "repair" for kind, _labels in events))
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

    def test_design_plan_uses_semantic_fallback_per_untyped_helper(self) -> None:
        # Historical Simplex state from run-20260821-001641: a blueprint repair
        # introduced this helper after neighboring candidates had already
        # established typed contracts.
        provider = "def:relu-network"
        helper = "lem:geometric-recursion-edge-realization-preservation"
        ctx = SimpleNamespace(
            nodes={
                provider: node(provider),
                helper: node(helper, uses={provider}),
            },
            stmt_fps={provider: "provider-v1", helper: "helper-v1"},
            design_plan_entries={
                provider: {
                    "target_signature": "structure def_relu_network where\n  hidden_layer_depth : Nat",
                    "helpers": [],
                    "decisions": ["typed provider contract"],
                },
            },
            semantic_plan_entries={
                provider: {
                    "representation": "stale semantic provider guidance",
                    "vocabulary": [],
                    "obligations": [],
                    "provider_requirements": [],
                },
                helper: {
                    "representation": "compose the compression layer with the later-state realization",
                    "vocabulary": [],
                    "obligations": [
                        "For all a,b>=0 and ambient input dimension N.",
                        "The explicit one-hidden-layer ReLU block followed by the later realization computes exactly T_{a,b+4}.",
                    ],
                    "provider_requirements": [
                        {"provider": provider, "capabilities": ["network realization and composition"]}
                    ],
                },
            },
            blueprint_direct_generation={},
        )

        block = _design_plan_block(ctx, [helper])

        self.assertIn("structure def_relu_network", block)
        self.assertIn("compose the compression layer", block)
        self.assertIn("ambient input dimension N", block)
        self.assertIn("computes exactly T_{a,b+4}", block)
        self.assertNotIn("stale semantic provider guidance", block)

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
            ctx,
            [label],
            "opaque interface rejected",
            escalated=True,
            transition_generation_epoch=False,
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
        epoch_transitions = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_generation_epoch_transition"
        ]
        self.assertEqual(len(epoch_transitions), 1)
        self.assertEqual(epoch_transitions[0]["labels"], [label])

    def test_plan_replacement_preserves_candidate_contract_origin(self) -> None:
        replacement = _preserve_plan_entry_progress(
            {
                "origin": "phase1_candidate",
                "semantic_revision_count": 1,
            },
            {
                "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                "target_signature": "def def_test : Prop",
            },
        )

        self.assertEqual(replacement["origin"], "phase1_candidate")
        self.assertEqual(replacement["semantic_revision_count"], 1)

    def test_candidate_owned_semantic_exhaustion_skips_legacy_plan_loop(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "uue_candidate_owned_semantic_exhaustion.json"
            ).read_text(encoding="utf-8")
        )
        labels = fixture["labels"]
        ctx = SimpleNamespace(
            name=fixture["blueprint"],
            nodes={label: node(label) for label in labels},
            stmt_fps=fixture["statement_fingerprints"],
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": fixture["statement_fingerprints"][label],
                    "target_signature": f"def {_lean_name(label)} : Prop",
                    "origin": "phase1_candidate",
                    "semantic_revision_count": 0,
                }
                for label in labels
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            telemetry=FakeTelemetry(),
        )
        evidence = fixture["semantic_rejection"]

        with patch(
            "formalize_blueprint._correct_phase1_design_plan"
        ) as legacy_correction:
            self.assertTrue(
                all(
                    _semantic_exhaustion_policy(ctx, label)
                    == fixture["expected_first_exhaustion"]
                    for label in labels
                )
            )
            decomposition, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    labels,
                    evidence,
                    layer_no=0,
                    source="historical-replay",
                )
            )
            self.assertEqual(decomposition, set())
            self.assertEqual(revised, set(labels))
            self.assertEqual(unresolved, set())
            self.assertTrue(
                all(
                    _semantic_exhaustion_policy(ctx, label)
                    == fixture["expected_second_exhaustion"]
                    for label in labels
                )
            )

            decomposition, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    labels,
                    evidence,
                    layer_no=0,
                    source="historical-replay",
                )
            )
            self.assertEqual(decomposition, set(labels))
            self.assertEqual(revised, set())
            self.assertEqual(unresolved, set())
            legacy_correction.assert_not_called()

        activation_events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_blueprint_direct_generation_activated"
        ]
        self.assertEqual(activation_events[-1]["source"], "candidate_semantic_exhaustion")

    def test_candidate_owned_decomposition_does_not_revise_legacy_plan(
        self,
    ) -> None:
        label = "def:local-basis-unitary"
        ctx = SimpleNamespace(
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "origin": "phase1_candidate",
                    "semantic_revision_count": 0,
                }
            },
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._revise_exhausted_phase1_contracts"
        ) as revise:
            revised = _revise_decomposition_plans_once(
                ctx,
                [label],
                "the blueprint needs an explicit tensor-product helper",
                layer_no=0,
                source="historical-replay",
            )

        self.assertEqual(revised, set())
        revise.assert_not_called()

    def test_blueprint_direct_exhaustion_routes_only_that_node_to_decomposition(
        self,
    ) -> None:
        repeated = "def:repeated"
        first_exhaustion = "lem:first-exhaustion"
        ctx = SimpleNamespace(
            nodes={
                repeated: node(repeated),
                first_exhaustion: node(first_exhaustion),
            },
            design_plan_entries={
                repeated: {"semantic_revision_count": 1},
                first_exhaustion: {"semantic_revision_count": 0},
            },
            stmt_fps={repeated: "repeated-v1", first_exhaustion: "first-v1"},
            blueprint_direct_generation={
                repeated: {
                    "statement_fp": "repeated-v1",
                    "source": "test",
                    "evidence": "blueprint-direct generation also failed",
                }
            },
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

    def test_compile_failures_share_bounded_semantic_retry_lifecycle(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "uue_repeated_compile_failure_lifecycle.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        ctx = SimpleNamespace(
            name=fixture["blueprint"],
            nodes={label: node(label)},
            stmt_fps={label: fixture["statement_fp"]},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": fixture["statement_fp"],
                    "target_signature": f"theorem {_lean_name(label)} : Prop",
                    "origin": "phase1_candidate",
                    "semantic_revision_count": 0,
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            telemetry=FakeTelemetry(),
        )
        evidence = fixture["compiler_error"]

        def candidate(tier: str) -> Phase1LayerCandidate:
            return Phase1LayerCandidate(
                labels=[label],
                parsed=_parse_module(
                    f"theorem {_lean_name(label)} : Prop := by\n  exact\n"
                ),
                import_modules=[],
                generation_tier=tier,
            )

        patches = (
            patch(
                "formalize_blueprint._phase1_compile_plan_defects",
                return_value={},
            ),
            patch(
                "formalize_blueprint._compiler_generation_evidence_by_label",
                return_value={label: evidence},
            ),
            patch("formalize_blueprint._store_generation_candidates"),
            patch("formalize_blueprint._store_generation_feedback"),
            patch("formalize_blueprint._sync_design_plan"),
        )
        with patches[0], patches[1], patches[2], patches[3], patches[4]:
            self.assertFalse(
                _record_retry_failure(
                    ctx,
                    [label],
                    stage="phase1_statement",
                    attempted_tier="base",
                    evidence=fixture["prior_semantic_rejection"],
                    source=f"phase1_layer_{fixture['layer']}_alignment",
                )
            )
            self.assertEqual(
                _retry_next_tier(ctx, label, "phase1_statement"),
                "escalation",
            )

            first = _route_phase1_compile_failure(
                ctx,
                candidate("escalation"),
                evidence,
                fixture["candidate"],
                layer_no=fixture["layer"],
            )
            self.assertFalse(first.authorizes_blueprint_repair)
            self.assertTrue(first.plan_revision_required)
            self.assertIn(label, ctx.blueprint_direct_generation)

            direct_base = _route_phase1_compile_failure(
                ctx,
                candidate("base"),
                evidence,
                fixture["candidate"],
                layer_no=fixture["layer"],
            )
            self.assertFalse(direct_base.authorizes_blueprint_repair)
            self.assertEqual(direct_base.failure_route.action, "singleton")
            self.assertEqual(
                _retry_next_tier(ctx, label, "phase1_statement"),
                "escalation",
            )

            direct_escalated = _route_phase1_compile_failure(
                ctx,
                candidate("escalation"),
                evidence,
                fixture["candidate"],
                layer_no=fixture["layer"],
            )
            self.assertTrue(direct_escalated.authorizes_blueprint_repair)
            self.assertEqual(direct_escalated.labels, [label])
            self.assertTrue(direct_escalated.decomposition_helpers)

        compile_lifecycle = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "node_retry_lifecycle"
            and fields["source"].endswith("_compile")
        ]
        self.assertEqual(
            [fields["next_state"] for fields in compile_lifecycle],
            fixture["expected_compile_lifecycle_states"],
        )
        decompositions = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_compile_exhaustion_decomposition"
        ]
        self.assertEqual(decompositions[-1]["labels"], [label])

    def test_attributed_compile_failure_does_not_advance_sibling_retries(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "scoped_compile_failure_attribution.json"
            ).read_text(encoding="utf-8")
        )
        labels = fixture["labels"]
        owner = fixture["attributed_labels"][0]
        evidence = fixture["compiler_error"]
        ctx = SimpleNamespace(
            name=fixture["blueprint"],
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"{label}-v1" for label in labels},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": f"{label}-v1",
                    "target_signature": f"theorem {_lean_name(label)} : Prop",
                    "origin": "phase1_candidate",
                    "semantic_revision_count": 0,
                }
                for label in labels
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            telemetry=FakeTelemetry(),
        )
        code = "\n".join(
            f"theorem {_lean_name(label)} : Prop := by\n  exact True.intro"
            for label in labels
        )
        failed = Phase1LayerCandidate(
            labels=labels,
            parsed=_parse_module(code),
            import_modules=[],
            generation_tier="base",
        )

        with (
            patch(
                "formalize_blueprint._phase1_compile_plan_defects",
                return_value={},
            ),
            patch(
                "formalize_blueprint._compiler_generation_evidence_by_label",
                return_value={owner: evidence},
            ),
            patch("formalize_blueprint._store_generation_candidates"),
            patch("formalize_blueprint._store_generation_feedback"),
        ):
            request = _route_phase1_compile_failure(
                ctx,
                failed,
                evidence,
                code,
                layer_no=fixture["layer"],
            )

        self.assertEqual(request.labels, [owner])
        self.assertEqual(request.section_labels, [owner])
        self.assertEqual(
            _retry_next_tier(ctx, owner, "phase1_statement"),
            fixture["expected_retry_tier"],
        )
        for label in fixture["preserved_labels"]:
            self.assertEqual(
                _retry_next_tier(ctx, label, "phase1_statement"),
                fixture["expected_preserved_tier"],
            )
        lifecycle_labels = {
            fields["label"]
            for event, fields in ctx.telemetry.events
            if event == "node_retry_lifecycle"
        }
        self.assertEqual(lifecycle_labels, {owner})
        preserved = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_compile_unattributed_siblings_preserved"
        ]
        self.assertEqual(preserved[-1]["failed_labels"], [owner])
        self.assertEqual(
            preserved[-1]["preserved_labels"], fixture["preserved_labels"]
        )

    def test_attributed_compile_failure_preserves_exact_sibling_candidate(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "scoped_compile_failure_attribution.json"
            ).read_text(encoding="utf-8")
        )
        labels = fixture["labels"]
        owner = fixture["attributed_labels"][0]
        preserved_labels = fixture["preserved_labels"]
        code = "\n\n".join(
            f"theorem {_lean_name(label)} : True := by\n  trivial"
            for label in labels
        )
        candidate = Phase1LayerCandidate(
            labels=labels,
            parsed=_parse_module(code),
            import_modules=[],
            generation_tier="base",
        )
        accepted = Section(
            1,
            preserved_labels,
            Path("Skeleton01.lean"),
            "Generated.S1",
            [],
        )
        ctx = SimpleNamespace(
            name=fixture["blueprint"],
            nodes={label: node(label) for label in labels},
            design_plan_entries={},
            workers=1,
            defer_phase1_alignment=False,
            telemetry=FakeTelemetry(),
        )
        routed = RepairRequest(
            "owner retry",
            [owner],
            section_labels=[owner],
            authorizes_blueprint_repair=False,
        )

        def compile_candidate(_ctx, current, *_args, **_kwargs):
            if current.labels == labels:
                return None, fixture["compiler_error"], code
            self.assertEqual(current.labels, preserved_labels)
            return [accepted], "", ""

        with patch(
            "formalize_blueprint._compile_semantic_phase1_candidate",
            side_effect=compile_candidate,
        ) as compile_call, patch(
            "formalize_blueprint._compiler_generation_evidence_by_label",
            return_value={owner: fixture["compiler_error"]},
        ), patch(
            "formalize_blueprint._route_phase1_compile_failure",
            return_value=routed,
        ) as route:
            with self.assertRaises(RepairRequest) as raised:
                _compile_semantic_phase1_candidates(
                    ctx,
                    [candidate],
                    [],
                    _SectionNumberAllocator(1),
                    layer_no=fixture["layer"],
                )

        self.assertEqual(compile_call.call_count, 2)
        self.assertEqual(route.call_args.args[1].labels, [owner])
        self.assertEqual(raised.exception.labels, [owner])
        self.assertEqual(raised.exception.frozen_sections, [accepted])
        events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_compile_candidate_siblings_preserved"
        ]
        self.assertEqual(events[-1]["failed_labels"], [owner])
        self.assertEqual(events[-1]["accepted_labels"], preserved_labels)

    def test_unattributed_compile_failure_keeps_group_isolation_route(
        self,
    ) -> None:
        labels = ["def:first", "def:second"]
        evidence = "Lean failed without a source location"
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"{label}-v1" for label in labels},
            retry_lifecycle={},
            telemetry=FakeTelemetry(),
        )
        code = "\n".join(
            f"def {_lean_name(label)} : Nat := 0" for label in labels
        )
        failed = Phase1LayerCandidate(
            labels=labels,
            parsed=_parse_module(code),
            import_modules=[],
            generation_tier="base",
        )

        with (
            patch(
                "formalize_blueprint._phase1_compile_plan_defects",
                return_value={},
            ),
            patch(
                "formalize_blueprint._compiler_generation_evidence_by_label",
                return_value={},
            ),
            patch("formalize_blueprint._store_generation_candidates"),
            patch("formalize_blueprint._store_generation_feedback"),
        ):
            request = _route_phase1_compile_failure(
                ctx, failed, evidence, code, layer_no=0
            )

        self.assertEqual(request.section_labels, labels)
        self.assertEqual(set(request.labels), set(labels))
        self.assertEqual(request.failure_route.action, "bisect")
        for label in labels:
            self.assertEqual(
                _retry_next_tier(ctx, label, "phase1_statement"),
                "escalation",
            )

    def test_precompile_deterministic_failures_use_bounded_retry_lifecycle(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "simplex_precompile_deterministic_failure_lifecycle.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        ctx = SimpleNamespace(
            name=fixture["blueprint"],
            nodes={label: node(label)},
            stmt_fps={label: fixture["statement_fp"]},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": fixture["statement_fp"],
                    "target_signature": (
                        f"theorem {_lean_name(label)} : Prop"
                    ),
                    "origin": "phase1_candidate",
                    "semantic_revision_count": 0,
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            telemetry=FakeTelemetry(),
        )
        evidence = fixture["deterministic_rejection"]

        def request(tier: str) -> RepairRequest:
            return RepairRequest(
                "Uncompiled Phase-1 candidate failed deterministic checks:\n"
                + evidence,
                [label],
                section_labels=[label],
                authorizes_blueprint_repair=False,
                failure_route=_route_lean_generation_failure([label]),
                evidence_by_label={label: evidence},
                retry_attempted_tier=tier,
            )

        with (
            patch("formalize_blueprint._store_generation_feedback"),
            patch("formalize_blueprint._prune_stale_generation_candidates"),
            patch("formalize_blueprint._sync_design_plan"),
        ):
            base = _route_phase1_precompile_deterministic_failure(
                ctx, request("base"), layer_no=fixture["layer"]
            )
            self.assertEqual(len(base), 1)
            self.assertFalse(base[0].authorizes_blueprint_repair)
            self.assertEqual(
                _retry_next_tier(ctx, label, "phase1_statement"),
                "escalation",
            )

            escalated = _route_phase1_precompile_deterministic_failure(
                ctx, request("escalation"), layer_no=fixture["layer"]
            )
            self.assertEqual(len(escalated), 1)
            self.assertFalse(escalated[0].authorizes_blueprint_repair)
            self.assertTrue(escalated[0].plan_revision_required)
            self.assertIn(label, ctx.blueprint_direct_generation)

            direct_base = _route_phase1_precompile_deterministic_failure(
                ctx, request("base"), layer_no=fixture["layer"]
            )
            self.assertFalse(direct_base[0].authorizes_blueprint_repair)
            self.assertEqual(
                _retry_next_tier(ctx, label, "phase1_statement"),
                "escalation",
            )

            direct_escalated = _route_phase1_precompile_deterministic_failure(
                ctx, request("escalation"), layer_no=fixture["layer"]
            )
            self.assertEqual(len(direct_escalated), 1)
            self.assertTrue(direct_escalated[0].authorizes_blueprint_repair)
            self.assertEqual(direct_escalated[0].labels, [label])
            self.assertTrue(direct_escalated[0].decomposition_helpers)

        lifecycle = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "node_retry_lifecycle"
            and fields["source"].endswith("_deterministic")
        ]
        self.assertEqual(
            [fields["next_state"] for fields in lifecycle],
            fixture["expected_lifecycle_states"],
        )
        decompositions = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_deterministic_exhaustion_decomposition"
        ]
        self.assertEqual(decompositions[-1]["labels"], [label])

    def test_real_repeated_plan_rejection_uses_bounded_three_stage_lifecycle(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "repeated_plan_semantic_exhaustion.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        ctx = SimpleNamespace(
            name=fixture["blueprint"],
            nodes={label: node(label)},
            stmt_fps={label: "finite-register-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "finite-register-v1",
                    "target_signature": "def def_finite_register_operators : Prop",
                    "semantic_revision_count": 0,
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_feedback={},
            generation_candidates={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            telemetry=FakeTelemetry(),
        )
        evidence = fixture["semantic_rejection"]

        with patch(
            "formalize_blueprint._correct_phase1_design_plan", return_value=True
        ) as correct:
            self.assertEqual(
                _semantic_exhaustion_policy(ctx, label), "plan-revision"
            )
            decomposition, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    [label],
                    evidence,
                    layer_no=0,
                    source="historical-replay",
                )
            )
            self.assertEqual(decomposition, set())
            self.assertEqual(revised, {label})
            self.assertEqual(unresolved, set())
            self.assertEqual(
                _semantic_exhaustion_policy(ctx, label), "blueprint-direct"
            )

            decomposition, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    [label],
                    evidence,
                    layer_no=0,
                    source="historical-replay",
                )
            )
            self.assertEqual(decomposition, set())
            self.assertEqual(revised, {label})
            self.assertEqual(unresolved, set())
            self.assertIn(label, ctx.blueprint_direct_generation)
            self.assertEqual(
                _semantic_exhaustion_policy(ctx, label), "decomposition"
            )

            decomposition, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    [label],
                    evidence,
                    layer_no=0,
                    source="historical-replay",
                )
            )
            self.assertEqual(decomposition, {label})
            self.assertEqual(revised, set())
            self.assertEqual(unresolved, set())
            correct.assert_called_once()

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

    def test_mixed_plan_audit_authorizes_blueprint_repair_per_node(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "mixed_plan_audit_routing.json"
            ).read_text(encoding="utf-8")
        )
        security, channel = (
            "def:security-parameter-negligible",
            "def:channel-povm",
        )
        labels = [security, channel]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"{label}-v1" for label in labels},
            tex_blocks={
                security: "Negligible for every eventually positive polynomial.",
                channel: "A completely positive trace-preserving linear map.",
            },
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": f"{label}-v1",
                    "target_signature": f"def {_lean_name(label)} : Prop",
                    "helpers": [],
                    "decisions": [],
                }
                for label in labels
            },
            design_plan_alternates={},
            design_plan="",
            paper_text="",
            base_timeout=120,
            hard_timeout=300,
            base_effort="medium",
            escalation_effort="high",
            retry_lifecycle={},
            generation_candidates={},
            telemetry=FakeTelemetry(),
        )
        response = CallResult(status="ok", text=json.dumps(fixture["payload"]))
        with patch("formalize_blueprint._call_model", return_value=response):
            audit = _audit_phase1_design_plan(ctx, labels)

        self.assertIsInstance(audit, AlignmentAuditResult)
        assert audit is not None
        self.assertEqual(audit.kind, "mixed")
        self.assertEqual(audit.labels_for("blueprint"), {security})
        self.assertEqual(audit.labels_for("lean-generation"), {channel})
        self.assertEqual(
            ctx.design_plan_entries[security]["rejected_kind"], "blueprint"
        )
        self.assertEqual(
            ctx.design_plan_entries[channel]["rejected_kind"], "lean-generation"
        )

        with patch(
            "formalize_blueprint._audit_phase1_design_plan", return_value=audit
        ):
            with self.assertRaises(RepairRequest) as raised:
                _phase1_frontier_plan_gateway(ctx, labels, labels, {})

        self.assertTrue(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(raised.exception.labels, [security])
        self.assertEqual(
            raised.exception.labels,
            fixture["expected_blueprint_repair_labels"],
        )
        self.assertNotIn(channel, raised.exception.model_repair_labels)
        routed = [
            event
            for event in ctx.telemetry.events
            if event[0] == "phase1_frontier_plan_audit_routed"
        ]
        self.assertEqual(len(routed), 1)
        self.assertEqual(routed[0][1]["blueprint_repair_labels"], [security])
        self.assertEqual(
            routed[0][1]["deferred_plan_correction_labels"], [channel]
        )

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

    def test_equivalent_plan_correction_feedback_is_not_called_twice(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase2_orchestration_replay"
                / "equivalent_failure_feedback.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
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
        identity = {label: fixture["same_identity"]}
        with patch(
            "formalize_blueprint._call_model", return_value=unchanged
        ) as call_model:
            self.assertFalse(
                _correct_phase1_design_plan(
                    ctx,
                    [label],
                    fixture["first_feedback"],
                    evidence_identities_by_label=identity,
                )
            )
            self.assertFalse(
                _correct_phase1_design_plan(
                    ctx,
                    [label],
                    fixture["equivalent_feedback"],
                    evidence_identities_by_label=identity,
                )
            )
            self.assertFalse(
                _correct_phase1_design_plan(
                    ctx,
                    [label],
                    fixture["different_feedback"],
                    evidence_identities_by_label={
                        label: fixture["different_identity"]
                    },
                )
            )

        self.assertEqual(call_model.call_count, 2)

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

    def test_frontier_plan_gateway_corrects_only_rejected_contract_slice(self) -> None:
        provider = "def:provider"
        target = "lem:target"
        consumer = "thm:consumer"
        nodes = {
            provider: node(provider),
            target: node(target, uses={provider}),
            consumer: node(consumer, uses={target}),
        }
        ctx = SimpleNamespace(
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": f"{label}-v1",
                    "target_signature": f"def {_lean_name(label)} : Nat",
                    "helpers": [],
                    "decisions": [],
                }
                for label in nodes
            },
            design_plan="",
            retry_lifecycle={},
            generation_candidates={},
            telemetry=FakeTelemetry(),
        )
        rejection = (
            "lean-generation",
            "Interface-plan audit rejected: target drops its provider relation",
            {target},
            [],
        )
        with patch(
            "formalize_blueprint._audit_phase1_design_plan",
            side_effect=[rejection, None],
        ) as audit, patch(
            "formalize_blueprint._correct_phase1_design_plan",
            return_value=True,
        ) as correct, patch(
            "formalize_blueprint._validate_design_plan_contract_closure",
            return_value={},
        ), patch("formalize_blueprint._prune_stale_generation_candidates"):
            remaining = _phase1_frontier_plan_gateway(
                ctx, [target], [provider, target, consumer], {}
            )

        self.assertEqual(remaining, {})
        self.assertEqual(audit.call_count, 2)
        self.assertEqual(correct.call_args.args[1], [target])
        self.assertEqual(
            set(correct.call_args.kwargs["context_labels"]),
            {provider, consumer},
        )
        self.assertFalse(correct.call_args.kwargs["escalated"])
        gateway_events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_frontier_plan_gateway"
        ]
        self.assertEqual(gateway_events[-1]["status"], "accepted_after_correction")

    def test_frontier_plan_gateway_rechecks_scoped_closure_after_correction(self) -> None:
        provider = "def:provider"
        target = "lem:target"
        nodes = {
            provider: node(provider),
            target: node(target, uses={provider}),
        }
        ctx = SimpleNamespace(
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": f"{label}-v1",
                    "target_signature": f"def {_lean_name(label)} : Nat",
                    "helpers": [],
                    "decisions": [],
                }
                for label in nodes
            },
            design_plan="",
            retry_lifecycle={},
            generation_candidates={},
            telemetry=FakeTelemetry(),
        )
        rejection = (
            "lean-generation",
            "Interface-plan audit rejected: missing provider field",
            {target},
            [],
        )
        closure = {target: [f"{target}: missing member on {provider}"]}
        with patch(
            "formalize_blueprint._audit_phase1_design_plan",
            side_effect=[rejection, None],
        ), patch(
            "formalize_blueprint._correct_phase1_design_plan",
            return_value=True,
        ) as correct, patch(
            "formalize_blueprint._validate_design_plan_contract_closure",
            side_effect=[closure, {}],
        ), patch("formalize_blueprint._prune_stale_generation_candidates"):
            remaining = _phase1_frontier_plan_gateway(
                ctx, [target], [provider, target], {}
            )

        self.assertEqual(remaining, {})
        self.assertEqual(correct.call_count, 2)
        self.assertEqual(
            correct.call_args.args[1], [target]
        )

    def test_future_consumer_closure_does_not_block_ready_provider(self) -> None:
        provider = "def:provider"
        consumer = "def:consumer"
        nodes = {
            provider: node(provider),
            consumer: node(consumer, uses={provider}),
        }
        ctx = SimpleNamespace(
            nodes=nodes,
            stmt_fps={label: f"{label}-v1" for label in nodes},
            design_plan_entries={
                provider: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": f"{provider}-v1",
                    "target_signature": "def def_provider : Nat",
                    "helpers": [],
                    "decisions": [],
                },
                consumer: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": f"{consumer}-v1",
                    "target_signature": (
                        "def def_consumer : def_provider.futureMember"
                    ),
                    "helpers": [],
                    "decisions": [],
                },
            },
            design_plan="",
            retry_lifecycle={},
            generation_candidates={},
            telemetry=FakeTelemetry(),
        )
        future_finding = {
            consumer: [
                f"{consumer}: target signature requires "
                "`def_provider.futureMember`, but planned declaration "
                "`def_provider` exposes no such member"
            ]
        }
        with patch(
            "formalize_blueprint._audit_phase1_design_plan",
            return_value=None,
        ) as audit, patch(
            "formalize_blueprint._correct_phase1_design_plan"
        ) as correct:
            remaining = _phase1_frontier_plan_gateway(
                ctx,
                [provider],
                [provider, consumer],
                future_finding,
            )

        self.assertEqual(remaining, future_finding)
        audit.assert_called_once_with(ctx, [provider])
        correct.assert_not_called()

    def test_exhausted_frontier_correction_forces_fresh_scoped_plan(self) -> None:
        label = "def:finite-register-operators"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "register-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": "register-v1",
                    "target_signature": "def def_finite_register_operators : Nat",
                    "helpers": [],
                    "decisions": [],
                    "rejected_audit_fp": "old-rejection",
                }
            },
            design_plan_alternates={label: {"target_signature": "stale"}},
            design_plan="",
            retry_lifecycle={},
            generation_candidates={},
            telemetry=FakeTelemetry(),
        )
        rejection = (
            "lean-generation",
            "Interface-plan audit rejected: partial trace swaps tensor factors",
            {label},
            [],
        )
        with patch(
            "formalize_blueprint._audit_phase1_design_plan",
            return_value=rejection,
        ), patch(
            "formalize_blueprint._correct_phase1_design_plan",
            return_value=False,
        ) as correct:
            with self.assertRaises(RepairRequest):
                _phase1_frontier_plan_gateway(ctx, [label], [label], {})

        self.assertEqual(correct.call_count, 2)
        self.assertNotIn(label, ctx.design_plan_entries)
        self.assertNotIn(label, ctx.design_plan_alternates)
        invalidations = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_frontier_plan_invalidated"
        ]
        self.assertEqual(invalidations[-1]["labels"], [label])
        self.assertEqual(
            invalidations[-1]["next_action"], "fresh_scoped_planning"
        )

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

        with patch("formalize_blueprint._ensure_phase1_semantic_plan") as plan, patch(
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

    def test_bottom_up_phase1_drains_independent_branch_before_repair(self) -> None:
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
        saved: list[list[str]] = []

        def transact(_ctx, _frontier, groups, _sections, alloc):
            labels = [label for group in groups for label in group]
            calls.append(labels)
            if len(calls) == 1:
                number = alloc()
                fast = Section(
                    number,
                    ["def:fast"],
                    Path(f"Skeleton{number:02d}.lean"),
                    f"Generated.Skeleton{number:02d}",
                    [],
                    refined_labels={"def:fast"},
                )
                raise RepairRequest(
                    "slow contract needs another generation attempt",
                    ["def:slow"],
                    context_labels=["def:slow"],
                    frozen_sections=[fast],
                    authorizes_blueprint_repair=False,
                )
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

        def save(_ctx, sections):
            saved.append(
                [label for section in sections for label in section.labels]
            )

        with patch("formalize_blueprint._ensure_phase1_semantic_plan"), patch(
            "formalize_blueprint._run_validated_contract_phase1_layer",
            side_effect=transact,
        ), patch("formalize_blueprint._save_ctx_state", side_effect=save):
            with self.assertRaises(RepairRequest) as raised:
                _run_phase1(ctx, [], set(nodes), "bottom-up")

        self.assertEqual(set(calls[0]), {"def:slow", "def:fast"})
        self.assertEqual(calls[1], ["lem:fast-child"])
        self.assertEqual(raised.exception.labels, ["def:slow"])
        self.assertIn("lem:fast-child", saved[-1])
        events = [event for event, _fields in ctx.telemetry.events]
        self.assertIn("phase1_independent_branch_drain_started", events)
        self.assertIn("phase1_independent_branch_drain_completed", events)

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

    def test_semantic_repair_singletons_share_compatible_correction_wave(self) -> None:
        labels = ["def:a", "def:b", "def:c", "def:d"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp-{label}" for label in labels},
            design_plan_entries={},
            generation_candidates={
                label: {
                    "statement_fp": f"fp-{label}",
                    "plan_fp": "",
                    "code": f"def {_lean_name(label)} : Nat := sorry",
                    "repair_stage": "semantic_rejected",
                    "generation_tier": "base",
                }
                for label in labels
            },
            retry_lifecycle={
                f"phase1_statement:{label}": {
                    "statement_fp": f"fp-{label}",
                    "state": "escalation",
                }
                for label in labels[:3]
            },
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._generation_feedback_for",
            return_value="exact semantic rejection",
        ), patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ):
            groups = _coalesce_phase1_semantic_correction_waves(
                ctx, [[label] for label in labels], []
            )

        self.assertEqual(groups, [labels[:3], [labels[3]]])
        events = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_semantic_correction_waves"
        ]
        self.assertEqual(events[0]["waves"], [labels[:3]])

    def test_semantic_repair_wave_does_not_merge_dependency_contexts(self) -> None:
        labels = ["def:a", "def:b"]
        ctx = SimpleNamespace(
            nodes={label: node(label) for label in labels},
            stmt_fps={label: f"fp-{label}" for label in labels},
            design_plan_entries={},
            generation_candidates={
                label: {
                    "statement_fp": f"fp-{label}",
                    "plan_fp": "",
                    "code": f"def {_lean_name(label)} : Nat := sorry",
                    "repair_stage": "semantic_rejected",
                }
                for label in labels
            },
            retry_lifecycle={},
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._generation_feedback_for",
            return_value="exact semantic rejection",
        ), patch(
            "formalize_blueprint._sections_for_deps",
            side_effect=lambda _ctx, group, _sections: ["A"] if group == ["def:a"] else ["B"],
        ):
            groups = _coalesce_phase1_semantic_correction_waves(
                ctx, [["def:a"], ["def:b"]], []
            )

        self.assertEqual(groups, [["def:a"], ["def:b"]])

    def test_validated_contract_layer_streams_generation_into_compile(self) -> None:
        labels = ["def:a", "def:b"]
        ctx = SimpleNamespace(workers=2, telemetry=FakeTelemetry())
        events: list[str] = []
        release_slow_generation = threading.Event()

        def candidate(label: str) -> Phase1LayerCandidate:
            return Phase1LayerCandidate(
                labels=[label],
                parsed=_parse_module(f"def {_lean_name(label)} : Nat := sorry\n"),
                import_modules=[],
                generation_tier="base",
            )

        def generate(_ctx, group, _sections):
            label = group[0]
            events.append(f"generate:{label}:start")
            if label == "def:b":
                self.assertTrue(release_slow_generation.wait(timeout=2))
            events.append(f"generate:{label}:done")
            return candidate(group[0])

        compiled = {
            label: Section(
                index,
                [label],
                Path(f"Skeleton{index:02d}.lean"),
                f"Generated.S{index}",
                [],
            )
            for index, label in enumerate(labels, 1)
        }

        def compile_candidate(_ctx, item, *_args, **_kwargs):
            label = item.labels[0]
            events.append(f"compile:{label}")
            if label == "def:a":
                release_slow_generation.set()
            return [compiled[label]], "", ""

        def integrate(*_args, **_kwargs):
            events.append("final-audit")
            return list(compiled.values())

        with patch(
            "formalize_blueprint._generate_uncompiled_phase1_candidate",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._compile_semantic_phase1_candidate",
            side_effect=compile_candidate,
        ), patch(
            "formalize_blueprint._audit_phase1_layer_candidates",
            side_effect=integrate,
        ):
            result = _run_validated_contract_phase1_layer(
                ctx, 0, [["def:a"], ["def:b"]], [], _SectionNumberAllocator(1)
            )

        self.assertEqual(result, list(compiled.values()))
        self.assertLess(
            events.index("compile:def:a"),
            events.index("generate:def:b:done"),
        )
        self.assertLess(events.index("compile:def:b"), events.index("final-audit"))

    def test_phase1_candidate_typecheck_defers_object_generation(self) -> None:
        label = "def:a"
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("def def_a : Nat := 1\n"),
            import_modules=[],
            generation_tier="base",
        )
        section = Section(
            1,
            [label],
            Path("Skeleton01.lean"),
            "Generated.S1",
            [],
            refined_labels=set(),
        )
        ctx = SimpleNamespace(
            workers=1,
            defer_phase1_alignment=False,
            telemetry=FakeTelemetry(),
        )
        with patch(
            "formalize_blueprint._freeze_section_from_code",
            return_value=[section],
        ) as freeze:
            result = _compile_semantic_phase1_candidates(
                ctx,
                [candidate],
                [],
                _SectionNumberAllocator(1),
                layer_no=0,
            )

        self.assertEqual(result, [section])
        self.assertTrue(freeze.call_args.kwargs["defer_object_gate"])

    def test_phase1_candidate_reuses_preaudit_object_after_acceptance(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "Skeleton01.lean"
            ctx = SimpleNamespace(
                name="paper",
                nodes={"def:a": node("def:a")},
                unavailable_imports=set(),
                defer_phase1_alignment=True,
                workers=1,
                lean_command=["lean"],
                telemetry=FakeTelemetry(),
                design_plan_entries={},
            )
            attempt = SimpleNamespace(
                ok=True,
                output="",
                duration_s=0.1,
                kind="lean",
            )
            with patch(
                "formalize_blueprint._section_module",
                return_value=("Generated.S1", path),
            ), patch(
                "formalize_blueprint._compile_module_olean",
                return_value=attempt,
            ) as first_compile, patch(
                "formalize_blueprint._section_objects_exist",
                return_value=True,
            ), patch(
                "formalize_blueprint._section_compile_fingerprint",
                return_value="fp",
            ), patch(
                "formalize_blueprint._skeleton_code_findings",
                return_value=[],
            ), patch(
                "formalize_blueprint._skeleton_deterministic_findings",
                return_value=[],
            ):
                sections = _freeze_section_from_code(
                    ctx,
                    ["def:a"],
                    [],
                    _SectionNumberAllocator(1),
                    ["def def_a : Nat := sorry"],
                    [],
                    [],
                    defer_object_gate=True,
                )
                self.assertIsNotNone(sections)
                section = sections[0]
                self.assertEqual(section.compile_fingerprint, "fp")

                with patch(
                    "formalize_blueprint._compile_fast_candidate_object"
                ) as second_compile, patch(
                    "formalize_blueprint._check_lean", return_value=(True, "")
                ), patch(
                    "formalize_blueprint.SCRATCH_DIR", root / "scratch"
                ), patch("formalize_blueprint._note_frozen_section"):
                    accepted = _finalize_phase1_accepted_sections(
                        ctx, 0, [section], []
                    )

        self.assertEqual(accepted, [section])
        first_compile.assert_called_once()
        second_compile.assert_not_called()

    def test_semantically_accepted_phase1_section_builds_object_before_freeze(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "Skeleton01.lean"
            path.write_text("def def_a : Nat := 1\n", encoding="utf-8")
            section = Section(
                1,
                ["def:a"],
                path,
                "Generated.S1",
                [],
                refined_labels=set(),
            )
            ctx = SimpleNamespace(
                name="paper",
                workers=1,
                lean_command=["lean"],
                telemetry=FakeTelemetry(),
            )
            with patch(
                "formalize_blueprint._compile_fast_candidate_object",
                return_value=(SimpleNamespace(ok=True), "", ""),
            ) as object_build, patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._section_objects_exist", return_value=False
            ), patch(
                "formalize_blueprint._note_frozen_section"
            ) as frozen:
                accepted = _finalize_phase1_accepted_sections(
                    ctx, 0, [section], []
                )

        self.assertEqual(accepted, [section])
        object_build.assert_called_once()
        frozen.assert_called_once_with(ctx, ["def:a"])
        self.assertEqual(section.refined_labels, {"def:a"})

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
            "formalize_blueprint._compile_semantic_phase1_candidate",
            side_effect=lambda _ctx, candidate, *_args, **_kwargs: (
                [
                    Section(
                        1,
                        list(candidate.labels),
                        Path("Skeleton01.lean"),
                        "Generated.S1",
                        [],
                    )
                ],
                "",
                "",
            ),
        ) as compile_candidate, patch(
            "formalize_blueprint._audit_phase1_layer_candidates",
            return_value=compiled,
        ):
            _run_validated_contract_phase1_layer(
                ctx, 0, [["def:a"], ["def:b"]], [], _SectionNumberAllocator(1)
            )

        revise.assert_not_called()
        self.assertEqual(
            {
                call.args[1].labels[0]
                for call in compile_candidate.call_args_list
            },
            set(labels),
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
            "formalize_blueprint._compile_semantic_phase1_candidate",
            return_value=([accepted], "", ""),
        ) as compile_candidate, patch(
            "formalize_blueprint._audit_phase1_layer_candidates",
            return_value=[accepted],
        ) as audit:
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
        compile_candidate.assert_called_once()
        audit.assert_called_once()
        self.assertEqual(raised.exception.labels, ["def:b"])
        self.assertEqual(raised.exception.frozen_sections, [accepted])

    def test_streamed_compile_failure_keeps_compile_failure_route(self) -> None:
        label = "def:a"
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("def def_a : Nat := sorry\n"),
            import_modules=[],
            generation_tier="base",
        )
        routed = RepairRequest(
            "Lean compile failure already routed",
            [label],
            section_labels=[label],
            authorizes_blueprint_repair=False,
        )
        ctx = SimpleNamespace(workers=1, telemetry=FakeTelemetry())

        with patch(
            "formalize_blueprint._generate_uncompiled_phase1_candidate",
            return_value=candidate,
        ), patch(
            "formalize_blueprint._compile_semantic_phase1_candidate",
            return_value=(None, "exact Lean error", "def def_a : Nat := sorry"),
        ), patch(
            "formalize_blueprint._route_phase1_compile_failure",
            return_value=routed,
        ) as compile_route, patch(
            "formalize_blueprint._route_phase1_precompile_deterministic_failure"
        ) as precompile_route, patch(
            "formalize_blueprint._store_generation_candidates"
        ):
            with self.assertRaises(RepairRequest) as raised:
                _run_validated_contract_phase1_layer(
                    ctx,
                    1,
                    [[label]],
                    [],
                    _SectionNumberAllocator(1),
                )

        compile_route.assert_called_once()
        precompile_route.assert_not_called()
        self.assertEqual(raised.exception.labels, [label])

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

    def test_parallel_compile_aggregates_authorized_exhaustion_route(self) -> None:
        label = "thm:security"
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module(f"theorem {_lean_name(label)} : True := by trivial\n"),
            import_modules=[],
            generation_tier="escalation",
        )
        ctx = SimpleNamespace(workers=1, telemetry=FakeTelemetry())

        def fail_compile(_ctx, _labels, *_args, **kwargs):
            kwargs["failure_evidence"].append("unexpected token ':'")
            return None

        authorized = RepairRequest(
            "compiler lifecycle exhausted",
            [label],
            decomposition_helpers=["introduce an explicit helper lemma"],
            section_labels=[label],
            authorizes_blueprint_repair=True,
        )
        with patch(
            "formalize_blueprint._freeze_section_from_code",
            side_effect=fail_compile,
        ), patch(
            "formalize_blueprint._route_phase1_compile_failure",
            return_value=authorized,
        ):
            with self.assertRaises(RepairRequest) as raised:
                _compile_semantic_phase1_candidates(
                    ctx,
                    [candidate],
                    [],
                    _SectionNumberAllocator(1),
                    layer_no=3,
                )

        self.assertTrue(raised.exception.authorizes_blueprint_repair)
        self.assertEqual(raised.exception.labels, [label])
        self.assertEqual(
            raised.exception.decomposition_helpers,
            ["introduce an explicit helper lemma"],
        )

    def test_parallel_compile_revises_only_plan_defect_in_mixed_failure(self) -> None:
        labels = ["lem:plan-defect", "lem:generated-defect"]
        candidate = Phase1LayerCandidate(
            labels=labels,
            parsed=_parse_module(
                "theorem lem_plan_defect : True := sorry\n\n"
                "theorem lem_generated_defect : True := sorry\n"
            ),
            import_modules=[],
            generation_tier="base",
        )
        ctx = SimpleNamespace(workers=1, telemetry=FakeTelemetry())

        def fail_compile(_ctx, _labels, *_args, **kwargs):
            kwargs["failure_evidence"].append("Lean rejected both declarations")
            return None

        with patch(
            "formalize_blueprint._freeze_section_from_code",
            side_effect=fail_compile,
        ), patch(
            "formalize_blueprint._phase1_compile_plan_defects",
            return_value={labels[0]: "plan-owned unknown name"},
        ), patch(
            "formalize_blueprint._revise_exhausted_phase1_contracts",
            return_value={labels[0]},
        ) as revise, patch(
            "formalize_blueprint._store_generation_candidates"
        ), patch(
            "formalize_blueprint._store_generation_feedback"
        ):
            with self.assertRaises(RepairRequest) as raised:
                _compile_semantic_phase1_candidates(
                    ctx,
                    [candidate],
                    [],
                    _SectionNumberAllocator(1),
                    layer_no=0,
                )

        self.assertEqual(raised.exception.labels, [labels[1]])
        self.assertEqual(raised.exception.failure_route.failed_labels, (labels[1],))
        self.assertFalse(raised.exception.plan_revision_required)
        self.assertEqual(
            revise.call_args.kwargs["policy"],
            "post_compile_plan_realization",
        )

    def test_parallel_compile_all_plan_defects_restart_without_quarantine(self) -> None:
        label = "lem:plan-defect"
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("theorem lem_plan_defect : True := sorry\n"),
            import_modules=[],
            generation_tier="base",
        )
        ctx = SimpleNamespace(workers=1, telemetry=FakeTelemetry())

        def fail_compile(_ctx, _labels, *_args, **kwargs):
            kwargs["failure_evidence"].append("unknown plan-owned identifier")
            return None

        with patch(
            "formalize_blueprint._freeze_section_from_code",
            side_effect=fail_compile,
        ), patch(
            "formalize_blueprint._phase1_compile_plan_defects",
            return_value={label: "plan-owned unknown name"},
        ), patch(
            "formalize_blueprint._revise_exhausted_phase1_contracts",
            return_value={label},
        ), patch(
            "formalize_blueprint._store_generation_candidates"
        ), patch(
            "formalize_blueprint._store_generation_feedback"
        ):
            with self.assertRaises(RepairRequest) as raised:
                _compile_semantic_phase1_candidates(
                    ctx,
                    [candidate],
                    [],
                    _SectionNumberAllocator(1),
                    layer_no=0,
                )

        self.assertEqual(raised.exception.labels, [label])
        self.assertTrue(raised.exception.plan_revision_required)
        self.assertIsNone(raised.exception.failure_route)

    def test_parallel_compile_routes_plan_defect_before_slow_sibling_finishes(
        self,
    ) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "compile_plan_defect_head_of_line.json"
            ).read_text(encoding="utf-8")
        )
        plan_label = fixture["plan_defect_label"]
        slow_label = fixture["slow_sibling_label"]
        candidates = [
            Phase1LayerCandidate(
                labels=[label],
                parsed=_parse_module(f"def {_lean_name(label)} : Nat := 1\n"),
                import_modules=[],
                generation_tier="base",
            )
            for label in (plan_label, slow_label)
        ]
        ctx = SimpleNamespace(workers=2, telemetry=FakeTelemetry())
        correction_started = threading.Event()
        sibling_observed_correction: list[bool] = []

        def fail_compile(_ctx, candidate_labels, *_args, **kwargs):
            label = candidate_labels[0]
            if label == slow_label:
                sibling_observed_correction.append(
                    correction_started.wait(timeout=0.5)
                )
            kwargs["failure_evidence"].append(f"Lean failed for {label}")
            return None

        def plan_defects(_ctx, labels, _code, _evidence):
            return (
                {plan_label: "plan-owned unknown name"}
                if plan_label in labels
                else {}
            )

        def revise(_ctx, labels, _evidence, **_kwargs):
            if plan_label in labels:
                correction_started.set()
                return {plan_label}
            return set()

        with patch(
            "formalize_blueprint._freeze_section_from_code",
            side_effect=fail_compile,
        ), patch(
            "formalize_blueprint._phase1_compile_plan_defects",
            side_effect=plan_defects,
        ), patch(
            "formalize_blueprint._revise_exhausted_phase1_contracts",
            side_effect=revise,
        ), patch(
            "formalize_blueprint._store_generation_candidates"
        ), patch(
            "formalize_blueprint._store_generation_feedback"
        ):
            with self.assertRaises(RepairRequest) as raised:
                _compile_semantic_phase1_candidates(
                    ctx,
                    candidates,
                    [],
                    _SectionNumberAllocator(1),
                    layer_no=fixture["layer"],
                )

        self.assertTrue(correction_started.is_set())
        self.assertEqual(sibling_observed_correction, [True])
        self.assertIn(plan_label, raised.exception.labels)
        self.assertIn(slow_label, raised.exception.labels)
        self.assertTrue(raised.exception.plan_revision_required)
        routed = [
            fields
            for event, fields in ctx.telemetry.events
            if event == "phase1_compile_failure_routed"
        ]
        self.assertEqual(
            {fields["classification"] for fields in routed},
            {"plan_revision", "lean_generation"},
        )

    def test_plan_owned_unknown_name_skips_local_compiler_patch_calls(self) -> None:
        label = "lem:claim"
        signature = "theorem lem_claim : Nat.ceilLog 3 4 ≤ 2"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": signature,
                    "helpers": [],
                }
            },
            generation_candidates={},
            unavailable_imports=set(),
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
            base_timeout=120,
        )
        evidence: list[str] = []
        failed_code: list[str] = []
        output = "error(lean.unknownIdentifier): Unknown constant `Nat.ceilLog`"

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with patch(
                "formalize_blueprint._section_module",
                return_value=("Generated.Skeleton01", root / "Skeleton01.lean"),
            ), patch(
                "formalize_blueprint._discard_section_artifacts"
            ), patch(
                "formalize_blueprint._check_lean",
                return_value=(False, output),
            ) as check, patch(
                "formalize_blueprint._targeted_patch_skeleton_decls"
            ) as patch_decls:
                result = _freeze_section_from_code(
                    ctx,
                    [label],
                    [],
                    _SectionNumberAllocator(1),
                    [signature + " := sorry"],
                    [],
                    [],
                    allow_patch=True,
                    route_plan_defects=True,
                    failure_evidence=evidence,
                    failure_candidate_code=failed_code,
                )

        self.assertIsNone(result)
        self.assertEqual(check.call_count, 2)
        patch_decls.assert_not_called()
        self.assertIn("plan-realizing interface", evidence[0])
        self.assertIn("Nat.ceilLog", failed_code[0])

    def test_phase1_interface_timeout_skips_local_compiler_patch_calls(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "simplex_interface_usability_lifecycle.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        signature = f"theorem {_lean_name(label)} : True := sorry"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={},
            semantic_plan_entries={},
            unavailable_imports=set(),
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
            base_timeout=120,
            defer_phase1_alignment=False,
        )
        evidence: list[str] = []
        failed_code: list[str] = []

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with patch(
                "formalize_blueprint._section_module",
                return_value=("Generated.Skeleton01", root / "Skeleton01.lean"),
            ), patch(
                "formalize_blueprint._sections_for_deps", return_value=[]
            ), patch(
                "formalize_blueprint._skeleton_code_findings", return_value=[]
            ), patch(
                "formalize_blueprint._skeleton_deterministic_findings",
                return_value=[],
            ), patch(
                "formalize_blueprint._discard_section_artifacts"
            ), patch(
                "formalize_blueprint._check_lean",
                return_value=(False, fixture["heartbeat_timeout"]),
            ) as check, patch(
                "formalize_blueprint._targeted_patch_skeleton_decls"
            ) as patch_decls:
                result = _freeze_section_from_code(
                    ctx,
                    [label],
                    [],
                    _SectionNumberAllocator(1),
                    [signature],
                    [],
                    [],
                    allow_patch=True,
                    failure_evidence=evidence,
                    failure_candidate_code=failed_code,
                )

        self.assertIsNone(result)
        check.assert_called_once()
        patch_decls.assert_not_called()
        self.assertEqual(len(failed_code), 1)
        self.assertTrue(evidence[0].startswith(OBJECT_INTERFACE_FAILURE_PREFIX))
        self.assertTrue(
            any(
                event == "phase1_interface_usability_patch_bypassed"
                for event, _fields in ctx.telemetry.events
            )
        )

    def test_phase1_ordinary_lean_failure_keeps_local_compiler_patch(self) -> None:
        label = "lem:claim"
        signature = f"theorem {_lean_name(label)} : True := sorry"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={},
            semantic_plan_entries={},
            unavailable_imports=set(),
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
            base_timeout=120,
            defer_phase1_alignment=False,
        )

        class PatchReached(RuntimeError):
            pass

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            with patch(
                "formalize_blueprint._section_module",
                return_value=("Generated.Skeleton01", root / "Skeleton01.lean"),
            ), patch(
                "formalize_blueprint._sections_for_deps", return_value=[]
            ), patch(
                "formalize_blueprint._skeleton_code_findings", return_value=[]
            ), patch(
                "formalize_blueprint._skeleton_deterministic_findings",
                return_value=[],
            ), patch(
                "formalize_blueprint._discard_section_artifacts"
            ), patch(
                "formalize_blueprint._check_lean",
                return_value=(
                    False,
                    "Skeleton01.lean:6:0: error: unexpected token 'end'",
                ),
            ) as check, patch(
                "formalize_blueprint._targeted_patch_skeleton_decls",
                side_effect=PatchReached,
            ) as patch_decls:
                with self.assertRaises(PatchReached):
                    _freeze_section_from_code(
                        ctx,
                        [label],
                        [],
                        _SectionNumberAllocator(1),
                        [signature],
                        [],
                        [],
                        allow_patch=True,
                    )

        check.assert_called_once()
        patch_decls.assert_called_once()

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
            "formalize_blueprint._compile_semantic_phase1_candidate",
            return_value=(
                [
                    Section(
                        2,
                        ["def:a", "def:c"],
                        Path("Skeleton02.lean"),
                        "Generated.S2",
                        [],
                    )
                ],
                "",
                "",
            ),
        ), patch(
            "formalize_blueprint._audit_phase1_layer_candidates",
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
                "formalize_blueprint._finalize_phase1_accepted_sections",
                return_value=[retained, candidates[1]],
            ) as finalize, patch(
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
        finalized = finalize.call_args.args[2]
        self.assertEqual(
            {label for section in finalized for label in section.labels},
            {"def:a", "def:c"},
        )

    def test_exact_plan_rejection_revises_before_generation_retry(self) -> None:
        label = "def:a"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            stmt_fps={label: "fp-a"},
            design_plan_entries={},
            generation_feedback={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            workers=1,
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
        )
        audit_result = AlignmentAuditResult(
            kind="lean-generation",
            reason="the plan omits a public blueprint condition",
            rejected={label},
            helpers=[],
            kinds_by_label={label: "lean-generation"},
            reasons_by_label={
                label: "the plan omits a public blueprint condition"
            },
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "Skeleton01.lean"
            path.write_text("def def_a : Prop := sorry\n", encoding="utf-8")
            candidate = Section(1, [label], path, "Generated.S1", [])
            with patch("formalize_blueprint.SCRATCH_DIR", root), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._model_alignment_audit",
                return_value=audit_result,
            ), patch(
                "formalize_blueprint._plan_realized_semantic_rejections",
                return_value={label},
            ), patch(
                "formalize_blueprint._revise_exhausted_phase1_contracts",
                return_value={label},
            ) as revise, patch(
                "formalize_blueprint._record_retry_failure"
            ) as retry_failure:
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(ctx, 1, [candidate])

        revise.assert_called_once_with(
            ctx,
            {label},
            "Blueprint contract audit rejected:\n"
            "- the plan omits a public blueprint condition",
        )
        retry_failure.assert_not_called()
        self.assertEqual(raised.exception.labels, [label])
        self.assertEqual(raised.exception.failure_route.action, "independent")
        self.assertTrue(
            any(
                event == "phase1_plan_realized_semantic_rejection"
                for event, _fields in ctx.telemetry.events
            )
        )

    def test_reported_combined_defect_revises_plan_before_generation_retry(self) -> None:
        label = "def:key-space"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            stmt_fps={label: "fp-key"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_key_space : Type",
                    "helpers": [],
                }
            },
            generation_candidates={},
            generation_feedback={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            workers=1,
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
        )
        audit_result = AlignmentAuditResult(
            kind="lean-generation",
            reason="the plan and Lean both abstract away concrete key pairs",
            rejected={label},
            helpers=[],
            kinds_by_label={label: "lean-generation"},
            reasons_by_label={
                label: "the plan and Lean both abstract away concrete key pairs"
            },
            origins_by_label={label: "both"},
            plan_requirements_by_label={
                label: ["keys are exactly valid coordinate pairs"]
            },
        )
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            path = root / "Skeleton01.lean"
            path.write_text("def def_key_space : Type := Nat\n", encoding="utf-8")
            candidate = Section(1, [label], path, "Generated.S1", [])
            with patch("formalize_blueprint.SCRATCH_DIR", root), patch(
                "formalize_blueprint._check_lean", return_value=(True, "")
            ), patch(
                "formalize_blueprint._model_alignment_audit",
                return_value=audit_result,
            ), patch(
                "formalize_blueprint._revise_exhausted_phase1_contracts",
                return_value={label},
            ) as revise, patch(
                "formalize_blueprint._plan_realized_semantic_rejections",
                return_value=set(),
            ), patch(
                "formalize_blueprint._record_retry_failure"
            ) as retry_failure:
                with self.assertRaises(RepairRequest) as raised:
                    _audit_phase1_layer_candidates(ctx, 2, [candidate])

        revise.assert_called_once()
        evidence = revise.call_args.args[2]
        self.assertIn("keys are exactly valid coordinate pairs", evidence)
        retry_failure.assert_not_called()
        self.assertEqual(raised.exception.labels, [label])
        self.assertEqual(raised.exception.failure_route.action, "independent")
        self.assertTrue(
            any(
                event == "phase1_audit_origin_plan_revision"
                for event, _fields in ctx.telemetry.events
            )
        )

    def test_semantic_first_combined_defect_uses_same_plan_route(self) -> None:
        label = "def:tensor-pauli-notation"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            telemetry=FakeTelemetry(),
        )
        candidate = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("def def_tensor_pauli_notation : Type := Nat\n"),
            import_modules=[],
            generation_tier="base",
        )
        audit = AlignmentAuditResult(
            kind="lean-generation",
            reason="the plan hides the tensor product behind an arbitrary type",
            rejected={label},
            helpers=[],
            kinds_by_label={label: "lean-generation"},
            reasons_by_label={
                label: "the plan hides the tensor product behind an arbitrary type"
            },
            origins_by_label={label: "both"},
            plan_requirements_by_label={
                label: ["the indexed tensor-product formula"]
            },
        )
        with patch(
            "formalize_blueprint._revise_exhausted_phase1_contracts",
            return_value={label},
        ) as revise, patch(
            "formalize_blueprint._record_retry_failure"
        ) as retry_failure:
            request = _semantic_first_failure_request(
                ctx, 4, [candidate], audit, []
            )

        revise.assert_called_once()
        retry_failure.assert_not_called()
        self.assertEqual(request.labels, [label])
        self.assertEqual(request.failure_route.action, "independent")
        self.assertFalse(request.authorizes_blueprint_repair)

    def test_compile_unknown_name_copied_from_plan_is_plan_defect(self) -> None:
        label = "lem:ahm-lower-bound"
        plan = "theorem lem_ahm_lower_bound (m : Nat) : Nat.ceilLog 3 m ≤ m"
        code = plan + " := by sorry"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": plan,
                    "helpers": [],
                }
            },
            generation_candidates={},
        )
        output = (
            "Skeleton.lean:1:44: error(lean.unknownIdentifier): "
            "Unknown constant `Nat.ceilLog`\n"
            "Skeleton.lean:1:1: error: unknown namespace `BigOperators`"
        )

        defects = _phase1_compile_plan_defects(ctx, [label], code, output)

        self.assertEqual(set(defects), {label})
        self.assertIn("Nat.ceilLog", defects[label])
        self.assertNotIn("BigOperators", defects[label])

    def test_generated_only_unknown_name_stays_generation_failure(self) -> None:
        label = "lem:claim"
        plan = "theorem lem_claim : True"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": plan,
                    "helpers": [],
                }
            },
            generation_candidates={},
        )

        self.assertEqual(
            _phase1_compile_plan_defects(
                ctx,
                [label],
                plan + " := by sorry",
                "error: unknown namespace `BigOperators`",
            ),
            {},
        )

    def test_unknown_helper_type_requires_exact_helper_interface(self) -> None:
        label = "def:claim"
        plan = "def def_claim : Prop"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": plan,
                    "helpers": [{
                        "name": "ClaimData",
                        "kind": "structure",
                        "members": [{
                            "name": "value",
                            "type": "MissingLibrary.Type",
                        }],
                    }],
                }
            },
            generation_candidates={},
        )
        code = (
            "structure _autobp_f5a1bed77d1e_ClaimData where\n"
            "  value : Nat\n\n"
            "def def_claim : Prop := sorry"
        )

        self.assertEqual(
            _phase1_compile_plan_defects(
                ctx,
                [label],
                code,
                "error: unknown constant `MissingLibrary.Type`",
            ),
            {},
        )

    def test_repeated_exact_plan_compile_failure_becomes_plan_defect(self) -> None:
        label = "lem:claim"
        plan = "theorem lem_claim (n : Nat) : n = n"
        code = plan + " := by sorry"
        output = "Skeleton01.lean:2:3: error: failed to synthesize Widget Nat"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "semantic_revision_count": 2,
                    "target_signature": plan,
                    "helpers": [],
                }
            },
            generation_candidates={},
        )
        ctx.generation_candidates[label] = {
            "plan_fp": _candidate_plan_fingerprint(ctx, label),
            "lean_status": "failed",
            "lean_output": "Other.lean:99:8: error: failed to synthesize Widget Nat",
        }

        defects = _phase1_compile_plan_defects(ctx, [label], code, output)

        self.assertEqual(set(defects), {label})
        self.assertIn("repeated", defects[label])

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

    def test_uncompiled_candidate_captures_realized_contract_epoch(self) -> None:
        label = "lem:claim"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "theorem lem_claim : True",
                    "helpers": [],
                    "decisions": [],
                }
            },
            blueprint_direct_generation={},
            retry_lifecycle={},
            base_timeout=10,
            hard_timeout=20,
            telemetry=FakeTelemetry(),
        )
        before = _candidate_plan_fingerprint(ctx, label)

        def generate(_ctx, _sec, _labels, _sections, _imports, _parsed, **kwargs):
            _ctx.design_plan_entries[label] = {
                "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                "target_signature": "theorem lem_claim : Nat = Nat",
                "helpers": [],
                "decisions": [],
            }
            kwargs["generation_tier_out"].append("base")
            return _parse_module("theorem lem_claim : Nat = Nat := sorry\n")

        with patch(
            "formalize_blueprint._semantic_repair_candidate", return_value=None
        ), patch(
            "formalize_blueprint._reusable_uncompiled_candidate", return_value=None
        ), patch(
            "formalize_blueprint._generate_phase1_statement_group",
            side_effect=generate,
        ), patch(
            "formalize_blueprint._sections_for_deps", return_value=[]
        ), patch(
            "formalize_blueprint._skeleton_code_findings", return_value=[]
        ), patch(
            "formalize_blueprint._skeleton_deterministic_findings", return_value=[]
        ), patch(
            "formalize_blueprint._store_generation_candidates"
        ):
            candidate = _generate_uncompiled_phase1_candidate(ctx, [label], [])

        after = _candidate_plan_fingerprint(ctx, label)
        self.assertNotEqual(before, after)
        self.assertEqual(candidate.plan_fps, {label: after})

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
                "formalize_blueprint._finalize_phase1_accepted_sections",
                return_value=[retained, candidates[1]],
            ), patch(
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
            {
                "event": "model_call",
                "run_id": "run-1",
                "blueprint": "paper",
                "purpose": "post_repair_blueprint_audit",
                "labels": ["def:b"],
                "duration_s": 7.5,
                "status": "ok",
            },
            {
                "event": "post_repair_boundary_audit",
                "run_id": "run-1",
                "blueprint": "paper",
                "labels": ["def:b"],
                "status": "repair_required",
                "issue_count": 1,
                "repair_labels": [],
                "required_dependencies": {"def:b": ["def:a"]},
                "decomposition_helpers": [],
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
        boundary = build_datasets(events)["post_repair_boundary_examples"]
        self.assertEqual(len(boundary), 1)
        self.assertEqual(boundary[0]["status"], "repair_required")
        self.assertEqual(
            boundary[0]["required_dependencies"], {"def:b": ["def:a"]}
        )
        self.assertEqual(boundary[0]["model_call_count"], 1)
        self.assertEqual(boundary[0]["model_duration_total_s"], 7.5)

    def test_statement_surface_probe_preserves_interface_and_removes_body(self) -> None:
        code = """import Mathlib

structure SameNodePackage where
  value : Nat

theorem lem_target (n : Nat) : n = n := by
  exact rfl
"""

        probe, changed = _statement_surface_probe_code(code, {"lem_target"})

        self.assertEqual(changed, ["lem_target"])
        self.assertIn("structure SameNodePackage where\n  value : Nat", probe)
        self.assertIn("theorem lem_target (n : Nat) : n = n := sorry", probe)
        self.assertNotIn("exact rfl", probe)

    def test_object_gate_identifies_expensive_public_interface(self) -> None:
        timeout = LeanAttempt(
            ok=False,
            command=["lean"],
            reason="timed out",
            kind="object-timeout",
            duration_s=OBJECT_COMPILE_USABILITY_TIMEOUT,
        )
        ctx = SimpleNamespace(
            name="paper",
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
        )
        code = "theorem lem_target (n : Nat) : n = n := by\n  rfl\n"

        with tempfile.TemporaryDirectory() as tmp, patch(
            "formalize_blueprint.SCRATCH_DIR", Path(tmp)
        ), patch(
            "formalize_blueprint._compile_module_olean",
            side_effect=[timeout, timeout],
        ) as compile_object:
            attempt, failure_class, evidence = _compile_fast_candidate_object(
                ctx,
                Path(tmp) / "Target.lean",
                code,
                ["lem:target"],
                complete_bodies=True,
            )

        self.assertIs(attempt, timeout)
        self.assertEqual(failure_class, "interface_usability")
        self.assertTrue(evidence.startswith(OBJECT_INTERFACE_FAILURE_PREFIX))
        self.assertIn("proof regeneration cannot fix it", evidence)
        self.assertEqual(compile_object.call_count, 2)
        self.assertTrue(
            all(
                call.kwargs["timeout"] == OBJECT_COMPILE_USABILITY_TIMEOUT
                for call in compile_object.call_args_list
            )
        )

    def test_object_gate_identifies_expensive_implementation_body(self) -> None:
        timeout = LeanAttempt(
            ok=False,
            command=["lean"],
            reason="timed out",
            kind="object-timeout",
            duration_s=OBJECT_COMPILE_USABILITY_TIMEOUT,
        )
        statement_ok = LeanAttempt(
            ok=True,
            command=["lean"],
            kind="lean",
            duration_s=2.5,
        )
        ctx = SimpleNamespace(
            name="paper",
            lean_command=["lean"],
            telemetry=FakeTelemetry(),
        )
        code = "theorem lem_target (n : Nat) : n = n := by\n  rfl\n"

        with tempfile.TemporaryDirectory() as tmp, patch(
            "formalize_blueprint.SCRATCH_DIR", Path(tmp)
        ), patch(
            "formalize_blueprint._compile_module_olean",
            side_effect=[timeout, statement_ok],
        ):
            _attempt, failure_class, evidence = _compile_fast_candidate_object(
                ctx,
                Path(tmp) / "Target.lean",
                code,
                ["lem:target"],
                complete_bodies=True,
            )

        self.assertEqual(failure_class, "implementation_object")
        self.assertTrue(
            evidence.startswith(OBJECT_IMPLEMENTATION_FAILURE_PREFIX)
        )
        self.assertIn("Preserve the public statement", evidence)
        self.assertEqual(
            _phase2_candidate_failure_kind(evidence), "implementation_object"
        )

    def test_complete_node_correction_policy_uses_object_diagnosis(self) -> None:
        label = "lem:target"
        ctx = SimpleNamespace(
            name="paper",
            nodes={label: node(label)},
            tex_blocks={label: "\\begin{lemma}Target.\\end{lemma}"},
        )

        with patch(
            "formalize_blueprint._frozen_interface_digest", return_value=""
        ), patch(
            "formalize_blueprint._dependency_contract_table", return_value=""
        ), patch("formalize_blueprint._common_rules", return_value=""):
            interface_prompt = _phase2_complete_node_correction_prompt(
                ctx,
                label,
                [],
                [],
                candidate_code="theorem lem_target : True := by trivial",
                evidence=OBJECT_INTERFACE_FAILURE_PREFIX + ": probe timed out",
                timeout_s=300,
            )
            body_prompt = _phase2_complete_node_correction_prompt(
                ctx,
                label,
                [],
                [],
                candidate_code="theorem lem_target : True := by trivial",
                evidence=OBJECT_IMPLEMENTATION_FAILURE_PREFIX + ": probe passed",
                timeout_s=300,
            )

        self.assertIn("MAY change the\n  Lean representation", interface_prompt)
        self.assertIn("mathematical source of truth", interface_prompt)
        self.assertIn("interface byte-for-byte", body_prompt)
        self.assertNotIn("MAY change the\n  Lean representation", body_prompt)

    def test_historical_object_timeout_is_bounded_and_classified(self) -> None:
        fixture_path = (
            REPO_ROOT
            / "tests"
            / "fixtures"
            / "phase2_orchestration_replay"
            / "simplex_object_interface_timeout.json"
        )
        fixture = json.loads(fixture_path.read_text(encoding="utf-8"))
        observed = fixture["observed"]
        required = fixture["required_behavior"]

        self.assertEqual(
            required["candidate_object_timeout_seconds"],
            OBJECT_COMPILE_USABILITY_TIMEOUT,
        )
        self.assertGreaterEqual(
            observed["repeated_object_timeout_exposure_seconds"], 3600
        )
        self.assertLess(
            observed["skeleton98"]["complete_proof_plain_seconds"],
            observed["skeleton98"][
                "statement_with_sorry_object_timed_out_after_seconds"
            ],
        )
        self.assertLess(
            observed["skeleton98"]["statement_with_sorry_plain_seconds"],
            observed["skeleton98"][
                "statement_with_sorry_object_timed_out_after_seconds"
            ],
        )
        self.assertEqual(
            required["statement_control_timeout_classification"],
            _phase2_candidate_failure_kind(
                OBJECT_INTERFACE_FAILURE_PREFIX + ": historical replay"
            ),
        )
        self.assertEqual(
            required["proof_control_success_classification"],
            _phase2_candidate_failure_kind(
                OBJECT_IMPLEMENTATION_FAILURE_PREFIX + ": historical replay"
            ),
        )

    def test_phase1_interface_timeout_revises_plan_without_blueprint_repair(self) -> None:
        label = "def:target"
        failed = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module("def def_target : Nat := sorry\n"),
            import_modules=[],
            generation_tier="base",
        )
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            telemetry=FakeTelemetry(),
        )
        evidence = OBJECT_INTERFACE_FAILURE_PREFIX + ": statement control timed out"

        with patch(
            "formalize_blueprint._revise_unusable_interface_plan",
            return_value=True,
        ) as revise, patch(
            "formalize_blueprint._store_generation_candidates"
        ), patch("formalize_blueprint._store_generation_feedback"):
            request = _route_phase1_compile_failure(
                ctx,
                failed,
                evidence,
                "def def_target : Nat := sorry\n",
                layer_no=1,
            )

        revise.assert_called_once_with(ctx, [label], evidence)
        self.assertTrue(request.plan_revision_required)
        self.assertFalse(request.authorizes_blueprint_repair)
        self.assertEqual(request.labels, [label])
        self.assertIn("blueprint is unchanged", str(request))

    def test_plain_phase1_elaboration_timeouts_are_interface_evidence(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "simplex_interface_usability_lifecycle.json"
            ).read_text(encoding="utf-8")
        )

        for field in ("plain_timeout", "heartbeat_timeout"):
            normalized = _phase1_interface_usability_evidence(fixture[field])
            self.assertTrue(normalized.startswith(OBJECT_INTERFACE_FAILURE_PREFIX))
            self.assertIn("already replaced", normalized)
            self.assertIn("does not authorize blueprint decomposition", normalized)

        malformed = "unexpected token ':'; expected ')'"
        self.assertEqual(_phase1_interface_usability_evidence(malformed), "")

    def test_interface_usability_lifecycle_is_bounded_and_non_mutating(self) -> None:
        fixture = json.loads(
            (
                REPO_ROOT
                / "tests"
                / "fixtures"
                / "phase1_orchestration_replay"
                / "simplex_interface_usability_lifecycle.json"
            ).read_text(encoding="utf-8")
        )
        label = fixture["label"]
        code = f"def {_lean_name(label)} : Nat := sorry\n"
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: fixture["statement_fp"]},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "statement_fp": fixture["statement_fp"],
                    "target_signature": f"def {_lean_name(label)} : Nat",
                    "helpers": [],
                    "decisions": [],
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_candidates={},
            generation_feedback={},
            diagnostic_evidence={},
            retry_lifecycle={},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            phase1_exchange_history={},
            model_resume_sessions={},
            telemetry=FakeTelemetry(),
        )

        def candidate(tier: str) -> Phase1LayerCandidate:
            return Phase1LayerCandidate(
                labels=[label],
                parsed=_parse_module(code),
                import_modules=[],
                generation_tier=tier,
            )

        def activate(_ctx, labels, evidence, **_kwargs):
            _ctx.blueprint_direct_generation[label] = {
                "statement_fp": fixture["statement_fp"],
                "source": "test",
                "evidence": evidence,
            }
            return set(labels)

        with patch(
            "formalize_blueprint._store_generation_candidates"
        ), patch(
            "formalize_blueprint._store_generation_feedback"
        ), patch(
            "formalize_blueprint._revise_unusable_interface_plan",
            return_value=True,
        ) as revise, patch(
            "formalize_blueprint._activate_blueprint_direct_generation",
            side_effect=activate,
        ) as activate_direct:
            first = _route_phase1_compile_failure(
                ctx,
                candidate("base"),
                fixture["plain_timeout"],
                code,
                layer_no=1,
            )
            second = _route_phase1_compile_failure(
                ctx,
                candidate("base"),
                fixture["heartbeat_timeout"],
                code,
                layer_no=1,
            )
            third = _route_phase1_compile_failure(
                ctx,
                candidate("escalation"),
                fixture["heartbeat_timeout"],
                code,
                layer_no=1,
            )

        revise.assert_called_once()
        activate_direct.assert_called_once()
        self.assertTrue(first.plan_revision_required)
        self.assertTrue(second.plan_revision_required)
        self.assertFalse(third.authorizes_blueprint_repair)
        self.assertIsNotNone(third.failure_route)
        self.assertFalse(third.decomposition_helpers)
        self.assertFalse(
            any(
                event == "phase1_compile_exhaustion_decomposition"
                for event, _fields in ctx.telemetry.events
            )
        )

    def test_interface_feedback_permits_bounded_same_node_structure(self) -> None:
        prompt_rule = _phase1_interface_prompt_rule(
            OBJECT_INTERFACE_FAILURE_PREFIX + ": historical timeout"
        )
        self.assertIn("named structural", prompt_rule)
        self.assertIn("same target node", prompt_rule)
        self.assertIn("do not spend time proving anything", prompt_rule)

    def test_interface_usability_evidence_survives_plan_epoch_transition(self) -> None:
        label = "def:target"
        evidence = (
            OBJECT_INTERFACE_FAILURE_PREFIX
            + ": statement control timed out after all bodies were `sorry`"
        )
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            generation_feedback={},
            diagnostic_evidence={},
            generation_candidates={
                label: {
                    "statement_fp": "statement-v1",
                    "code": "def def_target : Nat := sorry\n",
                    "candidate_hash": "candidate-v1",
                }
            },
            phase2_node_candidates={},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_target : Nat",
                    "helpers": [],
                    "decisions": ["old interface"],
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            retry_lifecycle={},
            phase1_exchange_history={},
            quarantined_labels=set(),
            quarantine={},
            local_group_partitions={},
            telemetry=FakeTelemetry(),
            design_plan="",
        )
        _record_diagnostic_evidence(
            ctx,
            label,
            evidence,
            source="phase1_interface_usability_gate",
        )

        ctx.design_plan_entries[label]["decisions"] = ["revised interface"]
        _transition_phase1_generation_epoch(
            ctx,
            [label],
            reason="test_interface_plan_replacement",
        )

        active = _active_diagnostic_evidence(ctx, [label])
        self.assertEqual(len(active), 1)
        self.assertEqual(active[0]["kind"], "operational")
        self.assertEqual(active[0]["lifetime"], "statement")
        self.assertIn(OBJECT_INTERFACE_FAILURE_PREFIX, _generation_feedback_for(ctx, [label]))
        self.assertNotIn(label, ctx.generation_candidates)

    def test_interface_plan_revision_cannot_restamp_failed_candidate(self) -> None:
        label = "def:target"
        code = "def def_target : Nat := sorry\n"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_target : Nat",
                    "helpers": [],
                    "decisions": ["original interface"],
                }
            },
            design_plan_alternates={},
            blueprint_direct_generation={},
            generation_candidates={},
            generation_feedback={},
            retry_lifecycle={},
            telemetry=telemetry,
        )
        producing_fp = _candidate_plan_fingerprint(ctx, label)
        failed = Phase1LayerCandidate(
            labels=[label],
            parsed=_parse_module(code),
            import_modules=[],
            generation_tier="base",
            plan_fps={label: producing_fp},
        )

        def revise_plan(_ctx, labels, _evidence):
            self.assertEqual(labels, [label])
            _ctx.design_plan_entries[label]["decisions"] = ["revised interface"]
            _prune_stale_generation_candidates(_ctx)
            return True

        evidence = OBJECT_INTERFACE_FAILURE_PREFIX + ": statement control timed out"
        with patch(
            "formalize_blueprint._revise_unusable_interface_plan",
            side_effect=revise_plan,
        ):
            request = _route_phase1_compile_failure(
                ctx,
                failed,
                evidence,
                code,
                layer_no=1,
            )

        self.assertTrue(request.plan_revision_required)
        self.assertNotIn(label, ctx.generation_candidates)
        self.assertNotEqual(
            producing_fp, _candidate_plan_fingerprint(ctx, label)
        )

    def test_interface_plan_invalidation_clears_old_candidate_and_retry(self) -> None:
        label = "def:target"
        telemetry = FakeTelemetry()
        ctx = SimpleNamespace(
            nodes={label: node(label)},
            stmt_fps={label: "statement-v1"},
            design_plan_entries={
                label: {
                    "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
                    "target_signature": "def def_target : Nat",
                    "helpers": [],
                    "decisions": ["unusable interface"],
                }
            },
            design_plan_alternates={label: {"target_signature": "alternate"}},
            blueprint_direct_generation={},
            generation_candidates={},
            retry_lifecycle={
                f"phase1_statement:{label}": {
                    "label": label,
                    "stage": "phase1_statement",
                    "statement_fp": "statement-v1",
                    "state": "escalation",
                }
            },
            telemetry=telemetry,
        )
        _store_generation_candidates(
            ctx,
            [label],
            "def def_target : Nat := sorry\n",
            source="phase1_interface_usability_gate",
            lean_status="passed",
        )
        self.assertIn(label, ctx.generation_candidates)

        with patch(
            "formalize_blueprint._correct_phase1_design_plan",
            return_value=False,
        ):
            changed = _revise_unusable_interface_plan(
                ctx,
                [label],
                OBJECT_INTERFACE_FAILURE_PREFIX + ": statement control timed out",
            )

        self.assertTrue(changed)
        self.assertNotIn(label, ctx.design_plan_entries)
        self.assertNotIn(label, ctx.design_plan_alternates)
        self.assertNotIn(label, ctx.generation_candidates)
        self.assertNotIn(f"phase1_statement:{label}", ctx.retry_lifecycle)

    def test_phase1_epoch_transition_owns_all_obsolete_scheduler_state(self) -> None:
        target = "def:target"
        peer = "def:peer"
        ctx = SimpleNamespace(
            nodes={target: node(target), peer: node(peer)},
            stmt_fps={target: "target-v1", peer: "peer-v1"},
            design_plan_entries={},
            blueprint_direct_generation={},
            generation_candidates={
                target: {"component_labels": [target, peer]},
                peer: {"component_labels": [target, peer]},
            },
            generation_feedback={
                target: {"statement_fp": "target-v1", "evidence": "keep me"}
            },
            retry_lifecycle={
                f"phase1_statement:{target}": {
                    "label": target,
                    "stage": "phase1_statement",
                },
                f"phase1_statement:{peer}": {
                    "label": peer,
                    "stage": "phase1_statement",
                },
                f"phase2_body:{target}": {
                    "label": target,
                    "stage": "phase2_body",
                },
            },
            phase1_exchange_history={
                "target-exchange": {"labels": [target]},
                "peer-exchange": {"labels": [peer]},
            },
            quarantined_labels={target},
            quarantine={target: {"statement_fp": "target-v1"}},
            local_group_partitions={
                target: {
                    "partition_id": "partition-1",
                    "group": [target, peer],
                },
                peer: {
                    "partition_id": "partition-1",
                    "group": [target, peer],
                },
            },
            telemetry=FakeTelemetry(),
        )

        _transition_phase1_generation_epoch(
            ctx,
            [target],
            reason="test_plan_replacement",
        )

        self.assertEqual(ctx.generation_candidates, {})
        self.assertNotIn(f"phase1_statement:{target}", ctx.retry_lifecycle)
        self.assertIn(f"phase1_statement:{peer}", ctx.retry_lifecycle)
        self.assertIn(f"phase2_body:{target}", ctx.retry_lifecycle)
        self.assertNotIn("target-exchange", ctx.phase1_exchange_history)
        self.assertIn("peer-exchange", ctx.phase1_exchange_history)
        self.assertNotIn(target, ctx.quarantined_labels)
        self.assertNotIn(target, ctx.quarantine)
        self.assertEqual(ctx.local_group_partitions, {})
        self.assertEqual(
            ctx.generation_feedback[target]["evidence"],
            "keep me",
        )

    def test_module_object_timeout_uses_requested_budget_and_cleans_objects(self) -> None:
        communicate_timeouts: list[int | None] = []

        class TimedOutProcess:
            pid = 1234
            returncode = -9

            def communicate(self, timeout=None):
                communicate_timeouts.append(timeout)
                if timeout is not None:
                    raise subprocess.TimeoutExpired(["lean"], timeout)
                return "", ""

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp).resolve()
            source = root / "AutoBlueprint" / "Generated" / "Test" / "Node.lean"
            source.parent.mkdir(parents=True)
            source.write_text("theorem node : True := by trivial\n", encoding="utf-8")
            sibling = source.with_suffix(".olean")
            build_object = (
                root
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "AutoBlueprint"
                / "Generated"
                / "Test"
                / "Node.olean"
            )
            sibling.write_bytes(b"stale")
            build_object.parent.mkdir(parents=True)
            build_object.write_bytes(b"stale")

            with patch(
                "refine_blueprint_with_lean.REPO_ROOT", root
            ), patch(
                "refine_blueprint_with_lean.subprocess.Popen",
                return_value=TimedOutProcess(),
            ), patch("refine_blueprint_with_lean.os.killpg") as kill_group:
                attempt = _compile_module_olean(
                    source, ["lean"], timeout=7
                )

            self.assertFalse(sibling.exists())
            self.assertFalse(build_object.exists())

        self.assertFalse(attempt.ok)
        self.assertEqual(attempt.kind, "object-timeout")
        self.assertIn("after 7s", attempt.reason)
        self.assertEqual(communicate_timeouts, [7, None])
        kill_group.assert_called_once_with(1234, 9)


if __name__ == "__main__":
    unittest.main()
