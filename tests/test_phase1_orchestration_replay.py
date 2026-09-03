from __future__ import annotations

import json
import re
import sys
import unittest
from datetime import datetime
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
FIXTURE_DIR = REPO_ROOT / "tests" / "fixtures" / "phase1_orchestration_replay"
PHASE2_FIXTURE_DIR = REPO_ROOT / "tests" / "fixtures" / "phase2_orchestration_replay"
sys.path.insert(0, str(REPO_ROOT / "scripts"))

from formalize_blueprint import (  # noqa: E402
    DesignPlanCandidate,
    _initial_plan_repair_costs,
)


def _fixture(name: str) -> dict:
    return json.loads((FIXTURE_DIR / name).read_text(encoding="utf-8"))


def _phase2_fixture(name: str) -> dict:
    return json.loads((PHASE2_FIXTURE_DIR / name).read_text(encoding="utf-8"))


def _first_compiling_sample(case: dict) -> int | None:
    for index, attempt in enumerate(case["attempts"], 1):
        if attempt["lean_status"] == "passed":
            return index
    return None


class PhaseOneOrchestrationReplayTests(unittest.TestCase):
    """Protect retry/scheduling decisions with portable historical evidence."""

    def test_historical_corrections_require_up_to_three_stochastic_samples(self) -> None:
        cases = _fixture("correction_sampling.json")["cases"]
        successful = [case for case in cases if _first_compiling_sample(case)]

        self.assertTrue(any(_first_compiling_sample(case) == 2 for case in successful))
        self.assertTrue(any(_first_compiling_sample(case) == 3 for case in successful))
        self.assertEqual(max(_first_compiling_sample(case) for case in successful), 3)

    def test_sampling_fixture_uses_complete_content_hashes(self) -> None:
        cases = _fixture("correction_sampling.json")["cases"]
        digest = re.compile(r"[0-9a-f]{64}")

        for case in cases:
            hashes = [
                case["statement_sha256"],
                case["plan_sha256"],
                case["prompt_sha256"],
            ]
            hashes.extend(attempt["response_sha256"] for attempt in case["attempts"])
            hashes.extend(attempt["candidate_sha256"] for attempt in case["attempts"])
            with self.subTest(run=case["run_id"], label=case["label"]):
                self.assertTrue(all(digest.fullmatch(value) for value in hashes))

    def test_three_sample_cap_preserves_success_and_stops_current_repeat(self) -> None:
        cases = _fixture("correction_sampling.json")["cases"]
        cap = 3

        for case in cases:
            first_success = _first_compiling_sample(case)
            if first_success is not None:
                with self.subTest(run=case["run_id"], label=case["label"]):
                    self.assertLessEqual(first_success, cap)

        current = next(
            case
            for case in cases
            if case["run_id"] == "20260731-052052"
            and case["label"] == "lem:claim6"
        )
        self.assertEqual(len(current["attempts"]), 6)
        self.assertEqual(len(current["attempts"][cap:]), 3)
        self.assertNotEqual(
            current["prompt_sha256"],
            current["next_distinct_prompt"]["prompt_sha256"],
        )
        self.assertEqual(current["next_distinct_prompt"]["lean_status"], "passed")

    def test_streaming_can_overlap_compile_without_splitting_final_audit(self) -> None:
        case = _fixture("streaming_transactions.json")["cases"][0]
        generated = datetime.fromisoformat(case["fast_candidate_generated"])
        generation_barrier = datetime.fromisoformat(case["all_generation_settled"])
        compiled = datetime.fromisoformat(case["fast_candidate_compiled"])

        blocked_seconds = (generation_barrier - generated).total_seconds()
        compile_seconds = (compiled - generation_barrier).total_seconds()
        self.assertEqual(blocked_seconds, 477)
        self.assertEqual(compile_seconds, 46)
        self.assertGreater(blocked_seconds, compile_seconds)
        self.assertEqual(case["final_audit_calls"], 1)

    def test_lean_rejection_cannot_repeat_without_a_revision_call(self) -> None:
        case = _fixture("compile_reuse_loop.json")["cases"][0]

        self.assertEqual(case["repeated_candidate_sha256_count"], 91)
        self.assertEqual(case["model_calls_during_repeated_retries"], 0)
        self.assertEqual(case["incorrectly_consumed_repair_trials"], 91)
        self.assertEqual(case["expected_zero_call_reuses_after_lean_failure"], 0)
        self.assertEqual(case["expected_next_action"], "model_revision")

    def test_semantically_rejected_candidate_cannot_dominate_revision(self) -> None:
        case = _fixture("semantic_candidate_dominance.json")["cases"][0]

        self.assertEqual(case["retained_lean_status"], "passed")
        self.assertEqual(case["retained_semantic_status"], "rejected")
        self.assertEqual(case["distinct_revision_lean_status"], "passed")
        self.assertNotEqual(
            case["retained_candidate_sha256"],
            case["distinct_revision_sha256"],
        )
        self.assertEqual(case["recorded_transition"], "no_measurable_progress")
        self.assertEqual(
            case["expected_transition"], "semantic_rejection_revision"
        )

    def test_repaired_blueprint_is_audited_before_lean_generation(self) -> None:
        case = _fixture("post_repair_boundary.json")["cases"][0]

        self.assertEqual(case["changed_contract_count"], 5)
        self.assertEqual(case["model_calls_before_missing_edge_was_discovered"], 7)
        self.assertEqual(case["elapsed_before_missing_edge_was_discovered_s"], 324)
        self.assertEqual(
            case["expected_first_post_repair_model_purpose"],
            "post_repair_blueprint_audit",
        )
        self.assertEqual(case["expected_lean_generation_calls_before_boundary"], 0)
        self.assertEqual(case["expected_route"], "dependency-edge-repair")

    def test_completed_boundary_edge_cannot_reauthorize_model_repair(self) -> None:
        case = _fixture("post_repair_boundary.json")["cases"][1]

        self.assertEqual(case["boundary_repair_labels"], [])
        self.assertEqual(case["observed_repeated_blueprint_repair_calls"], 6)
        self.assertGreater(case["observed_repeated_model_seconds"], 519)
        self.assertEqual(case["expected_repeated_blueprint_repair_calls"], 0)
        self.assertEqual(case["expected_next_action_after_edge"], "resume_phase1")
        self.assertEqual(case["expected_additional_boundary_audits_after_edge"], 0)

    def test_compound_repair_scope_keeps_deterministic_and_model_work_separate(self) -> None:
        case = _fixture("post_repair_boundary.json")["cases"][2]

        self.assertEqual(case["run_id"], "20260803-003136")
        self.assertIn(
            case["observed_false_scope_violation"],
            case["deterministic_changed_labels"],
        )
        self.assertNotIn(
            case["observed_false_scope_violation"],
            case["model_changed_labels"],
        )
        self.assertEqual(
            set(case["expected_scope_checked_labels"]),
            set(case["model_changed_labels"]),
        )
        self.assertEqual(case["expected_scope_violations"], [])
        self.assertEqual(
            set(case["observed_scope_checked_labels"]),
            set(case["model_changed_labels"])
            | set(case["deterministic_changed_labels"]),
        )
        self.assertEqual(case["observed_result"], "scope_rolled_back")
        self.assertEqual(
            set(case["expected_committed_labels"]),
            set(case["deterministic_changed_labels"])
            | set(case["model_changed_labels"]),
        )

    def test_statement_dependency_evidence_routes_before_generation_retry(self) -> None:
        case = _fixture("immediate_dependency_edge.json")["cases"][0]

        self.assertEqual(case["reported_classification"], "lean_translation_issue")
        self.assertEqual(case["routed_kind"], "lean-generation")
        self.assertFalse(case["blueprint_repair_authorized"])
        self.assertTrue(case["required_dependencies"])
        self.assertEqual(case["model_calls_before_edge_application"], 11)
        self.assertGreater(case["model_seconds_before_edge_application"], 275)
        self.assertEqual(case["expected_model_calls_before_edge_application"], 0)
        self.assertEqual(
            case["expected_outer_route"], "dependency-edge-repair"
        )

    def test_structured_statement_audit_classification_is_authoritative(self) -> None:
        case = _fixture("structured_statement_audit_routing.json")

        self.assertEqual(
            case["audit_response"]["classification"],
            "lean_translation_issue",
        )
        self.assertEqual(
            set(case["observed_before_fix"]["routed_kinds"].values()),
            {"decomposition", "lean-generation"},
        )
        self.assertTrue(case["observed_before_fix"]["blueprint_repair_authorized"])
        self.assertEqual(
            case["expected_after_fix"]["routed_kind"], "lean-generation"
        )
        self.assertFalse(
            case["expected_after_fix"]["blueprint_repair_authorized"]
        )
        for issue in case["audit_response"]["issues"]:
            self.assertEqual(issue["classification"], "lean_translation_issue")
            self.assertEqual(issue["failure_origin"], "plan")
            self.assertTrue(issue["required_dependencies"])
            self.assertTrue(issue["missing_plan_requirements"])
            self.assertEqual(issue["missing_helpers"], [])
            self.assertEqual(issue["missing_blueprint_information"], [])

    def test_semantic_plan_defects_route_before_stale_plan_generation(self) -> None:
        cases = _fixture("semantic_origin_serialization.json")["cases"]

        self.assertEqual(len(cases), 3)
        self.assertGreater(sum(case["serialized_delay_s"] for case in cases), 1200)
        for case in cases:
            with self.subTest(run=case["run_id"], label=case["label"]):
                self.assertEqual(case["observed_route"], "lean-generation")
                self.assertIn(
                    case["expected_failure_origin"], {"plan", "both"}
                )
                self.assertEqual(
                    case["expected_first_route"], "plan-revision"
                )
                self.assertEqual(
                    case["expected_stale_plan_generation_retries"], 0
                )

    def test_exhausted_frontier_plan_cannot_consume_no_work_retries(self) -> None:
        case = _fixture("frontier_gateway_exhaustion.json")

        self.assertEqual(case["run_id"], "20260801-014205")
        self.assertEqual(case["no_work_retries"], 98)
        self.assertLessEqual(
            case["last_retry_at_s"] - case["first_rejection_at_s"], 2
        )
        self.assertEqual(
            case["required_transition"],
            "invalidate exhausted frontier plan entry and request fresh scoped planning",
        )

    def test_mixed_plan_audit_does_not_widen_blueprint_repair(self) -> None:
        case = _fixture("mixed_plan_audit_routing.json")

        self.assertEqual(case["run_id"], "20260801-022052")
        self.assertNotEqual(
            case["observed_incorrect_blueprint_repair_labels"],
            case["expected_blueprint_repair_labels"],
        )
        self.assertEqual(
            case["expected_blueprint_repair_labels"],
            ["def:security-parameter-negligible"],
        )
        self.assertEqual(
            case["expected_plan_correction_labels"], ["def:channel-povm"]
        )

    def test_parallel_retry_state_fixture_preserves_the_race_boundary(self) -> None:
        case = _fixture("parallel_retry_state.json")

        self.assertEqual(case["source_run"], "20260801-041251")
        self.assertEqual(
            case["configured_workers"], case["simultaneous_generation_calls"]
        )
        self.assertGreater(case["next_generation_call_s"], case["wave_started_s"])
        self.assertEqual(
            set(case["shared_state"]),
            {"generation_candidates", "generation_feedback"},
        )
        self.assertEqual(len(case["required_invariants"]), 3)

    def test_empty_tournament_recovery_is_not_serialized_after_timeout(self) -> None:
        case = _fixture("empty_tournament_serial_fallback.json")

        observed_recovery_path = (
            case["serial_missing_tail_finished_s"]
            - case["candidate_a_second_empty_s"]
        )
        overlapped_recovery_path = (
            case["expected_overlapped_complete_s"]
            - case["expected_overlapped_recovery_start_s"]
        )
        self.assertEqual(case["expected_overlapped_recovery_start_s"], 35)
        self.assertGreaterEqual(
            observed_recovery_path - overlapped_recovery_path,
            case["minimum_saved_critical_path_s"],
        )

    def test_catastrophic_tournament_fixture_requires_full_restart(self) -> None:
        case = _fixture("catastrophic_tournament_admission.json")
        observed = case["candidates"]["A"]
        labels = [f"node-{index}" for index in range(case["node_count"])]
        findings = {label: [] for label in labels}
        for index in range(observed["score"][2]):
            findings[labels[index % len(labels)]].append(f"finding-{index}")
        candidate = DesignPlanCandidate(
            candidate_id="A",
            entries={label: {} for label in labels},
            missing=[],
            findings=findings,
            blocked=set(labels),
            components=[labels[:18], labels[18:35], labels[35:]],
        )
        repair_work, tournament_work = _initial_plan_repair_costs(
            candidate, case["node_count"]
        )

        self.assertEqual(case["source_run"], "20260801-083320")
        self.assertEqual(
            case["candidates"]["A"]["blocked_initial_frontier"],
            len(case["initial_frontier"]),
        )
        self.assertEqual(case["candidates"]["B"]["status"], "timeout")
        self.assertFalse(case["required_behavior"]["admit_degraded_plan"])
        self.assertTrue(
            case["required_behavior"]["restart_complete_tournament"]
        )
        self.assertFalse(
            case["required_behavior"]["authorize_blueprint_edit"]
        )
        self.assertGreaterEqual(repair_work, tournament_work)

    def test_near_good_tournament_fixture_prefers_scoped_repair(self) -> None:
        case = _fixture("repairable_tournament_admission.json")
        observed = case["candidate"]
        labels = [f"node-{index}" for index in range(case["node_count"])]
        blocked = set(labels[: observed["blocked_contracts"]])
        candidate = DesignPlanCandidate(
            candidate_id=observed["id"],
            entries={label: {} for label in labels},
            missing=[],
            findings={
                label: [f"finding for {label}"]
                for label in blocked
            },
            blocked=blocked,
            components=[[label] for label in blocked],
        )

        repair_work, tournament_work = _initial_plan_repair_costs(
            candidate, case["node_count"]
        )

        self.assertEqual(case["source_run"], "20260801-180629")
        self.assertEqual(
            (repair_work, tournament_work),
            (
                case["cost_model"]["repair_work"],
                case["cost_model"]["full_tournament_work"],
            ),
        )
        self.assertLess(repair_work, tournament_work)
        self.assertTrue(
            case["required_behavior"]["admit_for_scoped_repair"]
        )
        self.assertFalse(
            case["required_behavior"]["restart_complete_tournament"]
        )

    def test_repeated_plan_semantic_fixture_records_bounded_lifecycle(self) -> None:
        case = _fixture("repeated_plan_semantic_exhaustion.json")

        self.assertEqual(case["source_run"], "20260801-054159")
        self.assertEqual(case["label"], "def:finite-register-operators")
        self.assertEqual(len(case["observed_events"]), 3)
        self.assertEqual(
            case["maximum_plan_corrections_for_statement_fingerprint"], 1
        )
        self.assertEqual(
            case["required_lifecycle"],
            [
                "correct_interface_plan_once",
                "generate_from_blueprint_after_corrected_plan_exhausts",
                "decompose_only_after_blueprint_direct_generation_exhausts",
            ],
        )

    def test_invalid_patch_import_is_removed_at_the_merge_boundary(self) -> None:
        case = _fixture("invalid_patch_import.json")

        self.assertEqual(case["source_run"], "20260801-070856")
        self.assertEqual(
            case["invalid_import"], "import Mathlib.Data.Polynomial.Basic"
        )
        self.assertEqual(case["detector_result"], "unavailable")
        self.assertEqual(
            case["required_boundary"],
            "filter unavailable imports from the final merged ParsedModule",
        )
        self.assertEqual(case["expected_repair_trials_consumed"], 0)

    def test_planned_member_shadowing_fixture_preserves_local_binding(self) -> None:
        case = _fixture("planned_member_shadowing.json")

        self.assertEqual(case["source_run"], "20260801-074355")
        self.assertEqual(case["label"], "def:positive-loewner-density")
        self.assertGreaterEqual(case["outer_retries_observed"], 4)
        self.assertEqual(case["shadowed_member"], "DensityOperator")
        self.assertEqual(
            case["required_invariant"],
            "planned structure and class members shadow bare global helper aliases throughout their declaration body",
        )
        self.assertTrue(case["downstream_alias_resolution_must_remain_enabled"])

    def test_candidate_contract_refresh_fixture_requires_one_retry_lifecycle(self) -> None:
        case = _fixture("candidate_contract_refresh_lifecycle.json")

        self.assertEqual(case["source_run"], "20260825-194345")
        self.assertEqual(
            case["observed_before_fix"]["typed_contract_realized_epoch_transitions"],
            282,
        )
        self.assertEqual(
            case["observed_before_fix"]["claim5_component_transitions"], 21
        )
        self.assertEqual(
            set(case["observed_before_fix"]["claim5_observed_retry_failure_counts"]),
            {1},
        )
        self.assertFalse(case["observed_before_fix"]["claim5_reached_exhaustion"])
        self.assertTrue(case["required_behavior"]["preserve_retry_lifecycle"])
        self.assertTrue(case["required_behavior"]["preserve_generation_candidate"])

    def test_theorem_like_contract_poisoning_fixture_cannot_burn_outer_budget(self) -> None:
        case = _fixture("theorem_like_contract_poisoning.json")

        self.assertEqual(case["source_run"], "20260827-131622")
        self.assertEqual(case["label"], "prop:dyadic-weights")
        self.assertEqual(
            case["observed_before_fix"]["zero_model_call_retries"], 68
        )
        self.assertLessEqual(
            case["observed_before_fix"]["zero_model_call_elapsed_seconds"],
            10,
        )
        self.assertTrue(
            case["observed_before_fix"][
                "candidate_rewrote_authoritative_contract_before_rejection"
            ]
        )
        self.assertTrue(
            case["required_behavior"]["bare_prop_contract_rejected"]
        )
        self.assertFalse(
            case["required_behavior"]["rejected_candidate_may_refresh_contract"]
        )
        self.assertEqual(
            case["required_behavior"][
                "additional_outer_retries_without_model_or_state_progress"
            ],
            0,
        )

    def test_phase2_invalidation_fixture_is_graph_scoped_not_file_scoped(self) -> None:
        case = _phase2_fixture("graph_scoped_invalidation.json")

        self.assertEqual(case["source_run"], "20260825-194345")
        self.assertEqual(
            case["dependency_graph_descendants"],
            case["changed_labels"],
        )
        discarded = set(
            case["observed_before_fix"][
                "discarded_only_because_they_followed_the_edit_in_file_order"
            ]
        )
        self.assertTrue(discarded)
        self.assertTrue(
            discarded.issubset(set(case["expected_after_fix"]["retained_labels"]))
        )
        self.assertEqual(
            case["expected_after_fix"]["retained_source_lean_returncode"], 0
        )
        self.assertTrue(
            case["expected_after_fix"][
                "recheck_labels_do_not_gain_blueprint_helper_authority"
            ]
        )


if __name__ == "__main__":
    unittest.main()
