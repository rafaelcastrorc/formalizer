#!/usr/bin/env python3
"""Statements-first Lean formalization pipeline.

This is the fast successor to ``refine_blueprint_with_lean.py``. The blueprint
remains the only mathematical source of truth and Lean remains the critic; what
changes is *when* model calls happen and how much each one is asked to do:

Fixed traversal policy. Phase 1 freezes statements bottom-up from dependency
leaves toward public results. Phase 2 fills deferred bodies top-down from public
results toward supporting declarations. Phase 1 parallelizes independent groups
and routed fragments; Phase 2 parallelizes independent nodes within each
root-first wave.

Phase 1 (statements and interfaces). Traverse the existing blueprint dependency
graph bottom-up and freeze exact Lean statements and interfaces corresponding
one-to-one with the blueprint. A bounded pair of concurrent root-first planning
calls records compact per-node contract decisions. Their mechanically coherent
provider-consumer components are selected and merged before generation; the
alternate is retained as a zero-call fallback. Planning does not generate Lean
or change traversal. Entries are statement-fingerprinted, persisted, and
selectively invalidated by repairs.
All compilation-driven interface correction, deterministic coverage checking,
statement alignment, and any required blueprint repair happen here. Bottom-up
sections remain in-memory candidates while deterministic checks run, compile
in parallel, and then receive the authoritative statement audit. Rejected
declarations alone are corrected and re-audited; accepted siblings keep their
exact text. The final import gate re-audits only declarations (or owned helpers)
changed by compiler feedback.
A Phase-1 candidate may contain only its blueprint targets and exact
plan-owned structure/inductive/class interfaces. Executable helper definitions
or theorems are implementation work and are rejected before compilation.
A contract is frozen only after those checks pass. Later phases may replace ``sorry``
bodies but cannot silently edit an accepted statement.

Model-output boundary. Every Lean response is canonicalized into declarations
before it reaches state: the pipeline owns imports/preamble/module layout,
normalizes theorem-like commands, rejects duplicate names, gives local helpers
stable node-owned global names, and records ownership. Raw model files are never
persisted or merged directly.

Phase 2 (implementations). Follow a top-down traversal across every deferred
body: theorem proofs and ``def``/``abbrev`` implementations. Higher proofs are
therefore checked first against the complete frozen Phase-1 interface; filling
a lower theorem body later does not alter that interface. Completed definition
bodies receive a semantic blueprint audit before acceptance. For every frozen
``sorry``:
1. a deterministic tactic ladder (``rfl``/``omega``/``norm_num``/``ring``/
   ``simp``/``aesop``) runs first, with zero model cost;
2. survivors are filled by batched model calls;
3. the residue is sent to singleton calls through the configured escalation runner;
4. persistent failures become *evidence* for a bounded blueprint repair.

Phase ownership is one-way. A Phase-2 repair may add a helper node or change a
statement contract. Phase 2 regenerates each affected blueprint node as one
complete Lean declaration containing both its current statement and body. The
complete declaration passes deterministic, Lean, and alignment gates together;
there is no statement-only repair followed by another proof call. Phase 2 does
not return to Phase 1 or make the completed initial-skeleton milestone regress.

Timeouts are treated as latency, never as mathematical difficulty: a timed-out
call is bisected before any singleton uses the escalation runner. Only real Lean/audit output (or
an explicit NEEDS-DECOMPOSITION refusal) can trigger a blueprint repair, and
repairs regenerate changed full-node contracts. Unchanged descendants are
deferred, rebound to the repaired modules, and deterministically recompiled;
only failed rechecks return to model generation. Proof-sketch edits therefore
still recheck the Lean that is supposed to certify them.

Published output is unchanged in meaning: ``formalization.lean`` contains no
``sorry``, passes the strict correctness audit and a from-scratch Lean check,
and has a 1-1 statement correspondence with the blueprint. ``sorry`` exists
only inside the internal scratch skeleton, which is never published.
"""
from __future__ import annotations

import argparse
import copy
import concurrent.futures
import contextlib
import hashlib
import json
import os
import re
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time
import traceback
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterable, Mapping

from generate_blueprint import _extract_json, read_paper
from lean_preflight import check_lean_environment
from model_runners import RunnerError, get_runner
from model_runners.api import choose_model, list_anthropic_model_ids, list_openai_model_ids
from model_runners.base import is_environment_error, is_transient_error
from model_runners.cli import choose_codex_base_model, choose_codex_escalation_model, list_codex_model_ids
from refine_blueprint_with_lean import (
    LEAN_IDIOM_CHEATSHEET,
    FORBIDDEN_ASSUMPTIONS,
    FORBIDDEN_BLUEPRINT_STUBS,
    LeanAttempt,
    PLACEHOLDER_NAME_RE,
    TeeStream,
    _alignment_failure_kind,
    _authorized_alignment_failure_kind,
    _blueprint_library_preference,
    _compile_module_olean,
    _compose_lean_file,
    _decomposition_note,
    _default_lean_command,
    _dependency_closure,
    _dependency_descendants,
    _deterministic_statement_audit,
    _extract_lean_code,
    _generated_module_dir,
    _is_timeout_error,
    _lean_declarations,
    _lean_env,
    _lean_name,
    _library_roots,
    _missing_olean_imports,
    _module_safe_name,
    _node_order,
    _node_summary,
    _node_tex_blocks,
    _nonmathlib_uses_missing_from_decl,
    _parse_decomposition_refusal,
    _publish_lean_text,
    _repair_unknown_universe_levels,
    _rebuild_site_for,
    _run_lean,
    _run_log_path,
    _rg_library_candidates,
    _search_local_lean_libraries,
    _search_terms_from_blueprint,
    _statement_audit_prompt,
    _write_report,
)
from telemetry import TelemetryRun, node_structural_features
from validate_blueprint import Node, print_result, validate_blueprint

# The pipeline's source is organized into part files (constants, grouped
# utilities, and one file per phase) but executes as this single module:
# each part is compiled and executed into this module's namespace, in
# order. This preserves the monolith's runtime semantics exactly - every
# function still resolves collaborators through formalize_blueprint's
# globals, so tests patching `formalize_blueprint.<name>` and tools
# importing private helpers keep working unchanged. Definition order
# across parts is checked mechanically; see organize.md for the layout.
_PART_FILES = (
    "Utils/Constants.py",
    "Utils/Logging.py",
    "Utils/Types.py",
    "Utils/Graph.py",
    "Utils/LeanSource.py",
    "Utils/LeanCheck.py",
    "Utils/Audits.py",
    "Utils/FailureRouting.py",
    "Utils/Transactions.py",
    "Utils/Draft.py",
    "Utils/Evidence.py",
    "Utils/Exchange.py",
    "Utils/Candidates.py",
    "Utils/ModelCalls.py",
    "Utils/Sections.py",
    "Utils/StateIO.py",
    "Utils/Prompts.py",
    "phase1.py",
    "phase2.py",
    "Utils/BlueprintRepair.py",
    "Utils/Reporting.py",
)
_PARTS_DIR = Path(__file__).resolve().parent
for _part_file in _PART_FILES:
    _part_path = _PARTS_DIR / _part_file
    exec(compile(_part_path.read_text(encoding="utf-8"), str(_part_path), "exec"))
del _part_file, _part_path


# ---------------------------------------------------------------------------
# Main


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("name", help="Existing blueprint name under blueprints/<name>/")
    parser.add_argument(
        "--runner",
        help=(
            "Base runner spec for batched skeleton/proof calls. If omitted, "
            "uses a cheap API runner when OPENAI_API_KEY or ANTHROPIC_API_KEY "
            "is set, otherwise falls back to local Codex."
        ),
    )
    parser.add_argument(
        "--escalation-runner",
        help="Runner spec for escalated singleton/repair calls (default: same as --runner)",
    )
    parser.add_argument(
        "--planner-tier",
        choices=("base", "escalation"),
        default="escalation",
        help=(
            "Model tier for the compact Phase-1 semantic planner: use "
            "--runner (base) or --escalation-runner (default)"
        ),
    )
    parser.add_argument("--paper", help="Optional original paper path/URL/text")
    parser.add_argument(
        "--max-trials",
        type=int,
        default=100,
        help="Shared outer repair/retry budget",
    )
    parser.add_argument("--timeout", type=int, default=300, help="Base per-model-call timeout (s)")
    parser.add_argument("--hard-timeout", type=int, default=600, help="Escalated per-call timeout (s)")
    parser.add_argument("--section-size", type=int, default=DEFAULT_SECTION_SIZE)
    parser.add_argument("--proof-batch-size", type=int, default=DEFAULT_PROOF_BATCH)
    parser.add_argument(
        "--conjecture-policy",
        choices=("record", "attempt"),
        default="record",
        help=(
            "Record conjectures as exact open propositions (default), or first "
            "add blueprint proofs and then attempt to formalize them"
        ),
    )
    parser.add_argument(
        "--workers",
        type=int,
        default=DEFAULT_WORKERS,
        help=(
            "Parallel Phase-2 body workers and bottom-up Phase-1 independent "
            "group/fragment workers"
        ),
    )
    parser.add_argument(
        "--reasoning-effort",
        choices=("low", "medium", "high", "xhigh"),
        default="medium",
        help="Codex reasoning effort for batched calls (escalations use --escalation-effort)",
    )
    parser.add_argument(
        "--escalation-effort",
        choices=("low", "medium", "high", "xhigh"),
        default="high",
    )
    resume_group = parser.add_mutually_exclusive_group()
    resume_group.add_argument(
        "--continue",
        dest="resume_mode",
        action="store_const",
        const="latest",
        default="latest",
        help="Reuse compatible frozen statements and accepted proofs (default)",
    )
    resume_group.add_argument(
        "--continue-phase1",
        dest="resume_mode",
        action="store_const",
        const="phase1",
        help=(
            "Discard later unpublished Phase 2 changes and restart from the "
            "immutable snapshot saved when Phase 1 completed"
        ),
    )
    resume_group.add_argument(
        "--fresh",
        dest="resume_mode",
        action="store_const",
        const="fresh",
        help="Discard generated fast-pipeline state and start from scratch",
    )
    parser.add_argument("--no-ladder", dest="ladder", action="store_false", help="Skip the free tactic ladder")
    parser.add_argument("--no-build", dest="build", action="store_false", help="Skip the site rebuild")
    parser.add_argument("--lean-command", help="Override checker command, e.g. 'lake env lean'")
    args = parser.parse_args(argv)
    args.continue_run = args.resume_mode != "fresh"
    default_runner, default_escalation_runner = _default_fast_runner_specs()
    runner = args.runner or default_runner
    escalation_runner = args.escalation_runner or (runner if args.runner else default_escalation_runner)

    if args.max_trials < 1:
        raise SystemExit("--max-trials must be at least 1")
    if args.hard_timeout < args.timeout:
        raise SystemExit("--hard-timeout must be at least --timeout")

    telemetry = TelemetryRun(
        REPO_ROOT,
        blueprint=args.name,
        command=[sys.argv[0], *(argv or sys.argv[1:])],
    )
    telemetry.record(
        "formalize_config",
        runner=runner,
        escalation_runner=escalation_runner,
        planner_tier=args.planner_tier,
        planner_runner=(
            escalation_runner if args.planner_tier == "escalation" else runner
        ),
        runner_was_auto=args.runner is None,
        escalation_runner_was_auto=args.escalation_runner is None,
        max_trials=args.max_trials,
        timeout_s=args.timeout,
        hard_timeout_s=args.hard_timeout,
        section_size=args.section_size,
        proof_batch=args.proof_batch_size,
        workers=args.workers,
        proof_order=PHASE2_PROOF_ORDER,
        phase1_order=PHASE1_STATEMENT_ORDER,
        phase2_order=PHASE2_PROOF_ORDER,
        phase1_validation_order="validated-contract_compile_final-audit",
        conjecture_policy=args.conjecture_policy,
        base_effort=args.reasoning_effort,
        escalation_effort=args.escalation_effort,
        continue_run=args.continue_run,
        resume_mode=args.resume_mode,
        ladder=args.ladder,
    )

    def finish(code: int, status: str, **fields) -> int:
        telemetry.record("run_end", exit_code=code, status=status, **fields)
        telemetry.flush_upload_queue()
        return code

    paper_text = ""
    if args.paper:
        print(f"==> Reading paper context from {args.paper}", flush=True)
        paper_text, _source = read_paper(args.paper)

    lean_command = shlex.split(args.lean_command) if args.lean_command else _default_lean_command()
    print("==> Checking Lean/Lake/Mathlib setup", flush=True)
    preflight = check_lean_environment(REPO_ROOT, lean_command=lean_command)
    if not preflight.ok:
        raise FileNotFoundError(
            f"{preflight.message}\n{(preflight.stderr or preflight.stdout).strip()}"
        )
    print(f"  {preflight.message} ({preflight.elapsed_s:.1f}s)", flush=True)

    if args.resume_mode == "phase1":
        _restore_phase1_checkpoint(args.name)

    prior_draft = _draft_blueprint_dir(args.name)
    draft_was_resumed = bool(
        args.continue_run
        and (prior_draft / "blueprint" / "src" / "content.tex").is_file()
    )
    discarded_prior_draft = bool(not args.continue_run and prior_draft.exists())
    blueprint_dir = _prepare_blueprint_draft(
        args.name, continue_run=args.continue_run
    )
    restored_interrupted_repair = (
        _restore_interrupted_phase2_repair(args.name, blueprint_dir)
        if args.continue_run
        else ""
    )
    if restored_interrupted_repair:
        _log(
            "==> Restored the pre-edit Phase 2 blueprint transaction after "
            "an interrupted repair call"
        )
    draft_content_path = blueprint_dir / "blueprint" / "src" / "content.tex"
    telemetry.record(
        "blueprint_draft_ready",
        mode="resumed" if draft_was_resumed else "created_from_published",
        discarded_prior_draft=discarded_prior_draft,
        restored_interrupted_phase2_repair=restored_interrupted_repair,
        draft=str(draft_content_path.relative_to(REPO_ROOT)),
        draft_sha256=hashlib.sha256(draft_content_path.read_bytes()).hexdigest(),
    )
    validation = validate_blueprint(
        REPO_ROOT, args.name, blueprint_dir=blueprint_dir
    )
    print_result(validation)
    if not validation.ok:
        return finish(1, "blueprint_validation_failed")
    _record_proof_graph_telemetry(
        telemetry,
        validation.nodes,
        proof_order=PHASE2_PROOF_ORDER,
        reason="initial",
    )

    blueprint_source = _read_blueprint_source_at(args.name, blueprint_dir)
    print("==> Searching local Lean libraries once for this run", flush=True)
    library_context, library_candidates = _search_local_lean_libraries(
        args.name, validation.nodes, blueprint_source, term_runner=None
    )

    ctx = Ctx(
        name=args.name,
        blueprint_dir=blueprint_dir,
        runner_spec=runner,
        escalation_runner_spec=escalation_runner,
        base_effort=args.reasoning_effort,
        escalation_effort=args.escalation_effort,
        base_timeout=args.timeout,
        hard_timeout=args.hard_timeout,
        lean_command=lean_command,
        telemetry=telemetry,
        paper_text=paper_text,
        library_context=library_context,
        library_candidates=list(library_candidates),
        section_size=args.section_size,
        proof_batch=args.proof_batch_size,
        workers=args.workers,
        use_ladder=args.ladder,
        planner_tier=args.planner_tier,
        conjecture_policy=args.conjecture_policy,
        refinement_order=PHASE1_STATEMENT_ORDER,
    )
    ctx.refresh_nodes(validation.nodes)

    generated_dir = _generated_module_dir(args.name)
    if not args.continue_run:
        # Fresh run: clear skeleton modules from previous runs (old ChunkNN
        # files from the legacy pipeline are cleared too; the two pipelines do
        # not share caches).
        if generated_dir.exists():
            shutil.rmtree(generated_dir)
        lake_generated_dir = _generated_lake_module_dir(args.name)
        if lake_generated_dir.exists():
            shutil.rmtree(lake_generated_dir)
        with contextlib.suppress(FileNotFoundError, OSError):
            _state_path(args.name).unlink()
        shutil.rmtree(
            SCRATCH_DIR / args.name / "phase2-repair-transactions",
            ignore_errors=True,
        )
        shutil.rmtree(_phase1_checkpoint_dir(args.name), ignore_errors=True)

    sections: list[Section] = _load_state(ctx, lean_command) if args.continue_run else []
    _prune_stale_generated(ctx, sections)
    active_repair = getattr(ctx, "phase2_repair_active", {}) or {}
    active_repair_id = str(active_repair.get("request_id") or "")
    if (
        args.continue_run
        and active_repair_id
        and not (
            _phase2_repair_transaction_dir(args.name, active_repair_id)
            / "manifest.json"
        ).is_file()
    ):
        # State written before durable repair snapshots existed cannot recover
        # the graph preceding its already-staged edit. Treat the exact resumed
        # state as a one-time migration baseline so no later verification
        # failure can accumulate another unverified helper component.
        _save_ctx_state(ctx, sections)
        _begin_phase2_repair_transaction(ctx, active_repair_id)
        _record(
            ctx.telemetry,
            "phase2_repair_transaction_legacy_baseline",
            request_id=active_repair_id,
            stage=str(active_repair.get("stage") or "repair"),
            labels=list(active_repair.get("labels") or []),
        )
        _log(
            "==> Established a durable rollback point for a Phase 2 repair "
            "resumed from pre-transaction state"
        )
    report_lines = [
        f"# Statements-First Formalization: `{args.name}`",
        "",
        f"- base runner: `{runner}` (effort `{args.reasoning_effort}`)",
        f"- escalation runner: `{escalation_runner}` (effort `{args.escalation_effort}`)",
        f"- compact semantic planner: `{args.planner_tier}` tier "
        f"(`{escalation_runner if args.planner_tier == 'escalation' else runner}`)",
        f"- timeouts: `{args.timeout}s` base / `{args.hard_timeout}s` escalated",
        f"- section size: `{args.section_size}`; proof batch: `{args.proof_batch_size}`; workers: `{args.workers}`",
        f"- Phase 1 statement order: `{PHASE1_STATEMENT_ORDER}`",
        f"- Phase 2 implementation order: `{PHASE2_PROOF_ORDER}`",
        f"- conjecture policy: `{args.conjecture_policy}`",
        f"- repair/retry budget: `{args.max_trials}`",
        f"- library candidates: `{len(library_candidates)}`",
        "",
    ]

    repair_trials = 0
    noop_repairs = 0
    escalation_note = ""
    stuck_sections: list[SectionStuckState] = []
    started = time.monotonic()
    # A resumed state must prove that all individually refined contracts still
    # compile together before Phase 2 can use them. Keep this run-scoped so the
    # deterministic recheck is paid once per statement-state, not once per
    # proof frontier.
    phase1_integration_checked = False
    _print_pipeline_progress(ctx, sections, repair_trials, args.max_trials)
    try:
        while True:
            if (
                not ctx.repair_boundary_pending
                and _complete_verified_phase2_repair(ctx, sections)
            ):
                _save_ctx_state(ctx, sections)
            repair_boundary_active = bool(ctx.repair_boundary_pending)
            boundary_request = _pending_repair_boundary_request(ctx)
            if boundary_request is not None:
                if boundary_request.provider_contract_labels:
                    sections = _reroute_active_phase2_repair_to_provider(
                        ctx, sections, boundary_request
                    )
                    phase1_integration_checked = False
                    continue
                scheduling_request = _phase2_prerequisite_request_for_repair(
                    ctx,
                    sections,
                    boundary_request,
                    source="post_repair_boundary",
                )
                if scheduling_request is not None:
                    ctx.repair_boundary_pending = {}
                    _save_ctx_state(ctx, sections)
                    _log(
                        "==> Phase 2 scheduling deferred definition prerequisite(s) "
                        "instead of editing the blueprint again: "
                        + ", ".join(
                            scheduling_request.implementation_prerequisites
                        )
                    )
                    continue
            queued_phase2_request = (
                None
                if boundary_request is not None
                else _pending_phase2_repair_request(ctx)
            )
            if ctx.phase2_prerequisite_labels:
                # A queued blueprint repair from a sibling worker must not
                # preempt an implementation prerequisite just discovered for
                # the blocked top-down proof. Completed prerequisites are
                # removed here; the remaining repair queue is then resumed.
                ctx.phase2_prerequisite_labels.difference_update(
                    _proved_labels(sections)
                )
                if ctx.phase2_prerequisite_labels:
                    queued_phase2_request = None
            if repair_boundary_active:
                # Persist both an accepted audit (cleared state) and a routed
                # rejection before any further model call can be interrupted.
                _save_ctx_state(ctx, sections)
            if boundary_request is None:
                sections, reactivated, dropped_cached = _reactivate_deferred_sections(
                    ctx, sections
                )
            else:
                reactivated, dropped_cached = set(), set()
            if reactivated or dropped_cached:
                phase1_integration_checked = False
                _save_ctx_state(ctx, sections)
            required_skeleton = {
                label for label, node in ctx.nodes.items() if not node.mathlibok
            }
            frozen = _frozen_labels(sections)
            contract_pending = required_skeleton - frozen
            # Deferred sections can become ready only after their directly
            # changed/missing providers have been regenerated. Preserve those
            # cached descendants until that work is complete. Forcing the
            # recheck now would report "dependencies_unavailable", delete the
            # retained source, and turn a small repair into whole-subgraph
            # model regeneration.
            if _deferred_recheck_may_drop_unready(
                sections, contract_pending
            ):
                sections, more_reactivated, more_dropped = (
                    _reactivate_deferred_sections(
                        ctx, sections, drop_unready=True
                    )
                )
                reactivated |= more_reactivated
                dropped_cached |= more_dropped
                _save_ctx_state(ctx, sections)
                if more_dropped:
                    continue
                frozen = _frozen_labels(sections)
            # Phase 2 blueprint mutations are transactional. Replacement Lean
            # for every invalidated/new node has priority over another queued
            # graph edit; otherwise independent diagnoses accumulate an
            # unverified helper forest before any repair receives feedback.
            if ctx.phase2_started and required_skeleton - frozen:
                queued_phase2_request = None
            evidence_for_repair: str | None = None
            repair_labels: list[str] = []
            repair_helpers: list[str] = []
            repair_section_labels: list[str] = []
            repair_context_labels: list[str] = []
            repair_required_dependencies: dict[str, set[str]] = {}
            repair_model_labels: list[str] = []
            repair_evidence_by_label: dict[str, str] = {}
            repair_evidence_identities_by_label: dict[str, dict[str, Any]] = {}
            repair_components: list[dict[str, Any]] = []
            phase1_repair = False
            repair_authorized = True
            active_phase2_repair_id = ""

            if boundary_request is not None:
                evidence_for_repair = boundary_request.evidence
                repair_labels = boundary_request.labels
                repair_authorized = True
                repair_required_dependencies = boundary_request.required_dependencies
                repair_model_labels = boundary_request.model_repair_labels
                repair_evidence_by_label = dict(
                    boundary_request.evidence_by_label
                )
                repair_evidence_identities_by_label = copy.deepcopy(
                    boundary_request.evidence_identities_by_label
                )
                repair_components = list(boundary_request.repair_components)
                repair_helpers = boundary_request.decomposition_helpers
                repair_section_labels = list(boundary_request.section_labels)
                repair_context_labels = list(boundary_request.context_labels)
                phase1_repair = True
                _quarantine_labels(
                    ctx, boundary_request.labels, "post_repair_boundary_audit"
                )
            elif queued_phase2_request is not None:
                evidence_for_repair = queued_phase2_request.evidence
                repair_labels = list(queued_phase2_request.labels)
                repair_authorized = True
                repair_required_dependencies = (
                    queued_phase2_request.required_dependencies
                )
                repair_model_labels = list(
                    queued_phase2_request.model_repair_labels
                )
                repair_evidence_by_label = dict(
                    queued_phase2_request.evidence_by_label
                )
                repair_evidence_identities_by_label = copy.deepcopy(
                    queued_phase2_request.evidence_identities_by_label
                )
                repair_components = list(
                    queued_phase2_request.repair_components
                )
                repair_helpers = list(
                    queued_phase2_request.decomposition_helpers
                )
                repair_section_labels = list(
                    queued_phase2_request.section_labels
                )
                repair_context_labels = list(
                    queued_phase2_request.context_labels
                )
                active_phase2_repair_id = _start_phase2_repair_transaction(
                    ctx,
                    sections,
                    queued_phase2_request,
                )
                phase1_repair = False
                _log(
                    "==> Processing independent queued Phase 2 blueprint repair: "
                    + ", ".join(repair_labels[:8])
                    + f" ({len(ctx.phase2_repair_queue)} queued)"
                )

            if evidence_for_repair is None:
                contract_pending = required_skeleton - _frozen_labels(sections)
                declaration_work = _phase2_declaration_work_labels(
                    ctx, sections, contract_pending
                )
                if declaration_work:
                    stage = _contract_work_stage(ctx)
                    if ctx.phase2_started:
                        print(
                            f"==> {stage}: completing {len(declaration_work)} "
                            "new/changed blueprint node(s), including their Lean "
                            "statements and bodies, in one Phase 2 transaction each "
                            f"({len(required_skeleton) - len(contract_pending)} current "
                            "node(s) retained)",
                            flush=True,
                        )
                        _record(
                            ctx.telemetry,
                            "phase2_whole_node_repair_started",
                            labels=sorted(declaration_work),
                            pending_count=len(declaration_work),
                            total_pending_count=len(contract_pending),
                            prerequisite_priority=(
                                declaration_work != contract_pending
                            ),
                            frozen_current_count=(
                                len(required_skeleton) - len(contract_pending)
                            ),
                        )
                    else:
                        print(
                            f"==> {stage}: freezing {len(contract_pending)} "
                            f"new/changed statement contract(s) {PHASE1_STATEMENT_ORDER} "
                            f"({len(required_skeleton) - len(contract_pending)} current "
                            "contract(s) already frozen)",
                            flush=True,
                        )
                    try:
                        sections = _run_pending_declaration_work(
                            ctx, sections, declaration_work
                        )
                        integration_failures = _phase1_recompile_environment(
                            ctx, sections
                        )
                        phase1_integration_checked = not integration_failures
                        _save_ctx_state(ctx, sections)
                        _print_pipeline_progress(
                            ctx, sections, repair_trials, args.max_trials
                        )
                        if integration_failures:
                            continue
                        if ctx.phase2_started:
                            active = getattr(ctx, "phase2_repair_active", {}) or {}
                            verifying_id = (
                                str(active.get("request_id") or "")
                                if str(active.get("stage") or "") == "verify"
                                else ""
                            )
                            repair_complete = bool(
                                verifying_id
                                and _complete_verified_phase2_repair(
                                    ctx, sections
                                )
                            )
                            if verifying_id:
                                _save_ctx_state(ctx, sections)
                            _record(
                                ctx.telemetry,
                                "phase2_whole_node_repair_completed",
                                labels=sorted(declaration_work),
                                completed_count=len(declaration_work),
                            )
                            if not verifying_id:
                                _log(
                                    "==> Phase 2 whole-node repair complete; "
                                    "resuming top-down proof scheduling"
                                )
                            elif repair_complete:
                                _log(
                                    "==> Phase 2 whole-node replacement verified; "
                                    "repair transaction complete"
                                )
                            else:
                                _log(
                                    "==> Phase 2 whole-node replacement verified; "
                                    "rechecking unchanged deferred descendants"
                                )
                            if verifying_id:
                                # Re-enter through the queue gate so stale
                                # diagnoses are pruned only after the complete
                                # repaired dependency environment verifies.
                                continue
                    except RepairRequest as request:
                        scheduling_request = _phase2_prerequisite_request_for_repair(
                            ctx,
                            sections,
                            request,
                            source="phase2_complete_node_decomposition",
                        )
                        if scheduling_request is not None:
                            _save_ctx_state(ctx, sections)
                            _log(
                                "==> Phase 2 will implement deferred definition "
                                "prerequisite(s) before retrying complete-node work: "
                                + ", ".join(
                                    scheduling_request.implementation_prerequisites
                                )
                            )
                            continue
                        active = getattr(ctx, "phase2_repair_active", {}) or {}
                        if (
                            ctx.phase2_started
                            and str(active.get("stage") or "") == "verify"
                            and _requires_blueprint_transaction(
                                request.authorizes_blueprint_repair,
                                request.required_dependencies,
                            )
                        ):
                            sections, request = _restart_active_phase2_repair(
                                ctx, sections, request
                            )
                            phase1_integration_checked = False
                        evidence_for_repair = request.evidence
                        repair_labels = request.labels
                        repair_authorized = request.authorizes_blueprint_repair
                        repair_required_dependencies = request.required_dependencies
                        repair_model_labels = request.model_repair_labels
                        repair_evidence_by_label = dict(
                            request.evidence_by_label
                        )
                        repair_evidence_identities_by_label = copy.deepcopy(
                            request.evidence_identities_by_label
                        )
                        repair_components = list(request.repair_components)
                        if _requires_blueprint_transaction(
                            repair_authorized,
                            repair_required_dependencies,
                        ):
                            _quarantine_labels(
                                ctx,
                                request.labels,
                                (
                                    "blueprint_repair_request"
                                    if repair_authorized
                                    else "statement_dependency_edge_request"
                                ),
                            )
                        else:
                            _apply_phase1_retry_scheduling(ctx, request)
                        repair_helpers = request.decomposition_helpers
                        # Defense in depth: no caller may widen an editable
                        # normalization scope beyond the labels whose evidence
                        # actually authorized blueprint repair.
                        authorized = set(request.labels)
                        repair_section_labels = sorted(
                            authorized & set(request.section_labels)
                        ) or sorted(authorized)
                        repair_context_labels = list(request.context_labels)
                        phase1_repair = not ctx.phase2_started
                        active_phase2_repair_id = (
                            _start_caught_phase2_repair_transaction(
                                ctx, sections, request
                            )
                        )

                elif not phase1_integration_checked:
                    stage = _contract_work_stage(ctx)
                    _log(
                        f"==> {stage} integration gate: reusing matching compiled "
                        "statements and rebuilding only dirty modules"
                    )
                    integration_failures = _phase1_recompile_environment(
                        ctx, sections
                    )
                    phase1_integration_checked = not integration_failures
                    _save_ctx_state(ctx, sections)
                    if integration_failures:
                        continue
                    active = getattr(ctx, "phase2_repair_active", {}) or {}
                    verifying_id = (
                        str(active.get("request_id") or "")
                        if ctx.phase2_started
                        and str(active.get("stage") or "") == "verify"
                        else ""
                    )
                    if verifying_id:
                        if not _complete_verified_phase2_repair(ctx, sections):
                            _save_ctx_state(ctx, sections)
                            _log(
                                "==> Active Phase 2 repair still has deferred "
                                "dependency rechecks; keeping its transaction open"
                            )
                            continue
                        _save_ctx_state(ctx, sections)
                        _log(
                            "==> Verified active Phase 2 blueprint repair; "
                            "revalidating queued diagnoses"
                        )
                        continue

            if evidence_for_repair is None and ctx.conjecture_policy == "attempt":
                missing_conjecture_proofs = sorted(
                    label
                    for label, node in ctx.nodes.items()
                    if not node.mathlibok
                    and _is_conjecture_node(label, node)
                    and not _blueprint_node_has_proof(ctx, label)
                )
                if missing_conjecture_proofs:
                    evidence_for_repair = (
                        "Conjecture policy `attempt` requires the blueprint to "
                        "contain the mathematical proof before Lean formalizes it. "
                        "Add a detailed proof environment for each listed conjecture "
                        "without weakening or changing its statement. The resulting "
                        "blueprint proof, not an independently invented Lean proof, "
                        "must drive Phase 2.\n\n"
                        + "\n".join(
                            f"- {label}:\n{ctx.stmt_blocks.get(label, '')[:4000]}"
                            for label in missing_conjecture_proofs
                        )
                    )
                    repair_labels = missing_conjecture_proofs
                    repair_section_labels = missing_conjecture_proofs
                    repair_context_labels = missing_conjecture_proofs
                    repair_authorized = True

            if evidence_for_repair is None and phase1_integration_checked:
                if _begin_phase2(ctx, sections):
                    _save_ctx_state(ctx, sections)
                    _create_phase1_checkpoint(ctx)
                    _print_pipeline_progress(
                        ctx, sections, repair_trials, args.max_trials
                    )

            if evidence_for_repair is None:
                unproved_by_section: list[tuple[Section, list[str]]] = []
                all_unproved: set[str] = set()
                for sec in sections:
                    parsed, index = _module_decl_texts(sec)
                    labels = [
                        label
                        for label in sec.labels
                        if _lean_name(label) in index
                        and _has_terminal_sorry(
                            parsed.decls[index[_lean_name(label)]].text
                        )
                    ]
                    all_unproved.update(labels)
                    if labels:
                        unproved_by_section.append((sec, labels))
                proof_layer = -1
                proof_roots: list[str] = []
                frontier_labels = sorted(all_unproved)
                if all_unproved:
                    (
                        proof_layer,
                        frontier_labels,
                        proof_roots,
                        scheduling_mode,
                    ) = _phase2_scheduling_frontier(ctx, all_unproved)
                    frontier = set(frontier_labels)
                    unproved_by_section = [
                        (sec, [label for label in labels if label in frontier])
                        for sec, labels in unproved_by_section
                    ]
                    unproved_by_section = [
                        (sec, labels)
                        for sec, labels in unproved_by_section
                        if labels
                    ]
                if unproved_by_section:
                    mode_note = (
                        (
                            "dependency-first definition prerequisite plus independent ready branches"
                            if scheduling_mode
                            == "definition_prerequisite_with_independent_ready"
                            else "dependency-first definition prerequisite"
                            if scheduling_mode == "definition_prerequisite_override"
                            else f"{PHASE2_PROOF_ORDER} ready frontier {proof_layer}"
                        )
                        + " "
                        f"({len(frontier_labels)} node(s))"
                    )
                    print(
                        f"==> Phase 2: implementing deferred bodies for {mode_note} "
                        f"with {args.workers} worker(s)",
                        flush=True,
                    )
                    _record(
                        ctx.telemetry,
                        "proof_frontier_scheduled",
                        proof_order=PHASE2_PROOF_ORDER,
                        phase1_order=PHASE1_STATEMENT_ORDER,
                        scheduling=scheduling_mode,
                        layer=proof_layer,
                        labels=frontier_labels,
                        theorem_labels=[
                            label
                            for label in frontier_labels
                            if _is_theorem_like_kind(ctx.nodes[label].kind)
                        ],
                        definition_body_labels=[
                            label
                            for label in frontier_labels
                            if not _is_theorem_like_kind(ctx.nodes[label].kind)
                        ],
                        node_kinds={
                            label: ctx.nodes[label].kind
                            for label in frontier_labels
                        },
                        root_labels=proof_roots,
                        unproved_before=len(all_unproved),
                        section_count=len(unproved_by_section),
                    )
                    outcomes: list[SectionProofOutcome] = []
                    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
                        futures = [
                            pool.submit(_prove_section, ctx, sec, sections, labels)
                            for sec, labels in unproved_by_section
                        ]
                        for future in concurrent.futures.as_completed(futures):
                            outcomes.append(future.result())
                    _save_ctx_state(ctx, sections)
                    request = _route_phase2_proof_outcomes(
                        ctx, outcomes, sections
                    )
                    if request is not None:
                        if request.scheduling_only:
                            _save_ctx_state(ctx, sections)
                            _log(
                                "==> Phase 2 will implement deferred definition "
                                "prerequisite(s) before retrying the blocked node: "
                                + ", ".join(
                                    request.implementation_prerequisites
                                )
                            )
                            continue
                        evidence_for_repair = request.evidence
                        repair_labels = list(request.labels)
                        repair_helpers = list(request.decomposition_helpers)
                        repair_section_labels = list(request.section_labels)
                        repair_context_labels = list(request.context_labels)
                        repair_authorized = request.authorizes_blueprint_repair
                        repair_required_dependencies = request.required_dependencies
                        repair_model_labels = list(request.model_repair_labels)
                        repair_evidence_by_label = dict(request.evidence_by_label)
                        repair_evidence_identities_by_label = copy.deepcopy(
                            request.evidence_identities_by_label
                        )
                        repair_components = list(request.repair_components)
                        if request.authorizes_blueprint_repair:
                            active = getattr(ctx, "phase2_repair_active", {}) or {}
                            if str(active.get("stage") or "") == "verify":
                                if request.provider_contract_labels:
                                    sections = _reroute_active_phase2_repair_to_provider(
                                        ctx, sections, request
                                    )
                                    phase1_integration_checked = False
                                    continue
                                sections, request = _restart_active_phase2_repair(
                                    ctx, sections, request
                                )
                                evidence_for_repair = request.evidence
                                repair_labels = list(request.labels)
                                repair_helpers = list(
                                    request.decomposition_helpers
                                )
                                repair_section_labels = list(
                                    request.section_labels
                                )
                                repair_context_labels = list(
                                    request.context_labels
                                )
                                repair_model_labels = list(
                                    request.model_repair_labels
                                )
                                repair_evidence_by_label = dict(
                                    request.evidence_by_label
                                )
                                repair_authorized = (
                                    request.authorizes_blueprint_repair
                                )
                                repair_required_dependencies = dict(
                                    request.required_dependencies
                                )
                                repair_evidence_identities_by_label = copy.deepcopy(
                                    request.evidence_identities_by_label
                                )
                                repair_components = list(
                                    request.repair_components
                                )
                                phase1_integration_checked = False
                            active_phase2_repair_id = (
                                _start_phase2_repair_transaction(
                                    ctx,
                                    sections,
                                    request,
                                )
                            )
                        phase1_repair = False
                    else:
                        proved_now = sorted(
                            {label for outcome in outcomes for label in outcome.proved}
                        )
                        remaining_after = all_unproved - set(proved_now)
                        _record(
                            ctx.telemetry,
                            "proof_frontier_result",
                            proof_order=PHASE2_PROOF_ORDER,
                            phase1_order=PHASE1_STATEMENT_ORDER,
                            layer=proof_layer,
                            labels=frontier_labels,
                            proved_labels=proved_now,
                            remaining_after=len(remaining_after),
                            status="accepted",
                        )
                        if proof_layer == 0:
                            admitted_dependencies = sorted(
                                {
                                    dep
                                    for label in proved_now
                                    for dep in _dependency_closure(ctx.nodes, [label])
                                    if dep in all_unproved
                                }
                            )
                            _record(
                                ctx.telemetry,
                                "conditional_root_proofs",
                                root_labels=proved_now,
                                admitted_dependency_labels=admitted_dependencies,
                                admitted_dependency_count=len(admitted_dependencies),
                            )
                        _print_pipeline_progress(
                            ctx, sections, repair_trials, args.max_trials
                        )
                        if remaining_after:
                            # The accepted frontier is cached against immutable
                            # statement contracts. Advance one graph layer in the
                            # selected direction before the completeness gate.
                            continue

            if evidence_for_repair is None:
                proved = _proved_labels(sections)
                recorded = _recorded_conjecture_labels(ctx, sections)
                required = {
                    label
                    for label, node in ctx.nodes.items()
                    if not node.mathlibok and label not in recorded
                }
                if required <= proved:
                    final_code = _assemble_final(ctx, sections)
                    final_path = SCRATCH_DIR / args.name / "assembled_formalization.lean"
                    final_path.parent.mkdir(parents=True, exist_ok=True)
                    final_path.write_text(final_code, encoding="utf-8")
                    print("==> Final from-scratch Lean check on the assembled file", flush=True)
                    final_attempt = _run_lean(final_path, lean_command)
                    final_audit_nodes = {
                        label: copy.copy(node)
                        for label, node in ctx.nodes.items()
                        if not node.mathlibok
                    }
                    for label in recorded:
                        if label in final_audit_nodes:
                            final_audit_nodes[label].uses = _statement_uses(
                                final_audit_nodes[label]
                            )
                    coverage_issues = (
                        _deterministic_statement_audit(
                            final_code,
                            final_audit_nodes,
                            ctx.nodes,
                        )
                        if final_attempt.ok
                        else []
                    )
                    _record(
                        ctx.telemetry,
                        "final_check_result",
                        lean_ok=final_attempt.ok,
                        coverage_ok=not coverage_issues,
                        coverage_issues=coverage_issues,
                        output_tail=final_attempt.output[-4000:] if not final_attempt.ok else "",
                    )
                    if final_attempt.ok and not coverage_issues:
                        promoted = _promote_blueprint_draft(ctx)
                        published = _publish_lean_text(args.name, final_code)
                        report_lines += [
                            "## Complete",
                            f"- elapsed: `{int(time.monotonic() - started)}s`",
                            f"- repair/retry trials used: `{repair_trials}/{args.max_trials}`",
                            f"- published blueprint: `{promoted.relative_to(REPO_ROOT)}`",
                            f"- published Lean: `{published.relative_to(REPO_ROOT)}`",
                            f"- open conjectures recorded: `{len(recorded)}`",
                        ]
                        if args.build:
                            site_lean = _rebuild_site_for(args.name)
                            report_lines.append(f"- site Lean: `{site_lean.relative_to(REPO_ROOT)}`")
                        report = _write_report(args.name, report_lines)
                        print(
                            "All required proofs completed"
                            + (
                                f"; {len(recorded)} open conjecture(s) recorded"
                                if recorded
                                else ""
                            )
                            + f". Published {published.relative_to(REPO_ROOT)}"
                        )
                        print(f"Report written to {report.relative_to(REPO_ROOT)}")
                        shutil.rmtree(ctx.blueprint_dir, ignore_errors=True)
                        return finish(0, "complete", repairs=repair_trials)
                    evidence_for_repair = (
                        "Final assembled check failed:\n"
                        + (final_attempt.output[-8000:] if not final_attempt.ok else "")
                        + "\n".join(coverage_issues)
                    )
                    repair_labels = sorted(required - proved) or sorted(required)
                    repair_section_labels = repair_labels
                else:
                    # Shouldn't happen: no failures reported but nodes unproved.
                    evidence_for_repair = "Internal inconsistency: unproved nodes without failure evidence: " + ", ".join(sorted(required - proved))
                    repair_labels = sorted(required - proved)
                    repair_section_labels = repair_labels

            if evidence_for_repair is not None and not _requires_blueprint_transaction(
                repair_authorized,
                repair_required_dependencies,
            ):
                retry_stage = _contract_work_stage(ctx)
                retry_event = (
                    "phase2_generation_retry"
                    if bool(getattr(ctx, "phase2_started", False))
                    else "phase1_generation_retry"
                )
                retry_source = (
                    "outer_phase2_retry"
                    if bool(getattr(ctx, "phase2_started", False))
                    else "outer_phase1_retry"
                )
                if repair_trials >= args.max_trials:
                    report_lines += [
                        f"## Stopped: {retry_stage} generation retry budget exhausted",
                        "",
                        "```text",
                        evidence_for_repair[-6000:],
                        "```",
                    ]
                    report = _write_report(args.name, report_lines)
                    print(
                        "Stopped after the configured retry budget was exhausted "
                        f"without obtaining valid {_contract_work_stage(ctx)} Lean statements."
                    )
                    print(f"Report written to {report.relative_to(REPO_ROOT)}")
                    return finish(
                        1,
                        "max_trials_exhausted",
                        unresolved=repair_labels,
                    )
                repair_trials += 1
                _record(
                    ctx.telemetry,
                    retry_event,
                    labels=repair_labels,
                    trial=repair_trials,
                    max_trials=args.max_trials,
                    evidence=evidence_for_repair[-4000:],
                    blueprint_edited=False,
                    workflow_phase=(2 if ctx.phase2_started else 1),
                )
                _log(
                    f"==> {retry_stage} generation retry {repair_trials}/"
                    f"{args.max_trials}; blueprint unchanged; affected: "
                    + ", ".join(repair_labels[:8])
                )
                evidence_tail = "\n".join(evidence_for_repair.splitlines()[-12:])
                if evidence_tail:
                    _log("  retry evidence (last lines):\n" + evidence_tail)
                report_lines.append(
                    f"- {retry_stage} generation retry {repair_trials} without "
                    f"blueprint edit: `{', '.join(repair_labels[:8])}`"
                )
                _store_generation_feedback(
                    ctx,
                    repair_labels,
                    evidence_for_repair,
                    source=retry_source,
                    evidence_by_label=(repair_evidence_by_label or None),
                    evidence_identity_by_label=(
                        repair_evidence_identities_by_label or None
                    ),
                )
                _save_ctx_state(ctx, sections)
                _print_pipeline_progress(
                    ctx, sections, repair_trials, args.max_trials
                )
                continue

            # --- blueprint repair path (the ONLY route that edits the unpublished draft)
            if repair_trials >= args.max_trials:
                report_lines += [
                    "## Stopped: blueprint repair budget exhausted",
                    "",
                    "```text",
                    evidence_for_repair[-6000:],
                    "```",
                ]
                report = _write_report(args.name, report_lines)
                print(f"Stopped after {args.max_trials} blueprint repair trial(s).")
                print(f"Report written to {report.relative_to(REPO_ROOT)}")
                print(
                    "The unpublished blueprint draft, frozen statements, and "
                    "accepted proofs are kept; rerun with --continue."
                )
                return finish(1, "max_trials_exhausted", unresolved=repair_labels)

            stuck_state: SectionStuckState | None = None
            use_section_normalization = False
            if phase1_repair and repair_section_labels:
                stuck_state = _stuck_state_for(stuck_sections, repair_section_labels)
                use_section_normalization = (
                    stuck_state.repairs >= SECTION_NORMALIZATION_REPAIR_TRIGGER
                    and not stuck_state.normalized
                )

            repair_trials += 1
            nodes_before_repair = dict(ctx.nodes)
            statement_blocks_before_repair = dict(ctx.stmt_blocks)
            statement_fps_before_repair = dict(ctx.stmt_fps)
            content_path = ctx.content_path
            content_before_repair = content_path.read_text(encoding="utf-8")
            # Compound transactions have two independently authorized writers:
            # deterministic dependency insertion and model-authored blueprint
            # repair. Scope-check only the latter against its own targets. If it
            # exceeds that scope, restore this snapshot while retaining any
            # deterministic edge that was already validated and applied.
            scope_nodes_before = nodes_before_repair
            scope_content_before = content_before_repair
            scope_targets = list(repair_labels)
            scope_changed: set[str] | None = None
            deterministic_changed: set[str] = set()
            note = escalation_note
            boundary_audit_changed: set[str] | None = None
            if repair_helpers:
                note = _decomposition_note(
                    repair_model_labels or repair_labels, repair_helpers
                )
            action = (
                "compound-repair"
                if repair_required_dependencies and repair_model_labels
                else "dependency-edge-repair"
                if repair_required_dependencies
                else ("normalization" if use_section_normalization else "repair")
            )
            if repair_required_dependencies:
                unresolved_dependencies = {
                    label: dependencies - set(_statement_uses(ctx.nodes[label]))
                    for label, dependencies in repair_required_dependencies.items()
                    if label in ctx.nodes
                }
                unresolved_dependencies = {
                    label: dependencies
                    for label, dependencies in unresolved_dependencies.items()
                    if dependencies
                }
                _record(
                    ctx.telemetry,
                    "statement_dependency_edge_routed",
                    labels=sorted(unresolved_dependencies),
                    required_dependencies={
                        label: sorted(dependencies)
                        for label, dependencies in unresolved_dependencies.items()
                    },
                    remaining_blueprint_repair_authorized=repair_authorized,
                    model_repair_labels=repair_model_labels,
                    route=(
                        "compound-repair"
                        if repair_model_labels
                        else "dependency-edge-repair"
                    ),
                )
                dependency_changed = _apply_required_dependency_edges(
                    ctx, unresolved_dependencies
                )
                deterministic_changed = set(dependency_changed)
                changed = set(dependency_changed)
                boundary_audit_changed = set()
                scope_changed = set()
                scope_nodes_before = dict(ctx.nodes)
                scope_content_before = content_path.read_text(encoding="utf-8")
                cycle_rejections = getattr(
                    ctx, "last_dependency_edge_rejections", {}
                )
                cycle_labels = list(cycle_rejections)
                cycle_evidence = "\n".join(
                    message
                    for rejected in cycle_rejections.values()
                    for message in rejected.values()
                )
                model_labels = list(
                    dict.fromkeys([*repair_model_labels, *cycle_labels])
                )
                still_unresolved = {
                    label: dependencies - set(_statement_uses(ctx.nodes[label]))
                    for label, dependencies in unresolved_dependencies.items()
                    if label in ctx.nodes
                }
                still_unresolved = {
                    label: dependencies
                    for label, dependencies in still_unresolved.items()
                    if dependencies
                }
                if still_unresolved and not cycle_rejections:
                    # Insertion was attempted but the required edge remains
                    # absent, normally because draft validation rolled the
                    # deterministic transaction back.  Only this condition,
                    # not an already-satisfied no-op, authorizes model repair.
                    action = "repair"
                    model_labels = list(
                        dict.fromkeys([*model_labels, *still_unresolved])
                    )
                if model_labels:
                    scope_targets = list(model_labels)
                    model_changed = _repair_blueprint_components(
                        ctx,
                        evidence_for_repair,
                        model_labels,
                        trial=repair_trials,
                        max_trials=args.max_trials,
                        escalation_note=(
                            (
                                "The proposed direct dependency edge was rejected "
                                "because it would create a cycle. Repair the "
                                "provider/helper direction without weakening any "
                                "claim. Do not request the rejected edge again.\n\n"
                                + cycle_evidence
                                + "\n\n"
                                + note
                            )
                            if cycle_rejections
                            else note
                            if dependency_changed
                            else (
                                "The semantic critic and corrected Lean agree that "
                                "the listed statement dependencies are required, "
                                "but adding the direct edge failed blueprint validation. "
                                "Repair the dependency structure without weakening claims.\n\n"
                                + note
                            )
                        ),
                        repair_runner_agent=(
                            escalation_runner.partition(":")[0]
                            in {"codex", "claude-code"}
                        ),
                        decomposition_roots=(
                            repair_model_labels or repair_labels
                            if repair_helpers
                            else ()
                        ),
                        repair_components=repair_components,
                    )
                    scope_changed = set(model_changed)
                    changed.update(model_changed)
                    boundary_audit_changed.update(model_changed)
                elif boundary_request is not None:
                    # The persisted boundary transaction consisted only of
                    # certified edges and is complete.  Do not let its stale
                    # fingerprints turn the next iteration into model repair.
                    ctx.repair_boundary_pending = {}
                report_lines.append(
                    f"- {action.replace('-', ' ')} {repair_trials}: {len(changed)} node "
                    f"contract(s) changed for `{', '.join(repair_labels[:8])}`"
                )
            elif use_section_normalization and stuck_state is not None:
                try:
                    changed = _normalize_stuck_section(
                        ctx,
                        evidence_for_repair,
                        repair_section_labels,
                        context_labels=repair_context_labels,
                        trial=repair_trials,
                        max_trials=args.max_trials,
                        repair_runner_agent=escalation_runner.partition(":")[0] in {"codex", "claude-code"},
                    )
                    stuck_state.normalized = True
                    report_lines.append(
                        f"- section normalization {repair_trials}: {len(changed)} node contract(s) changed "
                        f"for `{', '.join(repair_section_labels[:8])}`"
                    )
                except SectionNormalizationRejected as exc:
                    stuck_state.normalized = True
                    action = "repair"
                    fallback_note = (
                        f"Constrained section normalization was rolled back automatically: {exc}. "
                        "Do a narrower repair/decomposition now. Edit only the listed failing "
                        "node contracts unless a new helper node is strictly required by their "
                        "dependency-closed proof structure."
                    )
                    report_lines.append(
                        f"- section normalization {repair_trials}: rejected and rolled back ({exc}); "
                        "falling back to targeted repair"
                    )
                    changed = _repair_blueprint_components(
                        ctx,
                        evidence_for_repair,
                        repair_labels,
                        trial=repair_trials,
                        max_trials=args.max_trials,
                        escalation_note=fallback_note,
                        repair_runner_agent=escalation_runner.partition(":")[0] in {"codex", "claude-code"},
                        decomposition_roots=(repair_labels if repair_helpers else ()),
                        repair_components=repair_components,
                    )
                    report_lines.append(
                        f"- fallback repair {repair_trials}: {len(changed)} node statement(s) changed "
                        f"for `{', '.join(repair_labels[:8])}`"
                    )
                    stuck_state.repairs += 1
                    stuck_state.repairs_after_normalization += 1
            else:
                changed = _repair_blueprint_components(
                    ctx,
                    evidence_for_repair,
                    repair_labels,
                    trial=repair_trials,
                    max_trials=args.max_trials,
                    escalation_note=note,
                    repair_runner_agent=escalation_runner.partition(":")[0] in {"codex", "claude-code"},
                    decomposition_roots=(repair_labels if repair_helpers else ()),
                    repair_components=repair_components,
                )
                report_lines.append(
                    f"- repair {repair_trials}: {len(changed)} node statement(s) changed "
                    f"for `{', '.join(repair_labels[:8])}`"
                )
                if stuck_state is not None:
                    stuck_state.repairs += 1
                    if stuck_state.normalized:
                        stuck_state.repairs_after_normalization += 1
            disconnected_rollback = False
            if changed:
                checked_changes = (
                    set(changed) if scope_changed is None else set(scope_changed)
                )
                graph_distances = _repair_graph_distances(
                    scope_nodes_before, ctx.nodes, scope_targets, checked_changes
                )
                disconnected = {
                    label
                    for label, distance in graph_distances.items()
                    if distance is None
                }
                downstream_scope_violations = (
                    _phase1_repair_scope_violations(
                        scope_nodes_before,
                        ctx.nodes,
                        scope_targets,
                        checked_changes,
                    )
                    if phase1_repair
                    else set()
                )
                # Phase 2 receives exact evidence for complete nodes. Existing
                # dependencies and neighboring contracts are read-only unless
                # that same request names them as defective. New helper nodes
                # remain legal and are checked by the graph/boundary gates.
                phase2_existing_scope_violations = (
                    _phase2_existing_repair_scope_violations(
                        scope_nodes_before,
                        scope_targets,
                        checked_changes,
                    )
                    if bool(getattr(ctx, "phase2_started", False))
                    else set()
                )
                _record(
                    ctx.telemetry,
                    "blueprint_repair_scope",
                    workflow_phase=(
                        "phase2"
                        if bool(getattr(ctx, "phase2_started", False))
                        else "phase1"
                    ),
                    labels=repair_labels,
                    action=action,
                    changed_labels=sorted(changed),
                    scope_targets=sorted(scope_targets),
                    scope_checked_labels=sorted(checked_changes),
                    deterministic_changed_labels=sorted(deterministic_changed),
                    graph_distances=graph_distances,
                    disconnected_labels=sorted(disconnected),
                    added_labels=sorted(
                        set(ctx.nodes) - set(scope_nodes_before)
                    ),
                    removed_labels=sorted(
                        set(scope_nodes_before) - set(ctx.nodes)
                    ),
                    downstream_scope_violations=sorted(downstream_scope_violations),
                    phase2_existing_scope_violations=sorted(
                        phase2_existing_scope_violations
                    ),
                )
                if (
                    disconnected
                    or downstream_scope_violations
                    or phase2_existing_scope_violations
                ):
                    content_path.write_text(
                        scope_content_before, encoding="utf-8"
                    )
                    restored = _validate_draft(ctx)
                    if restored.ok:
                        ctx.refresh_nodes(restored.nodes)
                    else:
                        # The snapshot was validated immediately before the
                        # repair. Keep the in-memory graph coherent and let the
                        # next normal validation pass retry rather than turning
                        # a recoverable repair into a new terminal condition.
                        ctx.refresh_nodes(scope_nodes_before)
                        _record(
                            ctx.telemetry,
                            "blueprint_repair_result",
                            labels=repair_labels,
                            status="rollback_validation_retry",
                            changed_labels=sorted(checked_changes),
                            changed_count=len(checked_changes),
                        )
                    _record(
                        ctx.telemetry,
                        "blueprint_repair_result",
                        labels=repair_labels,
                        status=(
                            "scope_rolled_back"
                            if downstream_scope_violations
                            or phase2_existing_scope_violations
                            else "disconnected_rolled_back"
                        ),
                        changed_labels=sorted(checked_changes),
                        changed_count=len(checked_changes),
                        retained_deterministic_labels=sorted(
                            deterministic_changed
                        ),
                        disconnected_labels=sorted(disconnected),
                        downstream_scope_violations=sorted(downstream_scope_violations),
                        phase2_existing_scope_violations=sorted(
                            phase2_existing_scope_violations
                        ),
                    )
                    if phase2_existing_scope_violations:
                        report_lines.append(
                            f"- {action} {repair_trials}: rolled back edits to "
                            "pre-existing Phase 2 contracts outside the directly "
                            "authorized scope `"
                            + ", ".join(
                                sorted(phase2_existing_scope_violations)[:8]
                            )
                            + "`"
                        )
                    elif downstream_scope_violations:
                        report_lines.append(
                            f"- {action} {repair_trials}: rolled back downstream "
                            f"contract changes `{', '.join(sorted(downstream_scope_violations)[:8])}`"
                        )
                    else:
                        report_lines.append(
                            f"- {action} {repair_trials}: rolled back graph-unrelated "
                            f"contract changes `{', '.join(sorted(disconnected)[:8])}`"
                        )
                    changed = set(deterministic_changed)
                    if boundary_audit_changed is not None:
                        boundary_audit_changed.clear()
                    disconnected_rollback = True
                    if phase2_existing_scope_violations:
                        escalation_note = (
                            "The previous Phase 2 repair was rolled back because it "
                            "edited pre-existing blueprint nodes outside the exact "
                            "failure scope. Treat dependencies and neighboring nodes "
                            "as read-only. Edit only the listed target node(s); new "
                            "dependency-connected helper nodes are allowed when the "
                            "evidence requires decomposition."
                        )
                    elif downstream_scope_violations:
                        escalation_note = (
                            "The previous Phase 1 repair was rolled back because it "
                            "changed downstream/consumer blueprint contracts instead "
                            "of only the failing target and its dependency/helper side. "
                            "For the next repair, edit only the listed failing node(s) "
                            "and any helper/dependency nodes they directly need. Do not "
                            "rewrite consumers; they will be rechecked deterministically "
                            "after the repaired contract freezes."
                        )
                    else:
                        escalation_note = (
                            "The previous transaction was rolled back because it changed "
                            "blueprint nodes with no dependency path to the requested "
                            "repair targets in either the old or new uses graph. Keep "
                            "the next repair dependency-connected; add explicit uses "
                            "edges for genuinely necessary helpers or consumers."
                        )
            if changed:
                noop_repairs = 0
                escalation_note = ""
                changed_requiring_boundary_audit = (
                    changed
                    if boundary_audit_changed is None
                    else boundary_audit_changed
                )
                boundary_labels = _mark_repair_boundary_pending(
                    ctx,
                    changed_requiring_boundary_audit,
                    nodes_before_repair,
                    previous_statement_blocks=statement_blocks_before_repair,
                    previous_statement_fps=statement_fps_before_repair,
                    repair_roots=(repair_model_labels or repair_labels),
                    failure_evidence=evidence_for_repair,
                )
                sections, invalidated = _invalidate_after_repair(
                    ctx,
                    sections,
                    changed,
                    lean_command,
                    previous_nodes=nodes_before_repair,
                )
                if (
                    active_phase2_repair_id
                    and not disconnected_rollback
                    and (
                        not repair_model_labels
                        or scope_changed is None
                        or bool(scope_changed)
                    )
                ):
                    _mark_phase2_repair_verifying(
                        ctx,
                        active_phase2_repair_id,
                        changed,
                        recheck_labels=set(invalidated) - set(changed),
                    )
                phase1_integration_checked = False
                deferred_labels = {
                    label
                    for sec in sections
                    if sec.deferred
                    for label in sec.labels
                }
                _record(
                    ctx.telemetry,
                    "repair_invalidation",
                    workflow_phase=(
                        "phase2"
                        if bool(getattr(ctx, "phase2_started", False))
                        else "phase1"
                    ),
                    changed_labels=sorted(changed),
                    invalidated_labels=sorted(invalidated),
                    invalidated_count=len(invalidated),
                    deferred_labels=sorted(deferred_labels),
                    deferred_count=len(deferred_labels),
                    regeneration_labels=sorted(set(invalidated) - deferred_labels),
                    regeneration_count=len(set(invalidated) - deferred_labels),
                    kept_section_count=len(sections),
                    proof_order=PHASE2_PROOF_ORDER,
                    phase1_order=PHASE1_STATEMENT_ORDER,
                )
                _record_proof_graph_telemetry(
                    ctx.telemetry,
                    ctx.nodes,
                    proof_order=PHASE2_PROOF_ORDER,
                    reason="post_repair",
                    focus_labels=invalidated | changed,
                )
                _save_ctx_state(ctx, sections)
                print(
                    f"  {action} changed {len(changed)} contract(s); "
                    f"{len(deferred_labels)} unchanged dependent node(s) queued "
                    "for deterministic recheck; "
                    f"{len(set(invalidated) - deferred_labels)} node(s) require "
                    f"regeneration; kept {len(sections)} skeleton section(s)",
                    flush=True,
                )
                if boundary_labels:
                    print(
                        "  queued one scoped post-repair blueprint audit before "
                        "Lean generation for: "
                        + ", ".join(sorted(boundary_labels)[:8]),
                        flush=True,
                    )
            else:
                noop_repairs += 1
                repair_rejection = str(
                    getattr(ctx, "last_blueprint_repair_rejection", "") or ""
                )
                if disconnected_rollback:
                    print(
                        "  out-of-scope repair changes rolled back; "
                        "retrying with narrower scope",
                        flush=True,
                    )
                elif repair_rejection:
                    escalation_note = (
                        "The previous repair was rolled back by a deterministic "
                        "transaction guard. Correct this exact graph error without "
                        "weakening claims:\n\n" + repair_rejection
                    )
                    print(
                        "  invalid repair rolled back; exact graph evidence will "
                        "be supplied to the next attempt",
                        flush=True,
                    )
                elif noop_repairs == 1:
                    escalation_note = (
                        "Your previous repair changed NOTHING in the parsed node "
                        "statements. You MUST materially edit the TeX of the listed "
                        "node(s): add missing concrete semantics, hypotheses, or split "
                        "them into smaller nodes."
                    )
                else:
                    escalation_note = _decomposition_note(repair_labels)
                if repair_boundary_active and ctx.repair_boundary_pending:
                    prior = str(
                        ctx.repair_boundary_pending.get("evidence") or ""
                    ).rstrip()
                    ctx.repair_boundary_pending["evidence"] = (
                        prior
                        + "\n\nThe preceding corrective repair was a no-op. "
                        "Materially correct the exact audited statement defect."
                    )[-12000:]
                    _save_ctx_state(ctx, sections)
                if not disconnected_rollback:
                    print("  repair was a no-op; escalating instructions", flush=True)
            _print_pipeline_progress(ctx, sections, repair_trials, args.max_trials)
    except RunnerError as exc:
        report_lines += ["## Stopped on runner error", "", "```text", str(exc)[-4000:], "```"]
        report = _write_report(args.name, report_lines)
        print(f"Runner error stopped the run: {exc}", flush=True)
        print(f"Report written to {report.relative_to(REPO_ROOT)}")
        print(
            "The unpublished blueprint draft and Lean state are saved; rerun "
            "with --continue once the environment is fixed."
        )
        status = "environment_error" if is_environment_error(exc) else "runner_error"
        return finish(1, status, error=str(exc))
    except ValueError as exc:
        report_lines += ["## Stopped", "", "```text", str(exc)[-4000:], "```"]
        report = _write_report(args.name, report_lines)
        print(f"Stopped: {exc}", flush=True)
        print(f"Report written to {report.relative_to(REPO_ROOT)}")
        return finish(1, "invalid_state", error=str(exc))


def logged_main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument("name", nargs="?")
    known, _unknown = parser.parse_known_args(argv)
    if not known.name:
        return main(argv)
    log_path = _run_log_path(known.name)
    with log_path.open("w", encoding="utf-8") as log_file:
        log_file.write("# Auto-Blueprint statements-first formalization log\n")
        log_file.write(f"# cwd: {REPO_ROOT}\n")
        log_file.write(f"# command: {' '.join([sys.argv[0], *(argv or sys.argv[1:])])}\n\n")
        started_at = time.monotonic()
        with contextlib.redirect_stdout(
            TeeStream(sys.stdout, log_file, started_at=started_at)
        ), contextlib.redirect_stderr(TeeStream(sys.stderr, log_file, started_at=started_at)):
            old_sigterm = signal.getsignal(signal.SIGTERM)

            def log_sigterm(signum, _frame) -> None:
                print(
                    "received SIGTERM; "
                    f"pid={os.getpid()} ppid={os.getppid()} pgid={os.getpgrp()} "
                    f"active_stage={_active_stage()!r}; exiting {128 + signum}",
                    file=sys.stderr,
                    flush=True,
                )
                with contextlib.suppress(Exception):
                    log_file.flush()
                os._exit(128 + signum)

            signal.signal(signal.SIGTERM, log_sigterm)
            print(f"Log file: {log_path.relative_to(REPO_ROOT)}", flush=True)
            try:
                return main(argv)
            except (FileNotFoundError, RunnerError, subprocess.CalledProcessError) as exc:
                print(f"error: {exc}", file=sys.stderr)
                return 2
            except Exception:
                # Python normally prints an unhandled traceback only after
                # this redirect context has unwound. Print it here so the
                # persistent formalization log and the terminal/Web UI both
                # receive the complete failure.
                traceback.print_exc(file=sys.stderr)
                return 1
            finally:
                signal.signal(signal.SIGTERM, old_sigterm)
                print(f"Log file: {log_path.relative_to(REPO_ROOT)}", flush=True)


if __name__ == "__main__":
    raise SystemExit(logged_main())
