"""Phase 2: whole-node repair transactions, the tactic ladder, and proof implementation.

Part of formalize_blueprint.py — the statements-first Lean formalization
pipeline. This file is not an importable module: formalize_blueprint.py
compiles and executes every part file into its own module namespace, in a
fixed order, so the pipeline keeps the single `formalize_blueprint`
namespace that its tests and tooling patch and import against. Names used
here may therefore be defined in earlier parts or in
formalize_blueprint.py's import block. See organize.md.
"""
from __future__ import annotations
# ruff: noqa: F821


# ---------------------------------------------------------------------------
# Phase 2: deferred declaration bodies


def _phase2_whole_node_prompt(
    ctx: Ctx,
    label: str,
    sections: list[Section],
    import_modules: list[str],
    *,
    evidence: str = "",
    timeout_s: int,
) -> str:
    """Request one complete Lean declaration for one repaired blueprint node.

    Phase 1 has already served its one-time purpose before this path is
    reachable. A Phase-2 blueprint repair therefore returns the repaired
    statement and its implementation together; it must never create another
    statement-only skeleton followed by a separate proof call.
    """
    node = ctx.nodes[label]
    signatures = _frozen_interface_digest(
        sections, import_modules, budget=20000
    )
    feedback = (
        "\nExact failure evidence from the previous whole-node attempt:\n"
        f"```text\n{evidence[-8000:]}\n```\n"
        if evidence
        else ""
    )
    return f"""TASK: REPAIR-COMPLETE-PHASE2-NODE

Return exactly one Lean 4 code block containing the complete declaration for
the target blueprint node below. No commentary.

This is a Phase 2 whole-node transaction:
- Formalize the exact current blueprint statement and implement its complete
  proof or definition body in the SAME declaration.
- Do not return `sorry`, `admit`, `by ?`, an axiom, or a statement-only
  skeleton. Phase 1 is already complete and will not run again.
- The blueprint node, including its proof, is the mathematical source of truth.
  The Lean declaration must prove or realize that node, not an older frozen
  statement and not an independently weakened substitute.
- Use the required Lean name `{_lean_name(label)}`.
- A same-node structure/class/inductive interface may accompany the target
  only when it is the concrete representation of this exact blueprint node.
  Do not introduce executable or theorem helpers that lack blueprint nodes.
- If the blueprint genuinely lacks a mathematical helper needed to formalize
  this node, return the documented NEEDS-DECOMPOSITION response instead of
  weakening the declaration.
- This call has a wall-clock budget of about {timeout_s}s. Always leave enough
  time to emit the complete declaration.

{_common_rules(ctx, [label])}

Blueprint name: {ctx.name}
Target: {label}
Blueprint kind: {node.kind}
Statement dependencies: {', '.join(sorted(_statement_uses(node))) or '(none)'}
Proof-only dependencies: {', '.join(sorted(_proof_uses(node) - _statement_uses(node))) or '(none)'}

Resolved dependency contracts:
```text
{_dependency_contract_table(ctx, [label], sections)}
```

Frozen Lean interfaces available to this node:
```lean
{signatures or '-- none'}
```

Complete current blueprint node, including its proof:
```tex
{ctx.tex_blocks.get(label, '')[:12000]}
```
{feedback}
"""


def _phase2_complete_node_correction_prompt(
    ctx: Ctx,
    label: str,
    sections: list[Section],
    import_modules: list[str],
    *,
    candidate_code: str,
    evidence: str,
    timeout_s: int,
) -> str:
    """Correct one retained complete node without reopening Phase 1.

    This is intentionally not the skeleton patch prompt: the returned target
    keeps its real body, and the statement and implementation are validated and
    committed atomically after the call.
    """
    node = ctx.nodes[label]
    signatures = _frozen_interface_digest(
        sections, import_modules, budget=16000
    )
    interface_timeout = evidence.startswith(OBJECT_INTERFACE_FAILURE_PREFIX)
    implementation_timeout = evidence.startswith(
        OBJECT_IMPLEMENTATION_FAILURE_PREFIX
    )
    correction_policy = (
        """- The statement-only object probe also timed out. You MAY change the
  Lean representation of this node's public statement/interface, including a
  same-node named structure with named fields, but the represented mathematical
  statement and proof obligations must remain exactly those in the blueprint.
- Remove deeply nested dependent products, repeated proof-bearing casts, and
  long anonymous projection chains from the public surface. This is a Lean
  representation correction, not permission to weaken the claim."""
        if interface_timeout
        else """- The statement-only object probe passed. Preserve the public
  statement/interface byte-for-byte and simplify only the proof or definition
  body so object generation remains bounded."""
        if implementation_timeout
        else "- Preserve every correct part of its public statement and implementation."
    )
    return f"""TASK: CORRECT-COMPLETE-PHASE2-NODE

Return exactly one Lean 4 code block containing the corrected complete
declaration for `{label}`. No commentary.

The candidate below already represents one Phase-2 statement-and-body
transaction. Correct only what the exact rejection requires:
{correction_policy}
- The complete current blueprint node, including its proof, remains the
  mathematical source of truth.
- Return the statement and its complete proof/definition body together. Never
  return `sorry`, `admit`, an axiom, or a Phase-1 skeleton.
- Use the public Lean name `{_lean_name(label)}`.
- Do not weaken the claim, replace concrete objects by abstract placeholders,
  or omit hypotheses/equations to make Lean compile.
- A same-node structural representation may accompany the target only when it
  concretely realizes this node. Do not invent theorem helpers without
  blueprint nodes.
- If the exact evidence proves that the blueprint lacks a required
  mathematical helper, return the documented NEEDS-DECOMPOSITION response.
- This focused correction has about {timeout_s}s. Do not re-explore the whole
  paper or generated workspace; use the supplied interfaces and diagnostics.

{_common_rules(ctx, [label])}

Blueprint name: {ctx.name}
Target: {label}
Blueprint kind: {node.kind}

Resolved dependency contracts:
```text
{_dependency_contract_table(ctx, [label], sections)}
```

Frozen Lean interfaces available to this node:
```lean
{signatures or '-- none'}
```

Complete current blueprint node, including its proof:
```tex
{ctx.tex_blocks.get(label, '')[:12000]}
```

Current complete Lean candidate to edit:
```lean
{candidate_code[:30000]}
```

Exact current rejection:
```text
{evidence[-12000:]}
```
"""


def _phase2_complete_candidate(
    ctx: Ctx, label: str, response_text: str
) -> tuple[ParsedModule, list[str], str]:
    """Canonicalize one model response into an owned complete-node module."""
    parsed = _ingest_model_lean(ctx, [label], response_text).parsed
    decl_texts = _delivered_decl_texts(
        parsed,
        [label],
        {_lean_name(label)},
        _planned_helper_owner_by_name(ctx, [label]),
    )
    if decl_texts is None:
        raise ValueError(
            f"response omitted `{_lean_name(label)}` or included an unowned helper"
        )
    code, _ranges = _compose_module(
        parsed.imports, parsed.preamble, decl_texts
    )
    return parsed, decl_texts, code


def _phase2_candidate_failure_kind(evidence: str) -> str:
    if evidence.startswith(OBJECT_INTERFACE_FAILURE_PREFIX):
        return "interface_usability"
    if evidence.startswith(OBJECT_IMPLEMENTATION_FAILURE_PREFIX):
        return "implementation_object"
    if evidence.startswith("Deterministic checks"):
        return "deterministic"
    if evidence.startswith("Lean object compilation"):
        return "object_compile"
    if evidence.startswith("Lean rejected"):
        return "lean_compile"
    if evidence.startswith("Statement alignment"):
        return "semantic_alignment"
    return "validation"


def _run_phase2_whole_node_transaction(
    ctx: Ctx,
    label: str,
    sections: list[Section],
    alloc: _SectionNumberAllocator,
) -> list[Section]:
    """Generate/correct, validate, and freeze one repaired node atomically.

    A rejected complete declaration is retained as the next correction seed.
    Phase 1's patcher cannot be used here because it intentionally emits
    terminal ``sorry`` bodies; this transaction instead uses a dedicated
    complete-node correction prompt and re-runs every normal acceptance gate.
    """
    import_modules = _sections_for_deps(ctx, [label], sections)
    stored = _phase2_node_candidate(ctx, label)
    last_evidence = (
        str(stored.get("evidence") or "")
        if stored
        else _generation_feedback_for(ctx, [label])
    )
    candidate_code = str(stored.get("code") or "") if stored else ""
    last_failure_kind = (
        str(stored.get("failure_kind") or "validation")
        if stored
        else "validation"
    )
    last_failure_identity = (
        copy.deepcopy(stored.get("failure_identity"))
        if stored and isinstance(stored.get("failure_identity"), dict)
        else {}
    )
    if (
        stored
        and candidate_code.strip()
        and str(stored.get("failure_kind") or "") == "object_compile"
        and "object compilation" in last_evidence.lower()
        and "timed out" in last_evidence.lower()
    ):
        # State written before the usability gate retained the right complete
        # candidate but mislabeled a 600s object timeout as generic proof
        # generation. Diagnose that retained candidate once before spending a
        # correction call, then persist the actionable classification.
        legacy_timeout = LeanAttempt(
            ok=False,
            command=[],
            reason="Legacy object compilation timed out after 600s.",
            kind="object-timeout",
            duration_s=600.0,
        )
        failure_class, classified = _object_gate_evidence(
            ctx,
            [label],
            candidate_code,
            legacy_timeout,
            complete_bodies=True,
        )
        last_evidence = classified
        last_failure_kind = failure_class
        last_failure_identity = {
            "source": "object_gate",
            "failure_class": failure_class,
            "error_shape": _lean_error_shape(classified),
        }
        stored["evidence"] = classified[-12000:]
        stored["failure_kind"] = failure_class
        stored["failure_identity"] = copy.deepcopy(last_failure_identity)
        _record(
            ctx.telemetry,
            "phase2_legacy_object_timeout_classified",
            label=label,
            classification=failure_class,
        )
    # A repeated candidate/failure pair means focused correction already made
    # no progress. Reseed once from the blueprint; otherwise continue directly
    # from the retained complete declaration.
    correction_first = bool(stored and not stored.get("repeated_state"))
    attempts = (
        ["correction"]
        if correction_first
        else ["generation", "correction"]
    )
    for action in attempts:
        if action == "correction":
            if not candidate_code.strip():
                # No salvageable output exists (for example, the base call
                # timed out before emitting Lean). Preserve the old two-tier
                # availability policy, but make this a fresh full generation.
                tier = "escalation"
                timeout_s = ctx.hard_timeout
                effort = ctx.escalation_effort
                prompt = _phase2_whole_node_prompt(
                    ctx,
                    label,
                    sections,
                    import_modules,
                    evidence=last_evidence,
                    timeout_s=timeout_s,
                )
                purpose = "phase2_whole_node_repair"
            else:
                tier = "escalation"
                timeout_s = min(
                    ctx.hard_timeout, PHASE2_COMPLETE_CORRECTION_TIMEOUT
                )
                effort = ctx.escalation_effort
                prompt = _phase2_complete_node_correction_prompt(
                    ctx,
                    label,
                    sections,
                    import_modules,
                    candidate_code=candidate_code,
                    evidence=last_evidence,
                    timeout_s=timeout_s,
                )
                correction_fingerprint = hashlib.sha256(
                    (
                        _phase2_node_candidate_epoch(ctx, label)
                        + "\0"
                        + _candidate_hash(candidate_code)
                        + "\0"
                        + _diagnostic_failure_signature(
                            kind=last_failure_kind,
                            text=last_evidence,
                            identity=last_failure_identity,
                        )
                        + "\0"
                        + ctx.escalation_runner_spec
                    ).encode("utf-8")
                ).hexdigest()
                attempted = set(
                    (_phase2_node_candidate(ctx, label) or {}).get(
                        "attempted_corrections", []
                    )
                )
                if correction_fingerprint in attempted:
                    _record(
                        ctx.telemetry,
                        "phase2_complete_correction_skipped",
                        label=label,
                        reason=(
                            "identical_candidate_and_rejection_already_attempted"
                        ),
                        correction_sha256=correction_fingerprint,
                    )
                    # Reseed once from the blueprint instead of replaying the
                    # same correction or terminating the whole run.
                    attempts.append("generation")
                    continue
                _note_phase2_candidate_correction(
                    ctx, label, correction_fingerprint
                )
                purpose = "phase2_complete_node_correction"
        else:
            tier = "base"
            timeout_s = ctx.base_timeout
            effort = ctx.base_effort
            prompt = _phase2_whole_node_prompt(
                ctx,
                label,
                sections,
                import_modules,
                evidence=last_evidence,
                timeout_s=timeout_s,
            )
            purpose = "phase2_whole_node_repair"

        # Complete-node corrections are self-contained. Historical telemetry
        # shows resumed Phase-2 calls were both slower and far more likely to
        # hit 600s than fresh calls, while Phase-1 patch sessions remain useful.
        result = _call_model(
            ctx,
            prompt,
            purpose=purpose,
            timeout=timeout_s,
            effort=effort,
            labels=[label],
            escalated=tier == "escalation",
        )
        candidate_text = result.text or result.partial_text
        refusal = _parse_decomposition_refusal(
            candidate_text, expected_labels={label}
        )
        if refusal is not None:
            refusal_evidence = (
                f"Generator requested decomposition for {label}: "
                f"{refusal['reason']}"
            )
            # Phase 2 receives the complete current node, its proof, every
            # frozen dependency interface, and prior failure evidence. Unlike
            # Phase 1 statement generation, this is already the final
            # statement-and-body transaction. A concrete decomposition refusal
            # is therefore useful repair evidence, not a reason to pay for an
            # escalated generator to force a weakened substitute from the same
            # blueprint contract.
            _record(
                ctx.telemetry,
                "phase2_whole_node_decomposition",
                label=label,
                tier=tier,
                reason=refusal["reason"],
                missing_helpers=refusal["missing_helpers"],
                routed_immediately=True,
            )
            raise RepairRequest(
                refusal_evidence,
                [label],
                decomposition_helpers=refusal["missing_helpers"],
                section_labels=[label],
                authorizes_blueprint_repair=True,
            )
        # A timed-out CLI call may already have emitted a complete declaration.
        # Put that output through every normal gate before paying for another
        # call; an incomplete partial response simply fails ingestion below.
        if result.status not in {"ok", "timeout"} or not candidate_text.strip():
            last_evidence = result.error or (
                f"{tier} {action} call returned {result.status}"
            )
            last_failure_kind = "model_call"
            last_failure_identity = {
                "source": "model_call",
                "status": result.status,
            }
            continue
        try:
            parsed, decl_texts, delivered_code = _phase2_complete_candidate(
                ctx, label, candidate_text
            )
        except ValueError as exc:
            last_evidence = f"Invalid complete Lean response: {exc}"
            last_failure_kind = "response_format"
            last_failure_identity = {
                "source": "response_format",
                "error_type": type(exc).__name__,
            }
            continue
        failure_evidence: list[str] = []
        failure_identities: list[dict[str, Any]] = []
        failure_candidate_code: list[str] = []
        try:
            added = _freeze_section_from_code(
                ctx,
                [label],
                sections,
                alloc,
                decl_texts,
                list(parsed.imports),
                list(parsed.preamble),
                origin=f"Phase 2 whole-node {tier} transaction",
                allow_patch=False,
                complete_bodies=True,
                generation_tier=tier,
                failure_evidence=failure_evidence,
                failure_identities=failure_identities,
                failure_candidate_code=failure_candidate_code,
                lean_timeout=CANDIDATE_LEAN_CHECK_TIMEOUT,
            )
        except RepairRequest:
            # A semantic audit that identifies a blueprint defect is already
            # exact evidence for the normal Phase-2 blueprint transaction.
            raise
        if added is not None:
            _clear_phase2_node_candidate(ctx, label)
            _record(
                ctx.telemetry,
                "phase2_whole_node_transaction",
                label=label,
                status="committed",
                tier=tier,
                statement_fp=ctx.stmt_fps.get(label, ""),
                contract_fp=ctx.contract_fps.get(label, ""),
            )
            return added
        last_evidence = "\n".join(failure_evidence)[-12000:] or (
            "Complete declaration failed deterministic, Lean, or alignment gates."
        )
        last_failure_kind = _phase2_candidate_failure_kind(last_evidence)
        last_failure_identity = (
            copy.deepcopy(failure_identities[-1])
            if failure_identities
            else {}
        )
        candidate_code = (
            failure_candidate_code[-1]
            if failure_candidate_code
            else delivered_code
        )
        stored = _store_phase2_node_candidate(
            ctx,
            label,
            candidate_code,
            evidence=last_evidence,
            failure_kind=last_failure_kind,
            tier=tier,
            source=f"phase2_{action}_validation",
            failure_identity=last_failure_identity,
        )
        _store_generation_feedback(
            ctx,
            [label],
            last_evidence,
            source="phase2_whole_node_retry",
            evidence_identity_by_label={
                label: last_failure_identity
            } if last_failure_identity else None,
        )

    _record(
        ctx.telemetry,
        "phase2_whole_node_transaction",
        label=label,
        status="exhausted",
        evidence=last_evidence[-4000:],
        failure_class="lean_generation_exhausted",
        route="bounded_generation_retry",
        retained_candidate=bool(candidate_code.strip()),
        retained_candidate_sha256=(
            _candidate_hash(candidate_code) if candidate_code.strip() else ""
        ),
        blueprint_edit_authorized=False,
    )
    raise RepairRequest(
        "Phase 2 could not validate a complete Lean node within this bounded "
        "generation/correction transaction. The latest complete candidate is "
        "retained for the next correction. The blueprint remains unchanged because "
        "the failures provide no mathematical evidence that its contract needs "
        "repair. Retry Lean generation using the exact evidence below:\n\n"
        + last_evidence,
        [label],
        section_labels=[label],
        authorizes_blueprint_repair=False,
        evidence_by_label={label: last_evidence},
    )


def _run_phase2_whole_node_repairs(
    ctx: Ctx,
    sections: list[Section],
    pending: set[str],
) -> list[Section]:
    """Complete every Phase-2-changed node without reopening Phase 1.

    Nodes are made compilation-ready from dependencies upward, but each unit is
    one complete blueprint/Lean node. This ordering is local transaction
    plumbing; ordinary Phase 2 proof scheduling remains top-down.
    """
    alloc = _SectionNumberAllocator(
        max((section.number for section in sections), default=0) + 1
    )
    remaining = set(pending)
    while remaining:
        ready = _bottom_up_ready_frontier(
            ctx.nodes, remaining, _frozen_labels(sections)
        )
        if not ready:
            blocked = {
                label: sorted(
                    dep
                    for dep in ctx.nodes[label].uses
                    if dep in remaining and not ctx.nodes[dep].mathlibok
                )
                for label in sorted(remaining)
            }
            raise RepairRequest(
                "Phase 2 whole-node repair has no dependency-ready node; "
                "the repaired blueprint graph is cyclic or incomplete: "
                + json.dumps(blocked, sort_keys=True),
                sorted(remaining),
                section_labels=sorted(remaining),
                authorizes_blueprint_repair=True,
            )
        _log(
            f"==> Phase 2 whole-node repair: completing {len(ready)} "
            "dependency-ready node(s)"
        )
        worker_count = max(1, min(ctx.workers, len(ready)))
        results: dict[str, list[Section]] = {}
        failures: list[RepairRequest] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
            futures = {
                pool.submit(
                    _run_phase2_whole_node_transaction,
                    ctx,
                    label,
                    list(sections),
                    alloc,
                ): label
                for label in ready
            }
            for future in concurrent.futures.as_completed(futures):
                label = futures[future]
                try:
                    results[label] = future.result()
                except RepairRequest as request:
                    failures.append(request)
        completed: set[str] = set()
        for label in ready:
            added = results.get(label, [])
            if added:
                sections.extend(added)
                completed.add(label)
        remaining.difference_update(completed)
        _save_ctx_state(ctx, sections)
        if failures:
            # Whole-node workers can independently discover either a local
            # Lean-generation failure or evidence that authorizes a blueprint
            # edit/decomposition. Route the latter through the outer Phase-2
            # blueprint transaction; the non-blueprint aggregator deliberately
            # rejects those requests.
            authorized = [
                request
                for request in failures
                if request.authorizes_blueprint_repair
            ]
            if authorized:
                # Every worker produced evidence for its own node/component.
                # Keep those edit scopes independent: unioning them let one
                # repair model rewrite unrelated foundational interfaces and
                # invalidate accepted work from other branches.
                active = getattr(ctx, "phase2_repair_active", {}) or {}
                if str(active.get("stage") or "") == "verify":
                    # Verification of the active repair may expose one further
                    # helper defect. Extend that same transaction immediately;
                    # keep independent siblings queued behind it.
                    authorized.sort(key=lambda item: tuple(item.labels))
                    request = authorized[0]
                    _enqueue_phase2_repair_requests(ctx, authorized[1:])
                else:
                    _enqueue_phase2_repair_requests(ctx, authorized)
                    request = _pending_phase2_repair_request(ctx)
                    if request is None:
                        raise RuntimeError(
                            "authorized Phase 2 repair queue unexpectedly became empty"
                        )
                _save_ctx_state(ctx, sections)
            else:
                request = _aggregate_retry_requests(
                    failures, frozen_sections=[]
                )
            request.frozen_sections = []
            raise request
        if not completed:
            raise RepairRequest(
                "Phase 2 whole-node repair made no progress.",
                ready,
                section_labels=ready,
                authorizes_blueprint_repair=True,
            )
    return sections


@dataclass
class SectionProofOutcome:
    section: Section
    proved: list[str] = field(default_factory=list)
    failed: dict[str, str] = field(default_factory=dict)  # label -> evidence
    decomposition: dict[str, list[str]] = field(default_factory=dict)  # label -> helpers
    decomposition_evidence: dict[str, str] = field(default_factory=dict)


def _phase2_unimplemented_body_kinds(
    ctx: Ctx,
    sections: Iterable[Section],
) -> dict[str, str]:
    """Map definition labels whose Phase-2 implementation is unavailable.

    A provider can be unavailable either because its retained declaration still
    has a deferred body or because a legitimate Phase-2 blueprint repair
    invalidated and removed the complete declaration. Both states require the
    same local implementation scheduling; neither is evidence that the
    blueprint needs another edit.
    """
    section_list = list(sections)
    pending: dict[str, str] = {}
    for section in section_list:
        if section.deferred or not section.path.is_file():
            continue
        try:
            parsed = _parse_module(section.path.read_text(encoding="utf-8"))
        except OSError:
            continue
        by_name = {decl.name: decl for decl in parsed.decls if decl.name}
        for label in section.labels:
            decl = by_name.get(_lean_name(label))
            if decl is not None and _has_terminal_sorry(decl.text):
                pending[label] = decl.kind
    frozen = _frozen_labels(section_list)
    for label, node in ctx.nodes.items():
        if (
            not node.mathlibok
            and node.kind in DEFINITION_LIKE_KINDS
            and label not in frozen
        ):
            pending[label] = "missing-definition"
    return pending


def _phase2_implemented_definition_labels(
    ctx: Ctx, labels: Iterable[str]
) -> list[str]:
    """Return accepted Phase-2 labels whose bodies affect reduction.

    Theorem proof bodies are opaque to importers, so replacing ``sorry`` with a
    proof does not require rebuilding their section object.  A completed
    ``def``/``abbrev`` body is different: downstream declarations may need to
    unfold it, and must therefore import the new body rather than the frozen
    Phase-1 ``sorry`` object.
    """
    return [
        label
        for label in dict.fromkeys(labels)
        if label in ctx.nodes
        and not _is_theorem_like_kind(ctx.nodes[label].kind)
    ]


def _persist_phase2_section_outcome(
    ctx: Ctx,
    outcome: "SectionProofOutcome",
    sections: list[Section],
    *,
    original_source: str,
    original_compile_fingerprint: str,
) -> None:
    """Publish accepted Phase-2 work without exposing stale definition bodies.

    Phase 1 already built an importable ``.olean`` containing the frozen
    interfaces.  Keeping that object is correct for theorem-only proof work,
    but not after a definition body is implemented.  Rebuild such a section
    under the shared state lock before saving progress.  The source and object
    are restored transactionally if the object build unexpectedly fails.
    """
    definition_labels = _phase2_implemented_definition_labels(
        ctx, outcome.proved
    )
    with _STATE_LOCK:
        if definition_labels:
            attempt = _compile_section_olean(
                outcome.section, ctx.lean_command, sections
            )
            _record(
                ctx.telemetry,
                "phase2_definition_object_refresh",
                section=outcome.section.number,
                labels=definition_labels,
                status="success" if attempt.ok else "failed",
                duration_s=attempt.duration_s,
                error="" if attempt.ok else attempt.output[-4000:],
            )
            if not attempt.ok:
                outcome.section.path.write_text(
                    original_source, encoding="utf-8"
                )
                rollback = _compile_section_olean(
                    outcome.section, ctx.lean_command, sections
                )
                if rollback.ok:
                    outcome.section.compile_fingerprint = (
                        original_compile_fingerprint
                        or outcome.section.compile_fingerprint
                    )
                failed_labels = list(dict.fromkeys(outcome.proved))
                outcome.proved.clear()
                evidence = (
                    "accepted Phase-2 definition body could not be published "
                    "as an importable Lean object; the section was rolled back:\n"
                    + attempt.output[-4000:]
                )
                for label in failed_labels:
                    outcome.failed[label] = evidence
                if not rollback.ok:
                    raise RuntimeError(
                        "Phase-2 definition object publication failed and the "
                        "previous section object could not be restored:\n"
                        + rollback.output[-4000:]
                    )
        _save_ctx_state(ctx, sections)


def _phase2_definition_prerequisites(
    ctx: Ctx,
    sections: Iterable[Section],
    blocked_labels: Iterable[str],
    evidence_by_label: Mapping[str, str],
) -> dict[str, set[str]]:
    """Find deferred definitions that concrete Phase-2 evidence needs unfolded.

    Top-down proof order may assume a deferred theorem statement, but Lean
    cannot reduce a ``def`` whose value is still ``sorry``. This detector is
    intentionally evidence-bound: it considers only unresolved definition-like
    declarations in the blocked node's blueprint dependency closure, then
    requires the diagnostic to name that blueprint/Lean declaration. A unique
    direct definition is also accepted when the diagnostic explicitly says the
    obstacle is opacity or unfolding. It never infers a new dependency edge.
    """
    pending_kinds = _phase2_unimplemented_body_kinds(ctx, sections)
    definition_kinds = {"def", "abbrev", "instance", "missing-definition"}
    routed: dict[str, set[str]] = {}
    opacity_cue = re.compile(
        r"\b(?:opaque|unfold|unfolding|definition body|definitional|"
        r"does not reduce|cannot reduce|not implemented|incomplete definition)\b",
        re.IGNORECASE,
    )
    for blocked in dict.fromkeys(str(label) for label in blocked_labels):
        if blocked not in ctx.nodes:
            continue
        evidence = str(evidence_by_label.get(blocked) or "")
        if not evidence.strip():
            continue
        closure = _dependency_closure(ctx.nodes, [blocked]) - {blocked}
        candidates = {
            dependency
            for dependency in closure
            if pending_kinds.get(dependency) in definition_kinds
        }
        if not candidates:
            continue
        explicit = {
            dependency
            for dependency in candidates
            if dependency in evidence
            or re.search(
                rf"(?<![A-Za-z0-9_]){re.escape(_lean_name(dependency))}(?![A-Za-z0-9_])",
                evidence,
            )
        }
        selected = explicit
        if not selected and opacity_cue.search(evidence):
            direct = candidates & set(ctx.nodes[blocked].uses)
            if len(direct) == 1:
                selected = direct
        if selected:
            routed[blocked] = selected
    return routed


def _schedule_phase2_definition_prerequisites(
    ctx: Ctx,
    sections: Iterable[Section],
    blocked_labels: Iterable[str],
    evidence_by_label: Mapping[str, str],
    *,
    source: str,
) -> tuple[set[str], dict[str, set[str]]]:
    """Persist a local implementation-order override without editing TeX."""
    section_list = list(sections)
    routed = _phase2_definition_prerequisites(
        ctx, section_list, blocked_labels, evidence_by_label
    )
    prerequisites = {
        dependency for dependencies in routed.values() for dependency in dependencies
    }
    if not prerequisites:
        return set(), {}
    # A named provider may itself have been invalidated together with one or
    # more of its dependencies. Rebuild only the missing part of that existing
    # blueprint closure so the complete-node transaction remains
    # dependency-ready. Frozen theorem statements are sufficient and are not
    # reopened; no dependency edge is inferred here.
    frozen = _frozen_labels(section_list)
    missing_closure = {
        label
        for label in _dependency_closure(ctx.nodes, sorted(prerequisites))
        if label in ctx.nodes
        and not ctx.nodes[label].mathlibok
        and label not in frozen
    }
    prerequisites.update(missing_closure)
    if not hasattr(ctx, "phase2_prerequisite_labels"):
        ctx.phase2_prerequisite_labels = set()
    ctx.phase2_prerequisite_labels.update(prerequisites)
    _record(
        ctx.telemetry,
        "phase2_definition_prerequisite_routed",
        source=source,
        blocked_labels=sorted(routed),
        prerequisite_labels=sorted(prerequisites),
        prerequisites_by_blocked={
            label: sorted(dependencies) for label, dependencies in routed.items()
        },
        evidence_by_label={
            label: str(evidence_by_label.get(label) or "")[-4000:]
            for label in routed
        },
        blueprint_edited=False,
        repair_trial_consumed=False,
        normal_phase2_order=PHASE2_PROOF_ORDER,
        prerequisite_order="bottom-up",
    )
    return prerequisites, routed


def _phase2_prerequisite_frontier(
    ctx: Ctx, unresolved: set[str]
) -> tuple[int, list[str], list[str]] | None:
    """Return the next local dependency-body override, if one is pending."""
    if not hasattr(ctx, "phase2_prerequisite_labels"):
        ctx.phase2_prerequisite_labels = set()
    ctx.phase2_prerequisite_labels.intersection_update(unresolved)
    if not ctx.phase2_prerequisite_labels:
        return None
    return _next_implementation_frontier(
        ctx.nodes,
        set(ctx.phase2_prerequisite_labels),
        "bottom-up",
    )


def _prioritized_phase2_declaration_work(
    ctx: Ctx, pending: set[str]
) -> set[str]:
    """Prefer a persisted local prerequisite closure over unrelated repairs."""
    if not bool(getattr(ctx, "phase2_started", False)):
        return set(pending)
    priority = set(pending) & set(
        getattr(ctx, "phase2_prerequisite_labels", set())
    )
    return priority or set(pending)


def _phase2_declaration_work_labels(
    ctx: Ctx,
    sections: Iterable[Section],
    contract_pending: Iterable[str],
) -> set[str]:
    """Return missing declarations without republishing frozen definitions.

    A Phase-2 repair may introduce a new helper while its proof is blocked on
    an older frozen ``def`` whose body is still ``sorry``.  The helper remains
    contract-pending, but regenerating it cannot make progress until that
    provider is implemented.  A missing/invalidated provider belongs in the
    complete-node declaration path.  An already-frozen provider does not: the
    normal Phase-2 body scheduler must replace its ``sorry`` in the owning
    section and rebuild that section's object.  Publishing the frozen provider
    again in a new section creates a duplicate Lean declaration.
    """
    pending = set(contract_pending)
    if not bool(getattr(ctx, "phase2_started", False)):
        return pending
    prerequisites = set(getattr(ctx, "phase2_prerequisite_labels", set()))
    missing_prerequisites = prerequisites & pending
    if missing_prerequisites:
        return missing_prerequisites
    deferred_frozen_prerequisites = prerequisites & set(
        _phase2_unimplemented_body_kinds(ctx, sections)
    )
    if deferred_frozen_prerequisites:
        # Leave unrelated declaration work queued. The proof scheduler below
        # will select this provider through _phase2_prerequisite_frontier.
        return set()
    return _prioritized_phase2_declaration_work(ctx, pending)


def _route_phase2_proof_outcomes(
    ctx: Ctx,
    outcomes: Iterable[SectionProofOutcome],
    sections: Iterable[Section] = (),
) -> RepairRequest | None:
    """Route one proof frontier without widening blueprint-edit authority.

    Explicit decomposition findings are independent mathematical repair
    transactions, one per named blueprint node. Ordinary compiler/generation
    failures remain Lean retries and never inherit blueprint-edit authority
    merely because a sibling worker requested decomposition.
    """
    ordered = list(outcomes)
    section_list = list(sections)
    failed: dict[str, str] = {}
    authorized: list[RepairRequest] = []
    decomposition_evidence: dict[str, str] = {}
    decomposition_helpers: dict[str, list[str]] = {}
    for outcome in ordered:
        failed.update(outcome.failed)
        for label, helpers in outcome.decomposition.items():
            reason = outcome.decomposition_evidence.get(
                label, "generator requested decomposition"
            )
            decomposition_evidence[label] = reason
            decomposition_helpers[label] = list(helpers)

    prerequisites, prerequisite_routes = _schedule_phase2_definition_prerequisites(
        ctx,
        section_list,
        decomposition_evidence,
        decomposition_evidence,
        source="phase2_proof_decomposition",
    )
    prerequisite_blocked = set(prerequisite_routes)
    for label, reason in decomposition_evidence.items():
        if label in prerequisite_blocked:
            failed.pop(label, None)
            continue
        helpers = decomposition_helpers[label]
        evidence = (
            f"Phase 2 implementation requested decomposition for {label}.\n"
            f"Blueprint statement:\n{ctx.stmt_blocks.get(label, '')[:2500]}\n"
            f"Exact decomposition evidence:\n{reason[-5000:]}"
        )
        authorized.append(
            RepairRequest(
                evidence,
                [label],
                decomposition_helpers=list(helpers),
                section_labels=[label],
                context_labels=[label],
                authorizes_blueprint_repair=True,
                evidence_by_label={label: reason},
            )
        )

    if prerequisites:
        # Preserve unrelated, explicitly authorized blueprint diagnoses from
        # the same parallel frontier. They remain queued while the local Lean
        # implementation prerequisite takes scheduling priority.
        if authorized:
            _enqueue_phase2_repair_requests(ctx, authorized)
        if failed:
            _store_generation_feedback(
                ctx,
                failed,
                "\n\n".join(
                    f"- {label}: {evidence}" for label, evidence in failed.items()
                ),
                source="phase2_proof_frontier_parallel_failure",
                evidence_by_label=failed,
            )
        return RepairRequest(
            "Phase 2 requires deferred definition body/bodies before retrying "
            "the blocked top-down node(s). The blueprint is unchanged.",
            sorted(prerequisite_blocked),
            section_labels=sorted(prerequisite_blocked),
            authorizes_blueprint_repair=False,
            implementation_prerequisites=sorted(prerequisites),
            scheduling_only=True,
            evidence_by_label={
                label: decomposition_evidence[label]
                for label in prerequisite_blocked
            },
        )

    if authorized:
        _enqueue_phase2_repair_requests(ctx, authorized)
        if failed:
            _store_generation_feedback(
                ctx,
                failed,
                "\n\n".join(
                    f"- {label}: {evidence}" for label, evidence in failed.items()
                ),
                source="phase2_proof_frontier_parallel_failure",
                evidence_by_label=failed,
            )
        request = _pending_phase2_repair_request(ctx)
        if request is None:
            raise RuntimeError(
                "Phase 2 decomposition queue unexpectedly became empty"
            )
        return request

    if not failed:
        return None
    evidence = "\n\n".join(
        f"== Node {label} ==\n"
        f"Blueprint statement:\n{ctx.stmt_blocks.get(label, '')[:2500]}\n"
        f"Lean-generation evidence:\n{error[-3500:]}"
        for label, error in sorted(failed.items())
    )
    return RepairRequest(
        "Phase 2 body implementation did not produce accepted Lean. Retry the "
        "same frozen statements using the exact node-owned evidence below; the "
        "blueprint is unchanged.\n\n" + evidence,
        sorted(failed),
        section_labels=sorted(failed),
        authorizes_blueprint_repair=False,
        evidence_by_label=failed,
    )


def _phase2_prerequisite_request_for_repair(
    ctx: Ctx,
    sections: Iterable[Section],
    request: RepairRequest,
    *,
    source: str,
) -> RepairRequest | None:
    """Convert a misrouted blueprint repair into implementation scheduling."""
    if not bool(getattr(ctx, "phase2_started", False)):
        return None
    evidence_by_label = dict(request.evidence_by_label) or {
        label: request.evidence for label in request.labels
    }
    prerequisites, _routes = _schedule_phase2_definition_prerequisites(
        ctx,
        sections,
        request.labels,
        evidence_by_label,
        source=source,
    )
    if not prerequisites:
        return None
    return RepairRequest(
        "Phase 2 repair evidence identifies deferred definition body/bodies, "
        "so the scheduler will implement those dependencies before retrying "
        "the blocked node. The blueprint is unchanged.",
        list(request.labels),
        section_labels=list(request.section_labels),
        context_labels=list(request.context_labels),
        authorizes_blueprint_repair=False,
        implementation_prerequisites=sorted(prerequisites),
        scheduling_only=True,
        evidence_by_label=evidence_by_label,
    )


def _proof_base_round_limit(configured_batch_size: int, label_count: int) -> int:
    """Base proof rounds needed for feedback plus deterministic bisection."""
    actual_batch_size = min(
        max(1, configured_batch_size),
        max(1, label_count),
    )
    return max(2, (actual_batch_size - 1).bit_length() + 1)


def _module_decl_texts(sec: Section) -> tuple[ParsedModule, dict[str, int]]:
    parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
    index = {decl.name: i for i, decl in enumerate(parsed.decls) if decl.name}
    return parsed, index


def _write_section(sec: Section, parsed: ParsedModule) -> list[tuple[int, int]]:
    code, ranges = _compose_module(parsed.imports, parsed.preamble, [d.text for d in parsed.decls])
    sec.path.write_text(code, encoding="utf-8")
    return ranges


def _ladder_tactic(ctx: Ctx, label: str) -> str:
    node = ctx.nodes[label]
    deps = [
        _lean_name(dep)
        for dep in sorted(node.uses)
        if dep in ctx.nodes and not ctx.nodes[dep].mathlibok
    ][:8]
    statement = ctx.stmt_blocks.get(label, "")
    unmentioned = [dep for dep in deps if dep not in statement]
    simp_deps = f"(simp [{', '.join(deps)}])" if deps else "simp"
    if unmentioned:
        # The dependency contract requires these names to appear in the decl;
        # only a simp call naming them can satisfy it for a ladder proof.
        return f"by first | (simp [{', '.join(deps)}]) | (simp_all [{', '.join(deps)}])"
    return f"by first | rfl | omega | norm_num | ring | {simp_deps} | simp | aesop"


def _run_tactic_ladder(ctx: Ctx, sec: Section, sorry_labels: list[str], *, tag: str) -> list[str]:
    """Try to close sorries with zero model calls. Returns labels proved."""
    parsed, index = _module_decl_texts(sec)
    ladder_imports = [
        item for item in LADDER_IMPORTS if item not in _missing_olean_imports(LADDER_IMPORTS)
    ]
    candidates: dict[str, str] = {}
    originals: dict[str, str] = {}
    for label in sorry_labels:
        name = _lean_name(label)
        if name not in index:
            continue
        decl = parsed.decls[index[name]]
        originals[label] = decl.text
        tactic = _ladder_tactic(ctx, label)
        candidates[label] = (
            f"set_option maxHeartbeats {LADDER_HEARTBEATS} in\n"
            + _splice_proof(decl.text, tactic)
        )
    if not candidates:
        return []
    for label, text in candidates.items():
        parsed.decls[index[_lean_name(label)]].text = text
    parsed.imports = list(dict.fromkeys(parsed.imports + ladder_imports))
    ranges = _write_section(sec, parsed)
    ok, output = _check_lean(sec.path, ctx.lean_command, timeout=LEAN_CHECK_TIMEOUT)
    errors_by_decl, _file_level = ({}, []) if ok else _errors_by_decl(output, sec.file_name, ranges)
    proved: list[str] = []
    for label in list(candidates):
        idx = index[_lean_name(label)]
        if idx in errors_by_decl or (not ok and not errors_by_decl):
            parsed.decls[idx].text = originals[label]
        else:
            proved.append(label)
    if not proved:
        # Revert imports too; nothing kept from the ladder pass.
        parsed.imports = [item for item in parsed.imports if item not in set(ladder_imports)]
    _write_section(sec, parsed)
    if proved and (not ok):
        # Mixed outcome: recompile to confirm the kept subset stands alone.
        ok2, output2 = _check_lean(sec.path, ctx.lean_command)
        if not ok2:
            for label in proved:
                parsed.decls[index[_lean_name(label)]].text = originals[label]
            parsed.imports = [item for item in parsed.imports if item not in set(ladder_imports)]
            _write_section(sec, parsed)
            _log(f"ladder subset failed recompile; reverted ({output2.splitlines()[-1] if output2 else ''})", tag=tag)
            proved = []
    if proved:
        _log(f"tactic ladder closed {len(proved)}/{len(candidates)} proof(s) for free", tag=tag)
    _record(
        ctx.telemetry,
        "tactic_ladder_result",
        section=sec.number,
        labels=sorted(candidates),
        candidate_count=len(candidates),
        proved_labels=proved,
        proved_count=len(proved),
        imports=ladder_imports,
    )
    return proved


def _apply_proof_batch(
    ctx: Ctx,
    sec: Section,
    response_code: str,
    targets: dict[str, str],  # label -> frozen decl text
    *,
    tag: str,
) -> tuple[list[str], dict[str, str], dict[str, list[str]]]:
    """Splice returned bodies into the module; compile and audit survivors.

    Returns ``(implemented_labels, errors_by_label, repair_helpers_by_label)``.
    """
    parsed, index = _module_decl_texts(sec)
    try:
        model_parsed = _ingest_model_lean(
            ctx, targets.keys(), response_code
        ).parsed
    except ValueError as exc:
        return (
            [],
            {label: f"invalid Lean response structure: {exc}" for label in targets},
            {},
        )
    model_decls = {decl.name: decl for decl in model_parsed.decls if decl.name}
    new_imports = [
        item
        for item in model_parsed.imports
        if item not in _missing_olean_imports(model_parsed.imports)
    ]
    errors: dict[str, str] = {}
    repair_helpers: dict[str, list[str]] = {}
    originals: dict[str, str] = {}
    spliced: list[str] = []
    for label, frozen_text in targets.items():
        name = _lean_name(label)
        model_decl = model_decls.get(name)
        if model_decl is None:
            errors[label] = f"response omitted frozen declaration `{name}`"
            continue
        proof = _extract_by_proof(model_decl.text)
        if proof is None:
            errors[label] = (
                f"response body for `{name}` must be a tactic block introduced by `:= by`"
            )
            continue
        if re.search(r"\bsorry\b|\badmit\b", proof):
            errors[label] = f"response body for `{name}` still contains sorry/admit"
            continue
        originals[label] = parsed.decls[index[name]].text
        parsed.decls[index[name]].text = _splice_proof(frozen_text, proof)
        spliced.append(label)
    if not spliced:
        return [], errors, repair_helpers
    parsed.imports = list(dict.fromkeys(parsed.imports + new_imports))
    ranges = _write_section(sec, parsed)
    ok, output = _check_lean(sec.path, ctx.lean_command)
    if ok:
        proved = list(spliced)
    else:
        errors_by_decl, file_level = _errors_by_decl(output, sec.file_name, ranges)
        if file_level and not errors_by_decl:
            # Un-attributable failure: revert everything from this batch.
            for label in spliced:
                parsed.decls[index[_lean_name(label)]].text = originals[label]
            _write_section(sec, parsed)
            for label in spliced:
                errors[label] = "\n".join(file_level)[-4000:]
            return [], errors, repair_helpers
        proved = []
        for label in spliced:
            idx = index[_lean_name(label)]
            if idx in errors_by_decl:
                errors[label] = "\n".join(
                    errors_by_decl[idx]
                )[-4000:]
                parsed.decls[idx].text = originals[label]
            else:
                proved.append(label)
        ranges = _write_section(sec, parsed)
        if proved:
            ok2, output2 = _check_lean(sec.path, ctx.lean_command)
            if not ok2:
                for label in proved:
                    errors[label] = output2[-2000:]
                    parsed.decls[index[_lean_name(label)]].text = originals[label]
                _write_section(sec, parsed)
                proved = []
    # Dependency-mention contract: now that the proof exists, every non-Mathlib
    # `\uses` name must be visible in the finished declaration.
    if proved:
        module_code = sec.path.read_text(encoding="utf-8")
        decls = _lean_declarations(module_code)
        kept: list[str] = []
        for label in proved:
            decl = decls.get(_lean_name(label))
            missing = (
                _nonmathlib_uses_missing_from_decl(label, ctx.nodes[label], decl, ctx.nodes, decls)
                if decl is not None
                else []
            )
            if missing:
                errors[label] = (
                    "implementation compiled but does not visibly use required dependency "
                    "declaration(s): "
                    + ", ".join(f"`{_lean_name(dep)}`" for dep in missing)
                    + ". Use them instead of re-deriving inline."
                )
                parsed.decls[index[_lean_name(label)]].text = originals[label]
            else:
                kept.append(label)
        if len(kept) != len(proved):
            _write_section(sec, parsed)
            if kept:
                ok3, _out3 = _check_lean(sec.path, ctx.lean_command)
                if not ok3:
                    for label in kept:
                        parsed.decls[index[_lean_name(label)]].text = originals[label]
                        errors[label] = "kept subset failed recompile after dependency pruning"
                    _write_section(sec, parsed)
                    kept = []
        proved = kept
    semantic_body_labels = [
        label for label in proved if not _is_theorem_like_kind(ctx.nodes[label].kind)
    ]
    if semantic_body_labels:
        module_code = sec.path.read_text(encoding="utf-8")
        audit = _model_alignment_audit(
            ctx, semantic_body_labels, module_code, tag=f"{tag}-owned-body"
        )
        _record(
            ctx.telemetry,
            "definition_body_audit_result",
            section=sec.number,
            labels=semantic_body_labels,
            accepted=audit is None,
            routed_kind=audit[0] if audit is not None else "accepted",
            rejected_labels=(sorted(audit[2]) if audit is not None else []),
        )
        if audit is not None:
            kind, reason, rejected, helpers = audit
            rejected_bundles = set(semantic_body_labels) & set(rejected)
            if not rejected_bundles:
                rejected_bundles = set(semantic_body_labels)
            for label in rejected_bundles:
                errors[label] = reason
                parsed.decls[index[_lean_name(label)]].text = originals[label]
                if kind in {"blueprint", "decomposition"}:
                    repair_helpers[label] = list(helpers)
            proved = [label for label in proved if label not in rejected_bundles]
            _write_section(sec, parsed)
            if proved:
                ok4, output4 = _check_lean(sec.path, ctx.lean_command)
                if not ok4:
                    for label in proved:
                        parsed.decls[index[_lean_name(label)]].text = originals[label]
                        errors[label] = (
                            "accepted subset failed after definition-body audit rollback:\n"
                            + output4[-2000:]
                        )
                    _write_section(sec, parsed)
                    proved = []
    if proved:
        _log(f"accepted {len(proved)} implementation(s): {', '.join(proved[:6])}", tag=tag)
    return proved, errors, repair_helpers


def _prove_section(
    ctx: Ctx,
    sec: Section,
    sections: list[Section],
    requested_labels: list[str] | None = None,
) -> SectionProofOutcome:
    tag = f"S{sec.number:02d}"
    outcome = SectionProofOutcome(section=sec)
    original_source = sec.path.read_text(encoding="utf-8")
    original_compile_fingerprint = sec.compile_fingerprint
    # Per-section backend sessions (worker-thread local): implementation rounds over the
    # same file reuse the context built by earlier rounds. See _call_model.
    sessions: dict[str, str] = {}
    parsed, index = _module_decl_texts(sec)
    requested = set(requested_labels or sec.labels)
    sorry_labels = [
        label
        for label in sec.labels
        if label in requested
        and _lean_name(label) in index
        and _has_terminal_sorry(parsed.decls[index[_lean_name(label)]].text)
    ]
    if not sorry_labels:
        return outcome

    # Blueprint repairs may add proof-level `\uses` without touching statements;
    # make sure every dependency's skeleton module is imported before proving.
    needed = [m for m in _sections_for_deps(ctx, sec.labels, sections) if m != sec.module]
    new_lines = [f"import {m}" for m in needed if f"import {m}" not in parsed.imports]
    if new_lines:
        parsed.imports = list(dict.fromkeys(parsed.imports + new_lines))
        _write_section(sec, parsed)
        sec.import_modules = sorted(set(sec.import_modules) | set(needed))

    if ctx.use_ladder:
        try:
            ladder_labels = [
                label for label in sorry_labels if _is_theorem_like_kind(ctx.nodes[label].kind)
            ]
            proved = _run_tactic_ladder(ctx, sec, ladder_labels, tag=tag)
        except Exception as exc:  # noqa: BLE001 - the ladder is best-effort only
            _log(f"tactic ladder crashed ({exc}); continuing with model implementations", tag=tag)
            proved = []
        outcome.proved.extend(proved)
        _clear_retry_lifecycle(ctx, proved, stage="phase2_body")
        sorry_labels = [label for label in sorry_labels if label not in proved]

    import_modules = sec.import_modules
    remaining = list(sorry_labels)
    errors: dict[str, str] = {}
    batch_size = ctx.proof_batch
    # Enough base-tier rounds to reduce a repeatedly failing batch to
    # singletons by bisection. Derive the allowance from the work actually in
    # this section, not the configured capacity: a one-node section needs one
    # initial attempt plus one feedback-aware retry, while a real 12-node batch
    # retains enough rounds to bisect before escalation.
    max_batch_rounds = _proof_base_round_limit(batch_size, len(remaining))
    round_no = 0
    while remaining and round_no < max_batch_rounds:
        round_no += 1
        next_remaining: list[str] = []
        for i in range(0, len(remaining), batch_size):
            batch = remaining[i : i + batch_size]
            parsed, index = _module_decl_texts(sec)
            targets = {
                label: parsed.decls[index[_lean_name(label)]].text
                for label in batch
                if _lean_name(label) in index
            }
            prompt = _proof_prompt(
                ctx,
                list(targets.items()),
                sections,
                import_modules + [sec.module],
                errors={label: errors[label] for label in batch if label in errors},
                timeout_s=ctx.base_timeout,
            )
            result = _call_model(
                ctx,
                prompt,
                purpose="proof_batch",
                timeout=ctx.base_timeout,
                effort=ctx.base_effort,
                labels=batch,
                tag=tag,
                sessions=sessions,
            )
            if result.status == "timeout" and len(batch) > 1:
                route = _route_lean_generation_failure(batch)
                batch_size = min(
                    batch_size,
                    max(len(part) for part in route.parts),
                )
                next_remaining.extend(batch)
                _log(
                    "batch timed out; shared failure router reduced batch size "
                    f"to {batch_size}",
                    tag=tag,
                )
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_batch",
                    round=round_no,
                    labels=batch,
                    status="timeout_bisected",
                    proved_labels=[],
                    failed_labels=batch,
                    decomposition_labels=[],
                    next_batch_size=batch_size,
                    routing_action=route.action,
                )
                continue
            if result.status != "ok":
                route = _route_lean_generation_failure(batch)
                if route.action == "bisect":
                    batch_size = min(
                        batch_size,
                        max(len(part) for part in route.parts),
                    )
                    _log(
                        f"proof model call {result.status}; shared failure router "
                        f"reduced the next unit to {batch_size}",
                        tag=tag,
                    )
                _record(
                    ctx.telemetry,
                    "lean_generation_failure_routed",
                    stage="phase2_body",
                    action=route.action,
                    labels=batch,
                    failing_labels=list(route.failed_labels),
                    accepted_labels=list(route.accepted_labels),
                    part_sizes=[len(part) for part in route.parts],
                    round=round_no,
                    section=sec.number,
                    model_status=result.status,
                )
                next_remaining.extend(batch)
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_batch",
                    round=round_no,
                    labels=batch,
                    status=result.status,
                    proved_labels=[],
                    failed_labels=batch,
                    decomposition_labels=[],
                    error=result.error,
                    routing_action=route.action,
                    next_batch_size=batch_size,
                )
                continue
            refusal = _parse_decomposition_refusal(
                result.text, expected_labels=batch
            )
            if refusal is not None:
                refused = refusal["label"]
                outcome.decomposition[refused] = refusal["missing_helpers"]
                refusal_evidence = f"generator refusal: {refusal['reason']}"
                outcome.decomposition_evidence[refused] = refusal_evidence
                errors[refused] = refusal_evidence
                next_remaining.extend(label for label in batch if label != refused)
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_batch",
                    round=round_no,
                    labels=batch,
                    status="needs_decomposition",
                    proved_labels=[],
                    failed_labels=[label for label in batch if label != refused],
                    decomposition_labels=[refused],
                    missing_helpers={refused: refusal["missing_helpers"]},
                )
                continue
            proved, batch_errors, batch_repairs = _apply_proof_batch(
                ctx, sec, result.text, targets, tag=tag
            )
            outcome.proved.extend(proved)
            errors.update(batch_errors)
            outcome.decomposition.update(batch_repairs)
            outcome.decomposition_evidence.update(
                {
                    label: batch_errors.get(
                        label, "semantic audit requested decomposition"
                    )
                    for label in batch_repairs
                }
            )
            failed_batch = [
                label
                for label in batch
                if label not in proved and label not in batch_repairs
            ]
            local_unit = [label for label in batch if label not in batch_repairs]
            route = (
                _route_lean_generation_failure(local_unit, failed_batch)
                if failed_batch
                else None
            )
            if route is not None and route.action == "bisect":
                batch_size = min(
                    batch_size,
                    max(len(part) for part in route.parts),
                )
                _log(
                    "Lean-generation failure affected the full proof batch; "
                    f"shared router reduced the next unit to {batch_size}",
                    tag=tag,
                )
            if route is not None:
                _record(
                    ctx.telemetry,
                    "lean_generation_failure_routed",
                    stage="phase2_body",
                    action=route.action,
                    labels=local_unit,
                    failing_labels=list(route.failed_labels),
                    accepted_labels=list(route.accepted_labels),
                    part_sizes=[len(part) for part in route.parts],
                    round=round_no,
                    section=sec.number,
                )
            _record(
                ctx.telemetry,
                "proof_attempt_result",
                section=sec.number,
                phase="proof_batch",
                round=round_no,
                labels=batch,
                status=(
                    "needs_decomposition"
                    if batch_repairs and not proved and not failed_batch
                    else "partial"
                    if proved and (failed_batch or batch_repairs)
                    else "success"
                    if proved
                    else "failed"
                ),
                proved_labels=proved,
                failed_labels=failed_batch,
                decomposition_labels=sorted(batch_repairs),
                errors={label: batch_errors[label] for label in failed_batch if label in batch_errors},
                routing_action=route.action if route is not None else "accepted",
                next_batch_size=batch_size,
            )
            next_remaining.extend(
                label for label in batch if label not in proved and label not in outcome.decomposition
            )
        remaining = next_remaining

    # Escalation: only singleton calls reach the configured escalation runner.
    still: list[str] = []
    for label in remaining:
        parsed, index = _module_decl_texts(sec)
        name = _lean_name(label)
        if name not in index or not _has_terminal_sorry(parsed.decls[index[name]].text):
            continue
        if _retry_next_tier(ctx, label, "phase2_body") == "base":
            _record_retry_failure(
                ctx,
                [label],
                stage="phase2_body",
                attempted_tier="base",
                evidence=errors.get(label, "base proof generation did not close the body"),
                source="proof_batch_residue",
            )
        solved = False
        for attempt in range(1, PROOF_SINGLETON_RETRIES + 1):
            targets = {label: parsed.decls[index[name]].text}
            prompt = _proof_prompt(
                ctx,
                list(targets.items()),
                sections,
                import_modules + [sec.module],
                errors={label: errors[label]} if label in errors else None,
                singleton=True,
                timeout_s=ctx.hard_timeout,
            )
            result = _call_model(
                ctx,
                prompt,
                purpose="proof_singleton",
                timeout=ctx.hard_timeout,
                effort=ctx.escalation_effort,
                labels=[label],
                escalated=True,
                tag=tag,
                sessions=sessions,
            )
            if result.status != "ok":
                _record_retry_failure(
                    ctx,
                    [label],
                    stage="phase2_body",
                    attempted_tier="escalation",
                    evidence=result.error or result.status,
                    source="proof_singleton_model_call",
                )
                errors.setdefault(
                    label,
                    f"escalated implementation call {result.status}: {result.error[:400]}",
                )
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_singleton",
                    attempt=attempt,
                    labels=[label],
                    status=result.status,
                    proved_labels=[],
                    failed_labels=[label],
                    decomposition_labels=[],
                    error=result.error,
                )
                continue
            refusal = _parse_decomposition_refusal(
                result.text, expected_labels={label}
            )
            if refusal is not None:
                outcome.decomposition[label] = refusal["missing_helpers"]
                refusal_evidence = f"generator refusal: {refusal['reason']}"
                outcome.decomposition_evidence[label] = refusal_evidence
                errors[label] = refusal_evidence
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_singleton",
                    attempt=attempt,
                    labels=[label],
                    status="needs_decomposition",
                    proved_labels=[],
                    failed_labels=[],
                    decomposition_labels=[label],
                    missing_helpers={label: refusal["missing_helpers"]},
                )
                break
            proved, batch_errors, batch_repairs = _apply_proof_batch(
                ctx, sec, result.text, targets, tag=tag
            )
            errors.update(batch_errors)
            outcome.decomposition.update(batch_repairs)
            outcome.decomposition_evidence.update(
                {
                    repair_label: batch_errors.get(
                        repair_label, "semantic audit requested decomposition"
                    )
                    for repair_label in batch_repairs
                }
            )
            if batch_repairs:
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_singleton",
                    attempt=attempt,
                    labels=[label],
                    status="needs_decomposition",
                    proved_labels=[],
                    failed_labels=[],
                    decomposition_labels=sorted(batch_repairs),
                    missing_helpers=batch_repairs,
                )
                break
            if proved:
                outcome.proved.extend(proved)
                _clear_retry_lifecycle(ctx, proved, stage="phase2_body")
                solved = True
                _record(
                    ctx.telemetry,
                    "proof_attempt_result",
                    section=sec.number,
                    phase="proof_singleton",
                    attempt=attempt,
                    labels=[label],
                    status="success",
                    proved_labels=proved,
                    failed_labels=[],
                    decomposition_labels=[],
                )
                break
            _record(
                ctx.telemetry,
                "proof_attempt_result",
                section=sec.number,
                phase="proof_singleton",
                attempt=attempt,
                labels=[label],
                status="failed",
                proved_labels=[],
                failed_labels=[label],
                decomposition_labels=[],
                errors={label: batch_errors.get(label, errors.get(label, ""))},
            )
            _record_retry_failure(
                ctx,
                [label],
                stage="phase2_body",
                attempted_tier="escalation",
                evidence=batch_errors.get(label, errors.get(label, "proof rejected")),
                source="proof_singleton_validation",
            )
            parsed, index = _module_decl_texts(sec)
        if not solved and label not in outcome.decomposition:
            still.append(label)

    for label in still:
        outcome.failed[label] = errors.get(
            label, "no implementation found within the configured budgets"
        )
    _record(
        ctx.telemetry,
        "proof_section_result",
        section=sec.number,
        labels=sec.labels,
        proved_labels=outcome.proved,
        failed_labels=sorted(outcome.failed),
        decomposition_labels=sorted(outcome.decomposition),
        proved_count=len(outcome.proved),
        failed_count=len(outcome.failed),
        decomposition_count=len(outcome.decomposition),
    )
    _persist_phase2_section_outcome(
        ctx,
        outcome,
        sections,
        original_source=original_source,
        original_compile_fingerprint=original_compile_fingerprint,
    )
    return outcome
