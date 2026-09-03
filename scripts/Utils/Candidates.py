"""Phase-1/Phase-2 candidate state machines and the retry lifecycle.

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


def _prune_stale_generation_candidates(ctx: Ctx) -> set[str]:
    """Drop candidate Lean that no longer matches its statement or plan."""
    with _STATE_LOCK:
        candidates = getattr(ctx, "generation_candidates", {})
        stale = {
            label
            for label, entry in candidates.items()
            if label not in ctx.nodes
            or entry.get("statement_fp") != ctx.stmt_fps.get(label)
            or str(entry.get("plan_fp") or "")
            != _candidate_plan_fingerprint(ctx, label)
        }
        for label in stale:
            candidates.pop(label, None)
    telemetry = getattr(ctx, "telemetry", None)
    if stale and telemetry is not None:
        _record(
            telemetry,
            "phase1_retry_candidate_invalidated",
            labels=sorted(stale),
            reason="statement_fingerprint_changed",
        )
    return stale


def _candidate_plan_fingerprint(ctx: Ctx, label: str) -> str:
    """Fingerprint the exact untrusted plan contract used for generation."""
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label)
    direct = (getattr(ctx, "blueprint_direct_generation", {}) or {}).get(label)
    statement_fps = getattr(ctx, "stmt_fps", {}) or {}
    if isinstance(direct, dict) and str(direct.get("statement_fp") or "") == (
        statement_fps.get(label) or ""
    ):
        return hashlib.sha256(
            json.dumps(
                {
                    "mode": "blueprint_direct",
                    "statement_fp": str(direct.get("statement_fp") or ""),
                    "evidence": str(direct.get("evidence") or ""),
                },
                sort_keys=True,
            ).encode("utf-8")
        ).hexdigest()
    if not isinstance(entry, dict):
        return ""
    material = {
        "schema_version": int(entry.get("schema_version") or 0),
        "target_signature": str(entry.get("target_signature") or ""),
        "helpers": entry.get("helpers") or [],
        "decisions": entry.get("decisions") or [],
    }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _design_plan_public_surface_fingerprint(entry: Mapping[str, Any] | None) -> str:
    """Fingerprint the public Lean surface exposed by one plan entry.

    Decisions and prose are deliberately excluded. Downstream nodes can depend
    only on declaration headers, helper declarations, and typed helper members.
    """
    if not isinstance(entry, Mapping):
        return ""
    try:
        fragments = _design_plan_public_interface_fragments(dict(entry))
    except (TypeError, ValueError):
        return ""
    if not fragments:
        return ""
    return hashlib.sha256(
        json.dumps(fragments, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _candidate_is_reusable_uncompiled(entry: dict[str, Any]) -> bool:
    """Recognize candidates that completed every deterministic generation gate.

    Older state wrote valid siblings from an incomplete layer transaction with
    the reuse bit unset. Their source is unambiguous: the failing future never
    enters the sibling list stored by the transaction.

    Deterministic validity permits the first compilation attempt; it does not
    permit zero-call reuse after Lean has rejected that exact candidate. The
    failed code remains stored as revision context for the next model call.
    """
    if str(entry.get("lean_status") or "unknown") == "failed":
        return False
    if bool(entry.get("reusable_uncompiled")):
        return True
    return bool(
        re.fullmatch(
            r"phase1_layer_\d+_incomplete_generation",
            str(entry.get("source") or ""),
        )
    )


def _candidate_hash(code: str) -> str:
    return hashlib.sha256(code.strip().encode("utf-8")).hexdigest()


def _phase2_node_candidate_epoch(ctx: Ctx, label: str) -> str:
    """Fingerprint the complete blueprint/dependency contract for one node."""
    material = {
        "label": label,
        "statement_fp": str(getattr(ctx, "stmt_fps", {}).get(label) or ""),
        "contract_fp": str(getattr(ctx, "contract_fps", {}).get(label) or ""),
        "dependency_context_fp": _phase2_repair_context_fingerprint(
            ctx, [label]
        ),
    }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def _prune_stale_phase2_node_candidates(ctx: Ctx) -> set[str]:
    """Discard complete-node candidates after their blueprint epoch changes."""
    with _STATE_LOCK:
        candidates = getattr(ctx, "phase2_node_candidates", {})
        stale = {
            label
            for label, entry in candidates.items()
            if label not in getattr(ctx, "nodes", {})
            or str(entry.get("epoch") or "")
            != _phase2_node_candidate_epoch(ctx, label)
        }
        for label in stale:
            candidates.pop(label, None)
    telemetry = getattr(ctx, "telemetry", None)
    if stale and telemetry is not None:
        _record(
            telemetry,
            "phase2_complete_candidate_invalidated",
            labels=sorted(stale),
            reason="blueprint_or_dependency_contract_changed",
        )
    return stale


def _phase2_node_candidate(ctx: Ctx, label: str) -> dict[str, Any] | None:
    """Return a copy of the current complete-node correction seed."""
    _prune_stale_phase2_node_candidates(ctx)
    with _STATE_LOCK:
        entry = copy.deepcopy(
            getattr(ctx, "phase2_node_candidates", {}).get(label)
        )
    return entry if isinstance(entry, dict) else None


def _store_phase2_node_candidate(
    ctx: Ctx,
    label: str,
    code: str,
    *,
    evidence: str,
    failure_kind: str,
    tier: str,
    source: str,
    failure_identity: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Persist one exact statement+body candidate and its current rejection.

    The latest candidate is correction state, not accepted Lean.  Previously
    seen candidate/failure pairs remain as compact fingerprints so a later
    outer retry cannot pay for the same no-progress exchange again.
    """
    candidate_hash = _candidate_hash(code)
    evidence = evidence.strip()[-12000:]
    canonical_identity = _canonical_failure_identity(dict(failure_identity or {}))
    failure_hash = _diagnostic_failure_signature(
        kind=failure_kind,
        text=evidence,
        identity=canonical_identity,
    )
    with _STATE_LOCK:
        candidates = getattr(ctx, "phase2_node_candidates", None)
        if candidates is None:
            candidates = {}
            ctx.phase2_node_candidates = candidates
        previous = candidates.get(label) or {}
        seen = [
            str(item)
            for item in previous.get("seen_states") or []
            if str(item)
        ]
        state_hash = hashlib.sha256(
            (candidate_hash + "\0" + failure_hash).encode("utf-8")
        ).hexdigest()
        repeated = state_hash in seen
        if not repeated:
            seen.append(state_hash)
        entry = {
            "epoch": _phase2_node_candidate_epoch(ctx, label),
            "code": code[:60000],
            "candidate_hash": candidate_hash,
            "evidence": evidence,
            "failure_kind": failure_kind,
            "failure_hash": failure_hash,
            "failure_identity": canonical_identity,
            "tier": tier,
            "source": source,
            "revision": int(previous.get("revision") or 0) + 1,
            "seen_states": seen[-24:],
            "attempted_corrections": [
                str(item)
                for item in previous.get("attempted_corrections") or []
                if str(item)
            ][-24:],
            "repeated_state": repeated,
        }
        candidates[label] = entry
    if failure_kind == "semantic_alignment":
        _record_diagnostic_evidence(
            ctx,
            label,
            evidence,
            source=f"{source}:semantic",
            kind="semantic",
            lifetime="statement",
            failure_identity=canonical_identity,
        )
    else:
        diagnostic_kind = (
            "compiler"
            if failure_kind
            in {"lean_compile", "object_compile", "implementation_object"}
            else "deterministic"
        )
        _record_diagnostic_evidence(
            ctx,
            label,
            evidence,
            source=f"{source}:{diagnostic_kind}",
            kind=diagnostic_kind,
            lifetime="candidate",
            candidate_fp=candidate_hash,
            failure_identity=canonical_identity,
        )
    _record(
        ctx.telemetry,
        "phase2_complete_candidate_saved",
        label=label,
        source=source,
        tier=tier,
        failure_kind=failure_kind,
        candidate_sha256=candidate_hash,
        failure_sha256=failure_hash,
        revision=entry["revision"],
        repeated_state=repeated,
    )
    return copy.deepcopy(entry)


def _note_phase2_candidate_correction(
    ctx: Ctx, label: str, correction_fingerprint: str
) -> None:
    with _STATE_LOCK:
        entry = getattr(ctx, "phase2_node_candidates", {}).get(label)
        if not isinstance(entry, dict):
            return
        attempted = [
            str(item) for item in entry.get("attempted_corrections") or []
        ]
        if correction_fingerprint not in attempted:
            attempted.append(correction_fingerprint)
        entry["attempted_corrections"] = attempted[-24:]


def _clear_phase2_node_candidate(ctx: Ctx, label: str) -> None:
    with _STATE_LOCK:
        getattr(ctx, "phase2_node_candidates", {}).pop(label, None)
    _prune_stale_diagnostic_evidence(ctx)
    _sync_generation_feedback_projection(ctx)


def _finding_obligation_ids(finding: SkeletonFinding) -> set[str]:
    """Map a human-readable deterministic finding to stable obligation IDs.

    Existing deterministic audits remain the source of truth.  This adapter
    only gives their findings stable identities so two candidate revisions can
    be compared without relying on a paper-specific score or model judgment.
    """
    label = finding.label or "file"
    message = " ".join(finding.message.split())
    lower = message.lower()
    symbols = re.findall(r"`([^`]+)`", message)
    category = finding.category or ""

    if finding.dependencies:
        family = category or (
            "outside_dependency_closure"
            if "outside" in lower
            else "required_dependency"
        )
        return {
            f"{label}:{family}:{dependency}"
            for dependency in finding.dependencies
        }
    if "missing generated declaration" in lower:
        return {f"{label}:target_present:{finding.lean_name or label}"}
    if "is a definition but generated" in lower or (
        "is theorem-like but generated" in lower
    ):
        return {f"{label}:target_kind:{finding.lean_name or label}"}
    if "omitted helper" in lower:
        helper = symbols[0] if symbols else (finding.lean_name or "unknown")
        return {f"{label}:helper_present:{helper}"}
    if "helper" in lower and "must be a" in lower:
        helper = symbols[0] if symbols else (finding.lean_name or "unknown")
        return {f"{label}:helper_kind:{helper}"}
    if "omits required member" in lower:
        helper = symbols[0] if symbols else (finding.lean_name or "unknown")
        members = symbols[1:] or ["unknown"]
        return {f"{label}:helper_member:{helper}:{member}" for member in members}
    if "does not mention required dependency" in lower:
        return {
            f"{label}:required_dependency:{symbol}"
            for symbol in (symbols or ["unknown"])
        }
    if "cycle" in lower:
        return {
            f"{label}:declaration_cycle:{symbol}"
            for symbol in (symbols or [finding.lean_name or "unknown"])
        }

    family = category or re.sub(r"[^a-z0-9]+", "_", lower).strip("_")[:120]
    if symbols:
        return {f"{label}:{family}:{symbol}" for symbol in symbols}
    return {f"{label}:{family or 'deterministic_finding'}"}


def _candidate_obligation_universe(ctx: Ctx, labels: Iterable[str]) -> set[str]:
    """Return the provider-neutral deterministic contract surface for labels."""
    obligations = {
        "file:no_forbidden_placeholder",
        "file:no_top_level_assumption",
        "file:no_invented_blueprint_stub",
        "file:canonical_module_structure",
        "file:no_unplanned_declaration",
        "file:no_declaration_cycle",
        "file:phase1_body_policy",
    }
    plan_entries = getattr(ctx, "design_plan_entries", {}) or {}
    nodes = getattr(ctx, "nodes", {}) or {}
    for label in labels:
        node = nodes.get(label)
        if node is None:
            continue
        target = _lean_name(label)
        obligations.update(
            {
                f"{label}:target_present:{target}",
                f"{label}:target_kind:{target}",
            }
        )
        for dependency in sorted(_statement_uses(node)):
            dependency_node = nodes.get(dependency)
            if dependency_node is not None and not dependency_node.mathlibok:
                obligations.add(
                    f"{label}:required_dependency:{_lean_name(dependency)}"
                )
        for helper in (plan_entries.get(label) or {}).get("helpers") or []:
            helper_name = str(helper.get("name") or "").strip()
            if not helper_name:
                continue
            obligations.add(f"{label}:helper_present:{helper_name}")
            obligations.add(f"{label}:helper_kind:{helper_name}")
            for member in helper.get("required_members") or []:
                obligations.add(
                    f"{label}:helper_member:{helper_name}:{str(member)}"
                )
            for member in helper.get("members") or []:
                if isinstance(member, dict) and str(member.get("name") or "").strip():
                    obligations.add(
                        f"{label}:helper_member:{helper_name}:"
                        f"{str(member.get('name'))}"
                    )
    return obligations


def _evaluate_phase1_candidate(
    ctx: Ctx, labels: list[str], code: str
) -> tuple[set[str], set[str], list[SkeletonFinding]]:
    """Run the complete existing deterministic Phase-1 gate on a candidate."""
    target_kinds = _phase1_target_kinds(
        ctx, (label for label in labels if label in ctx.nodes)
    )
    label_by_name = {_lean_name(label): label for label in labels}
    try:
        findings = _skeleton_code_findings(
            code,
            target_kinds,
            label_by_name,
            _planned_helper_owner_by_name(ctx, labels),
        )
        findings += _skeleton_deterministic_findings(code, ctx, labels)
    except (TypeError, ValueError) as exc:
        findings = [
            SkeletonFinding(
                f"candidate could not be canonically evaluated: {exc}",
                category="canonical_ingest",
            )
        ]
    violations = {
        obligation
        for finding in findings
        for obligation in _finding_obligation_ids(finding)
    }
    universe = _candidate_obligation_universe(ctx, labels) | violations
    return universe, violations, findings


def _lean_error_count(output: str) -> int:
    count = len(re.findall(r"(?m):\d+:\d+:\s*error:", output))
    if count:
        return count
    return 1 if output.strip() else 0


def _candidate_transition_decision(
    previous: dict[str, Any] | None,
    proposed: dict[str, Any],
) -> tuple[bool, str, set[str], set[str]]:
    """Decide whether proposed code advances the same statement/plan epoch."""
    if not previous:
        return True, "initial_candidate", set(), set(
            proposed.get("deterministic_violations") or []
        )
    old_hash = str(previous.get("candidate_hash") or _candidate_hash(str(previous.get("code") or "")))
    new_hash = str(proposed.get("candidate_hash") or "")
    old_violations = set(previous.get("deterministic_violations") or [])
    new_violations = set(proposed.get("deterministic_violations") or [])
    regressed = new_violations - old_violations
    improved = old_violations - new_violations
    if old_hash == new_hash:
        return True, "same_candidate_evidence", regressed, improved
    if regressed:
        return False, "deterministic_regression", regressed, improved
    if improved:
        return True, "deterministic_progress", regressed, improved

    # A compiling candidate that failed semantic alignment is not a valid
    # rollback point. Once exact critic feedback has forced generation of a
    # different deterministic-clean interface, let that revision become the
    # candidate under evaluation even before it has compiled. Otherwise the
    # old candidate's ``lean_status == passed`` permanently dominates every
    # alternative with ``lean_status == unknown`` and the retry loop keeps
    # regenerating corrections that can never reach compilation/audit.
    if (
        previous.get("semantic_status") == "rejected"
        and new_hash != old_hash
        and not new_violations
    ):
        return True, "semantic_rejection_revision", regressed, improved

    old_lean = str(previous.get("lean_status") or "unknown")
    new_lean = str(proposed.get("lean_status") or "unknown")
    if new_lean == "passed" and old_lean != "passed":
        return True, "lean_progress", regressed, improved
    if new_lean == old_lean == "failed":
        old_count = int(previous.get("lean_error_count") or 0)
        new_count = int(proposed.get("lean_error_count") or 0)
        if new_count and (not old_count or new_count < old_count):
            return True, "lean_error_reduction", regressed, improved
    if (
        proposed.get("repair_stage") == "semantic_corrected"
        and previous.get("semantic_status") == "rejected"
    ):
        return True, "semantic_correction_candidate", regressed, improved
    return False, "no_measurable_progress", regressed, improved


def _upgrade_candidate_entry(
    ctx: Ctx, labels: list[str], entry: dict[str, Any]
) -> dict[str, Any]:
    """Lazily add monotonic-state fields to pre-migration candidate entries."""
    if int(entry.get("candidate_state_version") or 0) != 1:
        code, _ = _compose_module(
            [str(item) for item in entry.get("imports") or []],
            [str(item) for item in entry.get("preamble") or []],
            [str(entry.get("code") or "")],
        )
        obligations, violations, findings = _evaluate_phase1_candidate(
            ctx, labels, code
        )
        entry["deterministic_obligations"] = sorted(obligations)
        entry["satisfied_obligations"] = sorted(obligations - violations)
        entry["deterministic_violations"] = sorted(violations)
        entry["deterministic_findings"] = [
            finding.message[-4000:] for finding in findings
        ]
        entry["candidate_state_version"] = 1
    entry.setdefault("candidate_hash", _candidate_hash(str(entry.get("code") or "")))
    entry.setdefault("lean_status", "unknown")
    entry.setdefault("lean_output", "")
    entry.setdefault("lean_output_sha256", "")
    entry.setdefault("lean_error_count", 0)
    entry.setdefault("semantic_status", "unknown")
    entry.setdefault("semantic_evidence", "")
    entry.setdefault("semantic_evidence_sha256", "")
    entry.setdefault("base_attempted", entry.get("generation_tier") == "base")
    entry.setdefault(
        "escalation_attempted", entry.get("generation_tier") == "escalation"
    )
    entry.setdefault("revision", 1)
    entry.setdefault("rejected_transitions", [])
    entry.setdefault("working_candidate", {})
    return entry


def _working_candidate_payload(proposed: dict[str, Any]) -> dict[str, Any]:
    """Persist a deterministic-clean compiler intermediate separately.

    The monotonic candidate remains the rollback point. A compiler transaction
    may nevertheless need several valid rewrites before Lean's error count
    decreases. Keeping that intermediate in a separate slot lets the next
    correction continue from the latest diagnostics without pretending the
    intermediate is already the best candidate.
    """
    return {
        key: copy.deepcopy(proposed.get(key))
        for key in (
            "code",
            "candidate_hash",
            "source",
            "generation_tier",
            "repair_stage",
            "imports",
            "preamble",
            "component_labels",
            "required_dependencies",
            "deterministic_obligations",
            "satisfied_obligations",
            "deterministic_violations",
            "deterministic_findings",
            "lean_status",
            "lean_output",
            "lean_output_sha256",
            "lean_error_count",
            "semantic_status",
            "semantic_evidence",
            "semantic_evidence_sha256",
        )
    }


def _may_retain_working_candidate(
    *,
    source: str,
    proposed: dict[str, Any],
    accepted_as_best: bool,
    regressed: set[str],
) -> bool:
    """Whether a non-best proposal is a usable compiler transaction step."""
    return bool(
        not accepted_as_best
        and not regressed
        and proposed.get("lean_status") == "failed"
        and "compile" in source
        and str(proposed.get("code") or "").strip()
    )


def _store_generation_candidates(
    ctx: Ctx,
    labels: Iterable[str],
    code: str,
    *,
    source: str,
    all_labels: Iterable[str] | None = None,
    reusable_uncompiled: bool = False,
    generation_tier: str = "base",
    repair_stage: str = "generated",
    required_dependencies: dict[str, set[str]] | None = None,
    lean_status: str = "unknown",
    lean_output: str = "",
    semantic_status: str = "unknown",
    semantic_evidence: str = "",
    semantic_evidence_by_label: Mapping[str, str] | None = None,
    semantic_evidence_identity_by_label: Mapping[
        str, Mapping[str, Any]
    ] | None = None,
    expected_plan_fps: Mapping[str, str] | None = None,
) -> list[str]:
    """Retain only monotonic candidate improvements for the current epoch.

    Local helper declarations are assigned using the same ownership rule as
    routed-section salvage: a helper belongs to the next generated target.
    A proposed replacement is evaluated by the complete deterministic Phase-1
    gate before it can replace the best stored candidate. Shared-helper
    components move atomically. A deterministic regression remains evidence
    only. A deterministic-clean compiler intermediate is retained separately
    as the live correction transaction, while the best candidate remains the
    rollback point until that transaction makes measurable progress.
    """
    try:
        parsed = _parse_module(code)
    except (TypeError, ValueError):
        return []
    statement_fps = getattr(ctx, "stmt_fps", {})
    requested = [
        label for label in labels if label in ctx.nodes and statement_fps.get(label)
    ]
    all_label_list = [
        label
        for label in (all_labels if all_labels is not None else requested)
        if label in ctx.nodes
    ]
    target_names = {_lean_name(label) for label in all_label_list}
    label_by_name = {_lean_name(label): label for label in all_label_list}
    helper_owners = _planned_helper_owner_by_name(ctx, all_label_list)
    components = _target_components_from_helpers(
        parsed, label_by_name, helper_owners
    )
    component_for = {
        label: component
        for component in components
        for label in component
    }
    stored: list[str] = []
    handled: set[str] = set()
    requested_set = set(requested)
    for label in requested:
        if label in handled:
            continue
        component = component_for.get(label, {label})
        # A shared helper makes the complete component the unit of persistence.
        # Never save a fragment that cannot later be imported independently.
        if not component <= requested_set:
            continue
        component_labels = [item for item in all_label_list if item in component]
        stale_epoch = {
            component_label: {
                "generated": str(
                    (expected_plan_fps or {}).get(component_label) or ""
                ),
                "current": _candidate_plan_fingerprint(ctx, component_label),
            }
            for component_label in component_labels
            if expected_plan_fps is not None
            and str((expected_plan_fps or {}).get(component_label) or "")
            != _candidate_plan_fingerprint(ctx, component_label)
        }
        if stale_epoch:
            handled.update(component_labels)
            telemetry = getattr(ctx, "telemetry", None)
            if telemetry is not None:
                _record(
                    telemetry,
                    "phase1_retry_candidate_epoch_rejected",
                    labels=component_labels,
                    source=source,
                    plan_fps=stale_epoch,
                    reason="strategy_or_contract_changed_after_generation",
                )
            continue
        pieces = _delivered_decl_texts(
            parsed, component_labels, target_names, helper_owners
        )
        if not pieces:
            continue
        candidate = "\n\n".join(pieces).strip()
        if not candidate:
            continue
        candidate_code, _ = _compose_module(
            parsed.imports, parsed.preamble, pieces
        )
        component_semantic_evidence = semantic_evidence
        if semantic_evidence_by_label is not None:
            component_semantic_evidence = "\n\n".join(
                str(semantic_evidence_by_label.get(component_label) or "").strip()
                for component_label in component_labels
                if str(
                    semantic_evidence_by_label.get(component_label) or ""
                ).strip()
            )
        component_semantic_identity = {
            component_label: semantic_evidence_identity_by_label[component_label]
            for component_label in component_labels
            if semantic_evidence_identity_by_label is not None
            and component_label in semantic_evidence_identity_by_label
        }
        obligations, violations, findings = _evaluate_phase1_candidate(
            ctx, component_labels, candidate_code
        )
        candidate_hash = _candidate_hash(candidate)
        proposed = {
            "candidate_state_version": 1,
            "statement_fp": statement_fps[component_labels[0]],
            "plan_fp": _candidate_plan_fingerprint(ctx, component_labels[0]),
            "code": candidate[:45000],
            "candidate_hash": candidate_hash,
            "source": source,
            "reusable_uncompiled": bool(reusable_uncompiled),
            "generation_tier": (
                generation_tier
                if generation_tier in {"base", "escalation"}
                else "base"
            ),
            "repair_stage": repair_stage,
            "imports": list(parsed.imports),
            "preamble": list(parsed.preamble),
            "component_labels": list(component_labels),
            "required_dependencies": [],
            "deterministic_obligations": sorted(obligations),
            "satisfied_obligations": sorted(obligations - violations),
            "deterministic_violations": sorted(violations),
            "deterministic_findings": [
                finding.message[-4000:] for finding in findings
            ],
            "lean_status": lean_status,
            "lean_output": lean_output[-12000:],
            "lean_output_sha256": (
                hashlib.sha256(lean_output.encode("utf-8")).hexdigest()
                if lean_output
                else ""
            ),
            "lean_error_count": (
                _lean_error_count(lean_output) if lean_status == "failed" else 0
            ),
            "semantic_status": semantic_status,
            "semantic_evidence": component_semantic_evidence[-12000:],
            "semantic_evidence_sha256": (
                _diagnostic_failure_signature(
                    kind="semantic",
                    text=component_semantic_evidence,
                    identity=(
                        {"labels": component_semantic_identity}
                        if component_semantic_identity
                        else None
                    ),
                )
                if component_semantic_evidence
                else ""
            ),
            "base_attempted": generation_tier == "base",
            "escalation_attempted": generation_tier == "escalation",
            "revision": 1,
        }
        with _STATE_LOCK:
            candidates = getattr(ctx, "generation_candidates", None)
            if candidates is None:
                candidates = {}
                ctx.generation_candidates = candidates
            previous_entries = [
                (
                    _upgrade_candidate_entry(
                        ctx,
                        list(
                            (candidates.get(component_label) or {}).get(
                                "component_labels"
                            )
                            or [component_label]
                        ),
                        candidates[component_label],
                    )
                    if isinstance(candidates.get(component_label), dict)
                    else None
                )
                for component_label in component_labels
            ]
            decisions = [
                _candidate_transition_decision(previous, proposed)
                for previous in previous_entries
            ]
            accepted = all(decision[0] for decision in decisions)
            reasons = sorted({decision[1] for decision in decisions})
            regressed = set().union(*(decision[2] for decision in decisions))
            improved = set().union(*(decision[3] for decision in decisions))
            parent_hashes = sorted(
                {
                    str(entry.get("candidate_hash") or _candidate_hash(str(entry.get("code") or "")))
                    for entry in previous_entries
                    if isinstance(entry, dict) and str(entry.get("code") or "").strip()
                }
            )
            accepted_as_working = _may_retain_working_candidate(
                source=source,
                proposed=proposed,
                accepted_as_best=accepted,
                regressed=regressed,
            )
            if accepted:
                revision = max(
                    [int(entry.get("revision") or 0) for entry in previous_entries if isinstance(entry, dict)]
                    or [0]
                ) + (0 if reasons == ["same_candidate_evidence"] else 1)
                for component_label in component_labels:
                    previous = candidates.get(component_label) or {}
                    entry = dict(proposed)
                    label_semantic_evidence = (
                        str(
                            (semantic_evidence_by_label or {}).get(
                                component_label
                            )
                            or ""
                        ).strip()[-12000:]
                        if semantic_evidence_by_label is not None
                        else component_semantic_evidence[-12000:]
                    )
                    entry.update(
                        {
                            "statement_fp": statement_fps[component_label],
                            "plan_fp": _candidate_plan_fingerprint(
                                ctx, component_label
                            ),
                            "required_dependencies": sorted(
                                set(
                                    (required_dependencies or {}).get(
                                        component_label, set()
                                    )
                                )
                            ),
                            "base_attempted": bool(previous.get("base_attempted"))
                            or generation_tier == "base",
                            "escalation_attempted": bool(
                                previous.get("escalation_attempted")
                            )
                            or generation_tier == "escalation",
                            "revision": revision,
                            "semantic_evidence": label_semantic_evidence,
                            "semantic_evidence_sha256": (
                                _diagnostic_failure_signature(
                                    kind="semantic",
                                    text=label_semantic_evidence,
                                    identity=(
                                        semantic_evidence_identity_by_label.get(
                                            component_label
                                        )
                                        if semantic_evidence_identity_by_label
                                        is not None
                                        else None
                                    ),
                                )
                                if label_semantic_evidence
                                else ""
                            ),
                        }
                    )
                    if reasons == ["same_candidate_evidence"]:
                        entry["reusable_uncompiled"] = bool(
                            previous.get("reusable_uncompiled")
                        ) or bool(reusable_uncompiled)
                        entry["lean_status"] = (
                            lean_status
                            if lean_status != "unknown"
                            else str(previous.get("lean_status") or "unknown")
                        )
                        entry["lean_output"] = (
                            lean_output[-12000:]
                            if lean_output
                            else str(previous.get("lean_output") or "")
                        )
                        entry["lean_output_sha256"] = (
                            proposed["lean_output_sha256"]
                            or str(previous.get("lean_output_sha256") or "")
                        )
                        entry["lean_error_count"] = (
                            proposed["lean_error_count"]
                            or int(previous.get("lean_error_count") or 0)
                        )
                        # A deterministic-clean candidate is reusable only up
                        # to its first Lean check. Preserve failed code and
                        # diagnostics as the next revision seed, but never let
                        # the same bytes bypass model correction indefinitely.
                        if entry["lean_status"] == "failed":
                            entry["reusable_uncompiled"] = False
                        entry["semantic_status"] = (
                            semantic_status
                            if semantic_status != "unknown"
                            else str(previous.get("semantic_status") or "unknown")
                        )
                        entry["semantic_evidence"] = (
                            label_semantic_evidence
                            if label_semantic_evidence
                            else str(previous.get("semantic_evidence") or "")
                        )
                        entry["semantic_evidence_sha256"] = (
                            entry["semantic_evidence_sha256"]
                            or str(
                                previous.get("semantic_evidence_sha256") or ""
                            )
                        )
                    # Promotion completes the local correction transaction.
                    # Any older intermediate must not survive beside the new
                    # monotonic best.
                    entry["working_candidate"] = {}
                    candidates[component_label] = entry
                    stored.append(component_label)
                    handled.add(component_label)
            else:
                # A deterministic regression remains evidence only. A clean
                # compiler intermediate may be the next transaction seed, but
                # it stays separate from the monotonic best and cannot freeze.
                for component_label in component_labels:
                    previous = candidates.get(component_label)
                    if not isinstance(previous, dict):
                        continue
                    previous["base_attempted"] = bool(previous.get("base_attempted")) or generation_tier == "base"
                    previous["escalation_attempted"] = bool(previous.get("escalation_attempted")) or generation_tier == "escalation"
                    history = list(previous.get("rejected_transitions") or [])
                    history.append(
                        {
                            "candidate_hash": candidate_hash,
                            "source": source,
                            "reason": ",".join(reasons),
                            "regressed": sorted(regressed),
                            "improved": sorted(improved),
                            "lean_status": lean_status,
                            "lean_output_sha256": proposed["lean_output_sha256"],
                            "semantic_status": semantic_status,
                            "semantic_evidence_sha256": proposed[
                                "semantic_evidence_sha256"
                            ],
                        }
                    )
                    previous["rejected_transitions"] = history[-12:]
                    if accepted_as_working:
                        previous["working_candidate"] = (
                            _working_candidate_payload(proposed)
                        )
                    stored.append(component_label)
                    handled.add(component_label)
                if not accepted_as_working:
                    regression_evidence = (
                        "A proposed Phase 1 candidate was not installed because it did "
                        "not improve the retained candidate. Continue by editing the "
                        "retained candidate and preserve all of its satisfied "
                        "obligations.\n"
                        f"Decision: {', '.join(reasons)}\n"
                        "Regressed obligations: "
                        + (", ".join(sorted(regressed)) or "none")
                        + "\nRemaining proposed violations:\n"
                        + (_format_skeleton_findings(findings) or "none")
                    )
                    # Keep the retained candidate and the reason it was
                    # retained in one state transaction. A parallel worker may
                    # not observe the new candidate epoch without its feedback.
                    _store_generation_feedback(
                        ctx,
                        component_labels,
                        regression_evidence[-12000:],
                        source="candidate_regression",
                    )

        # Candidate persistence is the authoritative point where mechanical
        # diagnostics acquire an exact candidate lifetime. Semantic rejection
        # remains tied to the unchanged blueprint statement. Higher-level
        # handlers may repeat these strings, but the ledger cannot broaden
        # their scope.
        if semantic_status == "rejected" and component_semantic_evidence.strip():
            for component_label in component_labels:
                label_evidence = (
                    str(
                        (semantic_evidence_by_label or {}).get(component_label)
                        or ""
                    ).strip()
                    if semantic_evidence_by_label is not None
                    else component_semantic_evidence.strip()
                )
                if label_evidence:
                    _record_diagnostic_evidence(
                        ctx,
                        component_label,
                        label_evidence,
                        source=f"{source}:semantic",
                        kind="semantic",
                        lifetime="statement",
                        failure_identity=(
                            semantic_evidence_identity_by_label.get(
                                component_label
                            )
                            if semantic_evidence_identity_by_label is not None
                            else None
                        ),
                    )
        if (
            lean_status == "failed"
            and lean_output.strip()
            and (accepted or accepted_as_working)
        ):
            for component_label in component_labels:
                _record_diagnostic_evidence(
                    ctx,
                    component_label,
                    lean_output,
                    source=f"{source}:compiler",
                    kind="compiler",
                    lifetime="candidate",
                    candidate_fp=candidate_hash,
                )
        if violations and (accepted or accepted_as_working):
            scoped_findings = _generation_evidence_from_findings(
                component_labels, findings
            )
            for component_label, finding_text in scoped_findings.items():
                _record_diagnostic_evidence(
                    ctx,
                    component_label,
                    finding_text,
                    source=f"{source}:deterministic",
                    kind="deterministic",
                    lifetime="candidate",
                    candidate_fp=candidate_hash,
                )

        _record(
            ctx.telemetry,
            "phase1_candidate_transition",
            labels=component_labels,
            statement_fps={
                label: statement_fps[label] for label in component_labels
            },
            plan_fps={
                label: _candidate_plan_fingerprint(ctx, label)
                for label in component_labels
            },
            candidate_hash=candidate_hash,
            parent_candidate_hashes=parent_hashes,
            source=source,
            generation_tier=generation_tier,
            accepted_as_best=accepted,
            accepted_as_working=accepted_as_working,
            decision_reasons=reasons,
            deterministic_obligations=sorted(obligations),
            satisfied_obligations=sorted(obligations - violations),
            remaining_obligations=sorted(violations),
            newly_satisfied=sorted(improved),
            regressed_obligations=sorted(regressed),
            lean_status=lean_status,
            semantic_status=semantic_status,
        )
    if stored:
        with _STATE_LOCK:
            saved_code_chars = sum(
                len((getattr(ctx, "generation_candidates", {}).get(label) or {}).get("code", ""))
                for label in stored
            )
        _record(
            ctx.telemetry,
            "phase1_retry_candidate_saved",
            labels=stored,
            source=source,
            code_chars=saved_code_chars,
            statement_fps={label: statement_fps[label] for label in stored},
        )
    return stored


def _reusable_uncompiled_candidate(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    *,
    require_reusable: bool = True,
) -> Phase1LayerCandidate | None:
    """Rehydrate a complete pre-audit candidate without another model call.

    This path is deliberately stricter than ``_generation_candidates_for``:
    every requested statement must have passed deterministic validation for
    its current blueprint fingerprint, and its imports/preamble must have been
    persisted. Older state and rejected candidates fall back to generation.
    """
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
        entries = [candidates.get(label) for label in labels]
    if not entries or any(
        not isinstance(entry, dict)
        or (require_reusable and not _candidate_is_reusable_uncompiled(entry))
        or not str(entry.get("code") or "").strip()
        for entry in entries
    ):
        return None

    imports = list(
        dict.fromkeys(
            str(item)
            for entry in entries
            for item in (entry.get("imports") or [])
            if str(item).strip()
        )
    )
    preamble = list(
        dict.fromkeys(
            str(item)
            for entry in entries
            for item in (entry.get("preamble") or [])
            if str(item).strip()
        )
    )
    blocks: list[str] = []
    seen: set[str] = set()
    for entry in entries:
        code = str(entry.get("code") or "").strip()
        if code not in seen:
            seen.add(code)
            blocks.append(code)
    try:
        parsed = _parse_module(_compose_module(imports, preamble, blocks)[0])
    except (TypeError, ValueError):
        return None
    parsed = _namespace_owned_helpers(ctx, labels, parsed)

    target_names = {_lean_name(label) for label in labels}
    delivered = [decl.name for decl in parsed.decls if decl.name in target_names]
    if len(delivered) != len(labels) or set(delivered) != target_names:
        return None

    missing_imports = _missing_olean_imports(parsed.imports)
    if missing_imports:
        ctx.unavailable_imports.update(missing_imports)
        parsed.imports = [
            item for item in parsed.imports if item not in set(missing_imports)
        ]
    tier = (
        "escalation"
        if any(entry.get("generation_tier") == "escalation" for entry in entries)
        else "base"
    )
    candidate = Phase1LayerCandidate(
        labels=list(labels),
        parsed=parsed,
        import_modules=_sections_for_deps(ctx, labels, sections),
        generation_tier=tier,
        sessions={},
        plan_fps={
            label: str((entry or {}).get("plan_fp") or "")
            for label, entry in zip(labels, entries)
        },
    )
    target_kinds = _phase1_target_kinds(ctx, labels)
    label_by_name = {_lean_name(label): label for label in labels}
    for decl in candidate.parsed.decls:
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    code = _phase1_layer_candidate_code(candidate)
    findings = _skeleton_code_findings(
        code,
        target_kinds,
        label_by_name,
        _planned_helper_owner_by_name(ctx, labels),
    )
    findings += _skeleton_deterministic_findings(code, ctx, labels)
    if findings:
        return None
    _record(
        ctx.telemetry,
        (
            "phase1_uncompiled_candidate_reused"
            if require_reusable
            else "phase1_semantic_candidate_rehydrated"
        ),
        labels=labels,
        count=len(labels),
        generation_tier=tier,
    )
    return candidate


def _retained_generation_candidate_code(
    ctx: Ctx, labels: Iterable[str]
) -> str:
    """Compose the exact best stored candidate for the current plan epoch.

    Unlike ``_reusable_uncompiled_candidate``, this also returns candidates that
    still have deterministic or Lean failures. Correction loops need that exact
    text so a rejected patch cannot become their next editing baseline.
    """
    label_list = list(labels)
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
        entries = [candidates.get(label) for label in label_list]
    if not entries or any(
        not isinstance(entry, dict) or not str(entry.get("code") or "").strip()
        for entry in entries
    ):
        return ""
    imports = list(
        dict.fromkeys(
            str(item)
            for entry in entries
            for item in (entry.get("imports") or [])
            if str(item).strip()
        )
    )
    preamble = list(
        dict.fromkeys(
            str(item)
            for entry in entries
            for item in (entry.get("preamble") or [])
            if str(item).strip()
        )
    )
    blocks: list[str] = []
    seen: set[str] = set()
    for entry in entries:
        block = str(entry.get("code") or "").strip()
        if block and block not in seen:
            seen.add(block)
            blocks.append(block)
    return _compose_module(imports, preamble, blocks)[0] if blocks else ""


def _salvage_partial_phase1_response(
    ctx: Ctx,
    labels: list[str],
    parsed: ParsedModule,
    sections: list[Section],
    *,
    generation_tier: str,
) -> list[str]:
    """Persist independently valid declarations from an incomplete response.

    A missing target is evidence about that target, not about every declaration
    returned beside it.  Shared local helpers still define atomic components:
    a component is reusable only when all of its targets were delivered and the
    complete component passes the ordinary deterministic Phase-1 gates.
    Compilation and semantic auditing remain mandatory in the next transaction.
    """
    target_names = {_lean_name(label): label for label in labels}
    delivered = [
        target_names[decl.name]
        for decl in parsed.decls
        if decl.name in target_names
    ]
    if not delivered:
        return []
    code, _ = _compose_module(
        parsed.imports,
        parsed.preamble,
        [decl.text for decl in parsed.decls],
    )
    stored = _store_generation_candidates(
        ctx,
        delivered,
        code,
        source="phase1_partial_response",
        all_labels=labels,
        generation_tier=generation_tier,
        repair_stage="partial_delivered",
    )
    salvaged: list[str] = []
    handled: set[str] = set()
    with _STATE_LOCK:
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
    for label in stored:
        if label in handled:
            continue
        entry = candidates.get(label) or {}
        component = [
            item
            for item in entry.get("component_labels") or [label]
            if item in stored
        ]
        if not component or any(item in handled for item in component):
            continue
        candidate = _reusable_uncompiled_candidate(
            ctx, component, sections, require_reusable=False
        )
        if candidate is None:
            continue
        candidate_code = _phase1_layer_candidate_code(candidate)
        reusable = _store_generation_candidates(
            ctx,
            component,
            candidate_code,
            source="phase1_partial_response_validated",
            all_labels=component,
            reusable_uncompiled=True,
            generation_tier=generation_tier,
            repair_stage="deterministic_valid",
        )
        salvaged.extend(reusable)
        handled.update(component)
    salvaged = list(dict.fromkeys(salvaged))
    _record(
        ctx.telemetry,
        "phase1_partial_response_salvaged",
        requested_labels=labels,
        delivered_labels=delivered,
        salvaged_labels=salvaged,
        unresolved_labels=[label for label in labels if label not in salvaged],
        generation_tier=generation_tier,
    )
    if salvaged:
        _log(
            "  preserved "
            f"{len(salvaged)} deterministically valid declaration(s) from an "
            "incomplete model response"
        )
    return salvaged


def _semantic_repair_candidate(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
) -> Phase1LayerCandidate | None:
    """Revise the exact compiling candidate rejected by statement alignment.

    This is the mandatory continuation of a semantic rejection. It deliberately
    runs before ordinary generation so an outer retry cannot turn precise
    critic evidence into a cold restart. A failed direct correction is marked
    explicitly; only that state may fall back to generation of an alternative.
    """
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        entries = [
            copy.deepcopy(getattr(ctx, "generation_candidates", {}).get(label))
            for label in labels
        ]
    if not entries or any(
        not isinstance(entry, dict)
        or entry.get("repair_stage") != "semantic_rejected"
        for entry in entries
    ):
        return None
    evidence_by_label = {
        label: _generation_feedback_for(ctx, [label]) for label in labels
    }
    evidence_by_label = {
        label: value for label, value in evidence_by_label.items() if value
    }
    evidence = "\n\n".join(evidence_by_label.values())
    if not evidence:
        return None
    seed = _reusable_uncompiled_candidate(
        ctx, labels, sections, require_reusable=False
    )
    if seed is None:
        return None
    next_tiers = {
        _retry_next_tier(ctx, label, "phase1_statement") for label in labels
    }
    if len(next_tiers) == 1:
        # A correction wave is formed only from labels at the same retry tier.
        # Preserve that tier exactly instead of inheriting whichever producer
        # happened to create the retained source.
        seed.generation_tier = next(iter(next_tiers))
    required_dependencies = {
        label: {
            str(dep)
            for dep in entry.get("required_dependencies") or []
            if str(dep) in ctx.nodes and str(dep) != label
        }
        for label, entry in zip(labels, entries)
        if isinstance(entry, dict)
    }
    try:
        revised = _revise_semantic_candidates(
            ctx,
            [seed],
            set(labels),
            evidence,
            sections,
            required_dependencies=required_dependencies,
            reason_by_label=evidence_by_label,
        )
    except RepairRequest:
        for entry in entries:
            entry["repair_stage"] = "semantic_correction_failed"
        _record(
            ctx.telemetry,
            "phase1_semantic_candidate_transition",
            labels=labels,
            previous="semantic_rejected",
            current="semantic_correction_failed",
        )
        raise
    if len(revised) != 1 or set(revised[0].labels) != set(labels):
        return None
    candidate = revised[0]
    code = _phase1_layer_candidate_code(candidate)
    _store_generation_candidates(
        ctx,
        labels,
        code,
        source="semantic_repair",
        all_labels=labels,
        reusable_uncompiled=True,
        generation_tier=candidate.generation_tier,
        repair_stage="semantic_corrected",
        semantic_status="correction_pending",
        semantic_evidence=evidence,
    )
    _record(
        ctx.telemetry,
        "phase1_semantic_candidate_transition",
        labels=labels,
        previous="semantic_rejected",
        current="semantic_corrected",
    )
    return candidate


def _generation_candidates_for(ctx: Ctx, labels: Iterable[str]) -> str:
    """Return the latest usable declarations as one compact revision input.

    A deterministic-clean compiler intermediate takes precedence over the
    monotonic best because it carries the newest exact diagnostics. The best
    remains stored separately as the rollback point until the working code
    actually compiles or makes measurable deterministic progress.
    """
    label_list = list(labels)
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
    blocks: list[str] = []
    included: list[str] = []
    seen: set[str] = set()
    for label in label_list:
        entry = candidates.get(label)
        working = (
            (entry or {}).get("working_candidate")
            if isinstance((entry or {}).get("working_candidate"), dict)
            else {}
        )
        code = str(
            working.get("code") or (entry or {}).get("code") or ""
        ).strip()
        if not code or code in seen:
            continue
        seen.add(code)
        included.append(label)
        blocks.append(f"-- Rejected candidate for {label}\n{code}")
    text = "\n\n".join(blocks)
    if included:
        _record(
            ctx.telemetry,
            "phase1_retry_candidate_injected",
            labels=included,
            code_chars=len(text),
        )
    return text


def _clear_generation_candidates(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    reason: str = "statement_accepted",
    include_shared_components: bool = False,
) -> set[str]:
    """Forget candidate Lean owned by the requested labels.

    Accepted statements normally clear only their own candidate. An interface
    epoch transition can additionally clear every candidate that shares helper
    code with a changed label, because that stored code is one atomic unit.
    """
    wanted = set(labels)
    cleared: list[str] = []
    with _STATE_LOCK:
        candidates = getattr(ctx, "generation_candidates", {})
        if include_shared_components:
            wanted.update(
                label
                for label, entry in candidates.items()
                if wanted.intersection(
                    (
                        entry.get("component_labels")
                        if isinstance(entry, dict)
                        else None
                    )
                    or [label]
                )
            )
        for label in wanted:
            if candidates.pop(label, None) is not None:
                cleared.append(label)
    telemetry = getattr(ctx, "telemetry", None)
    if cleared and telemetry is not None:
        _record(
            telemetry,
            "phase1_retry_candidate_cleared",
            labels=cleared,
            reason=reason,
        )
    return set(cleared)


def _retry_lifecycle_key(stage: str, label: str) -> str:
    return f"{stage}:{label}"


def _retry_next_tier(ctx: Ctx, label: str, stage: str) -> str:
    """Return the next model tier without letting batching reset provenance."""
    statement_fps = getattr(ctx, "stmt_fps", {})
    entry = getattr(ctx, "retry_lifecycle", {}).get(
        _retry_lifecycle_key(stage, label), {}
    )
    if entry.get("statement_fp") != statement_fps.get(label):
        return "base"
    return "escalation" if entry.get("state") in {"escalation", "exhausted"} else "base"


def _record_retry_failure(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    stage: str,
    attempted_tier: str,
    evidence: str,
    source: str,
    evidence_identity: Mapping[str, Any] | None = None,
) -> set[str]:
    """Advance exact statement versions through base, escalation, exhausted.

    The transition is monotone.  A later batched audit reporting a base-tier
    candidate cannot reset a node that already reached escalation.
    """
    lifecycle = getattr(ctx, "retry_lifecycle", None)
    if lifecycle is None:
        lifecycle = {}
        ctx.retry_lifecycle = lifecycle
    exhausted: set[str] = set()
    evidence_hash = _diagnostic_failure_signature(
        kind=_diagnostic_evidence_policy(source)[0],
        text=evidence,
        identity=evidence_identity,
    )
    for label in labels:
        statement_fp = getattr(ctx, "stmt_fps", {}).get(label, "")
        if not statement_fp:
            continue
        key = _retry_lifecycle_key(stage, label)
        previous = lifecycle.get(key, {})
        previous_state = (
            str(previous.get("state") or "base")
            if previous.get("statement_fp") == statement_fp
            else "base"
        )
        state = (
            "exhausted"
            if attempted_tier == "escalation" or previous_state == "exhausted"
            else "escalation"
        )
        failures = int(previous.get("failures") or 0) + 1
        lifecycle[key] = {
            "label": label,
            "stage": stage,
            "statement_fp": statement_fp,
            "state": state,
            "last_tier": attempted_tier,
            "failures": failures,
            "source": source,
            "evidence_sha256": evidence_hash,
        }
        if state == "exhausted":
            exhausted.add(label)
        telemetry = getattr(ctx, "telemetry", None)
        if telemetry is not None:
            _record(
                telemetry,
                "node_retry_lifecycle",
                label=label,
                stage=stage,
                statement_fp=statement_fp,
                previous_state=previous_state,
                attempted_tier=attempted_tier,
                next_state=state,
                failures=failures,
                source=source,
                evidence_sha256=evidence_hash,
            )
    return exhausted


def _clear_retry_lifecycle(
    ctx: Ctx, labels: Iterable[str], *, stage: str | None = None
) -> set[str]:
    lifecycle = getattr(ctx, "retry_lifecycle", {})
    wanted = set(labels)
    removed: set[str] = set()
    for key, entry in list(lifecycle.items()):
        if entry.get("label") in wanted and (stage is None or entry.get("stage") == stage):
            lifecycle.pop(key, None)
            removed.add(key)
    return removed


def _prune_stale_retry_lifecycle(ctx: Ctx) -> set[str]:
    """Discard retry history when the corresponding blueprint statement changes."""
    lifecycle = getattr(ctx, "retry_lifecycle", {})
    stale = {
        key
        for key, entry in lifecycle.items()
        if entry.get("label") not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(str(entry.get("label") or ""))
    }
    for key in stale:
        lifecycle.pop(key, None)
    return stale
