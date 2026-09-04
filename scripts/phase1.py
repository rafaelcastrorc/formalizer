"""Phase 1: interface planning, statement generation, freezing, audits, and failure escalation.

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


def _phase1_context_atomic_units(ctx: Ctx, group: list[str]) -> list[list[str]]:
    """Keep persisted shared-helper candidate components indivisible."""
    available = set(group)
    emitted: set[str] = set()
    units: list[list[str]] = []
    for label in group:
        if label in emitted:
            continue
        component = set(_candidate_component_labels(ctx, label, available))
        unit = [item for item in group if item in component and item not in emitted]
        if not unit:
            unit = [label]
        units.append(unit)
        emitted.update(unit)
    return units


def _partition_phase1_groups_by_dependency_context(
    ctx: Ctx,
    groups: list[list[str]],
    sections: list[Section],
    *,
    budget: int = PHASE1_DEPENDENCY_CONTEXT_BUDGET,
) -> list[list[str]]:
    """Split candidate groups at the complete dependency-context boundary.

    The operation is deterministic and model-free. It greedily preserves the
    largest prefix whose exact generated dependency interface fits the soft
    budget. Persisted shared-helper components remain atomic; if such a unit or
    a singleton exceeds the budget, prompt construction receives its complete
    interface and telemetry records the unavoidable overage.
    """
    partitioned: list[list[str]] = []
    for original in groups:
        if not original:
            continue
        try:
            parts: list[list[str]] = []
            current: list[str] = []
            for unit in _phase1_context_atomic_units(ctx, original):
                trial = current + unit
                trial_chars = _phase1_dependency_interface_chars(
                    ctx, trial, sections
                )
                if current and trial_chars > budget:
                    parts.append(current)
                    current = list(unit)
                else:
                    current = trial
            if current:
                parts.append(current)

            sizes = [
                _phase1_dependency_interface_chars(ctx, part, sections)
                for part in parts
            ]
        except ValueError as exc:
            # This pre-dispatch pass is only a batching optimization. Synthetic
            # replay states and a temporarily deferred section may not expose a
            # readable interface yet. Preserve the original group and let the
            # existing prompt-construction completeness gate make the
            # authoritative decision when generation actually starts.
            _record(
                ctx.telemetry,
                "phase1_dependency_context_partition_deferred",
                labels=original,
                soft_budget=budget,
                reason=str(exc),
            )
            partitioned.append(original)
            continue
        if len(parts) > 1:
            _log(
                "  dependency context partitioned "
                f"{len(original)} node(s) into "
                + " + ".join(str(len(part)) for part in parts)
                + f" (soft limit {budget} chars)"
            )
            _record(
                ctx.telemetry,
                "phase1_dependency_context_partitioned",
                labels=original,
                groups=parts,
                interface_chars=sizes,
                soft_budget=budget,
            )
        for part, size in zip(parts, sizes):
            if size > budget:
                _record(
                    ctx.telemetry,
                    "phase1_dependency_context_soft_overflow",
                    labels=part,
                    interface_chars=size,
                    soft_budget=budget,
                    reason="atomic_component_or_singleton",
                )
        partitioned.extend(parts)
    return partitioned


def _coalesce_phase1_semantic_correction_waves(
    ctx: Ctx,
    groups: list[list[str]],
    sections: list[Section],
    *,
    max_labels: int = PHASE1_SEMANTIC_CORRECTION_WAVE_MAX,
) -> list[list[str]]:
    """Batch compatible semantic-repair singletons without merging state.

    The outer retry router intentionally isolates rejected declarations, but
    dispatching every independent correction as a separate model call wastes
    most of Phase 1's model time.  This coordinator merges only current
    ``semantic_rejected`` singletons that have the same dependency imports and
    next retry tier.  The correction transaction still receives and stores
    evidence per label, and an incomplete response goes through the existing
    multi-label isolation/bisection route.
    """
    if max_labels < 2 or len(groups) < 2:
        return groups
    with _STATE_LOCK:
        _prune_stale_generation_candidates(ctx)
        entries = copy.deepcopy(getattr(ctx, "generation_candidates", {}))

    def key_for(group: list[str]) -> tuple[tuple[str, ...], str] | None:
        if len(group) != 1:
            return None
        label = group[0]
        entry = entries.get(label)
        if (
            not isinstance(entry, dict)
            or entry.get("repair_stage") != "semantic_rejected"
            or not str(entry.get("code") or "").strip()
            or not _generation_feedback_for(ctx, [label])
        ):
            return None
        return (
            tuple(_sections_for_deps(ctx, [label], sections)),
            _retry_next_tier(ctx, label, "phase1_statement"),
        )

    merged: list[list[str]] = []
    open_wave_by_key: dict[tuple[tuple[str, ...], str], int] = {}
    merged_sources: dict[int, list[list[str]]] = {}
    for group in groups:
        key = key_for(group)
        position = open_wave_by_key.get(key) if key is not None else None
        if position is not None and len(merged[position]) < max_labels:
            label = group[0]
            # This is normally guaranteed by the ready frontier. Keep the
            # helper total when called from tests or future schedulers.
            independent = all(
                other not in _statement_uses(ctx.nodes[label])
                and label not in _statement_uses(ctx.nodes[other])
                for other in merged[position]
            )
            if independent:
                merged[position].append(label)
                merged_sources.setdefault(position, []).append(list(group))
                if len(merged[position]) >= max_labels:
                    open_wave_by_key.pop(key, None)
                continue
        merged.append(list(group))
        position = len(merged) - 1
        if key is not None:
            open_wave_by_key[key] = position
            merged_sources[position] = [list(group)]

    waves = [
        merged[position]
        for position, sources in merged_sources.items()
        if len(sources) > 1
    ]
    if waves:
        _log(
            "  coalesced semantic corrections into "
            + ", ".join(f"{len(wave)}-node" for wave in waves)
            + " wave(s)"
        )
        _record(
            ctx.telemetry,
            "phase1_semantic_correction_waves",
            input_groups=groups,
            output_groups=merged,
            waves=waves,
            max_labels=max_labels,
        )
    return merged


def _patchable_skeleton_labels(findings: list[SkeletonFinding], labels: list[str]) -> list[str]:
    """Return the small set of labels worth repairing in-place.

    Global file-shape problems still use the existing whole-section retry path.
    Targeted replacement is for declaration-local deterministic failures only.
    """
    section_labels = set(labels)
    targeted = [finding.label for finding in findings if finding.label in section_labels]
    if not targeted:
        return []
    if any(finding.label is None for finding in findings):
        return []
    ordered = [label for label in labels if label in set(targeted)]
    if len(ordered) > TARGETED_DECL_PATCH_MAX_LABELS:
        return []
    return ordered


def _isolated_deterministic_failure_labels(
    findings: list[SkeletonFinding], labels: list[str]
) -> list[str]:
    """Return an attributable proper subset, or empty for section-wide failures."""
    if any(finding.label is None for finding in findings):
        return []
    label_set = set(labels)
    failed = {finding.label for finding in findings if finding.label in label_set}
    if not failed or failed == label_set:
        return []
    return [label for label in labels if label in failed]


def _apply_skeleton_replacements(
    parsed: ParsedModule,
    labels: list[str],
    patch_labels: list[str],
    replacement_code: str,
    explicit_owner_by_name: dict[str, str] | None = None,
    required_helper_replacements: set[str] | None = None,
    unavailable_imports: set[str] | None = None,
) -> ParsedModule | None:
    """Merge replacement declarations into a generated section.

    The section remains a section: this only swaps or inserts declarations for
    the listed target labels. Accepted plan-owned helper interfaces are stable
    state: a target-only correction preserves them unless the response replaces
    them explicitly. Unplanned helpers still belong to the target replacement
    transaction and are discarded when omitted. The caller re-runs the
    deterministic audit on the whole module before freezing.
    """
    patch_parsed = _parse_module(replacement_code)
    target_names = {_lean_name(label) for label in labels}
    patch_names = {_lean_name(label) for label in patch_labels}
    replacements = {decl.name: decl for decl in patch_parsed.decls if decl.name in patch_names}
    if set(replacements) != patch_names:
        return None

    original = list(parsed.decls)
    original_names = {decl.name for decl in original if decl.name}
    label_by_name = {_lean_name(label): label for label in labels}
    original_consumers = _declaration_target_consumers(
        parsed, label_by_name, explicit_owner_by_name
    )
    patch_label_set = set(patch_labels)
    replaceable_helper_names = {
        decl.name
        for index, decl in enumerate(original)
        if decl.name
        and decl.name not in target_names
        and original_consumers.get(index, set())
        and original_consumers[index] <= patch_label_set
    }
    planned_helper_names = set(explicit_owner_by_name or {})
    returned_helper_names = {
        decl.name
        for decl in patch_parsed.decls
        if decl.name and decl.name not in patch_names and decl.name not in target_names
    }
    if not set(required_helper_replacements or {}) <= returned_helper_names:
        return None
    helper_decls = [
        decl
        for decl in patch_parsed.decls
        if decl.name
        and decl.name not in patch_names
        and decl.name not in target_names
        and (
            decl.name not in original_names
            or decl.name in replaceable_helper_names
        )
    ]

    helper_inserted = False
    used_replacements: set[str] = set()
    new_decls: list[DeclBlock] = []
    for index, decl in enumerate(original):
        # Unplanned local helpers belong to the target replacement transaction.
        # Plan-owned interfaces are different: once accepted, correcting only
        # the target must not silently delete them. An explicitly returned
        # replacement still supersedes the old interface below.
        if (
            decl.name not in patch_names
            and decl.name not in target_names
            and original_consumers.get(index, set())
            and original_consumers[index] <= patch_label_set
        ):
            if (
                decl.name in planned_helper_names
                and decl.name not in returned_helper_names
            ):
                new_decls.append(decl)
            continue
        if decl.name in patch_names:
            if not helper_inserted:
                new_decls.extend(helper_decls)
                helper_inserted = True
            new_decls.append(replacements[decl.name])
            used_replacements.add(decl.name)
        else:
            new_decls.append(decl)

    for label in patch_labels:
        lean_name = _lean_name(label)
        if lean_name in used_replacements:
            continue
        insert_at = None
        label_pos = labels.index(label)
        for previous in reversed(labels[:label_pos]):
            idx = next((i for i, decl in enumerate(new_decls) if decl.name == _lean_name(previous)), None)
            if idx is not None:
                insert_at = idx + 1
                break
        if insert_at is None:
            for following in labels[label_pos + 1 :]:
                idx = next((i for i, decl in enumerate(new_decls) if decl.name == _lean_name(following)), None)
                if idx is not None:
                    insert_at = idx
                    break
        if insert_at is None:
            insert_at = len(new_decls)
        if not helper_inserted:
            new_decls[insert_at:insert_at] = helper_decls
            helper_inserted = True
            insert_at += len(helper_decls)
        new_decls.insert(insert_at, replacements[lean_name])
        used_replacements.add(lean_name)

    # Lean declaration names are module-global. Keep the first declaration for
    # every name, not just current targets: a model may repeat an existing
    # dependency as a "helper", and retaining it poisons every later retry.
    seen_names: set[str] = set()
    deduped: list[DeclBlock] = []
    for decl in new_decls:
        if decl.name:
            if decl.name in seen_names:
                continue
            seen_names.add(decl.name)
        deduped.append(decl)
    merged_imports = list(dict.fromkeys(parsed.imports + patch_parsed.imports))
    missing_imports = set(_missing_olean_imports(merged_imports))
    if unavailable_imports is not None:
        unavailable_imports.update(missing_imports)
    return ParsedModule(
        # Import validation belongs after the merge. Validating only the patch
        # response is too late: the merge has already copied those imports into
        # the persistent skeleton, where they poison every subsequent retry.
        imports=[item for item in merged_imports if item not in missing_imports],
        preamble=list(dict.fromkeys(parsed.preamble + patch_parsed.preamble)),
        decls=deduped,
    )


def _targeted_patch_skeleton_decls(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    parsed: ParsedModule,
    module_code: str,
    findings: list[SkeletonFinding],
    *,
    timeout: int,
    sessions: dict[str, str] | None = None,
    escalated: bool = False,
    provisional_only: bool = False,
    escalate_timeout: bool = True,
    findings_already_persisted: bool = False,
) -> tuple[ParsedModule | None, str]:
    patch_labels = _patchable_skeleton_labels(findings, labels)
    if not patch_labels:
        return None, "not patchable"
    _log(
        "  targeted check isolated "
        + f"{len(patch_labels)} declaration(s); patching: "
        + ", ".join(patch_labels)
    )
    try:
        prompt = _targeted_skeleton_patch_prompt(
            ctx,
            patch_labels,
            sections,
            import_modules,
            module_code,
            findings,
            timeout_s=timeout,
            provisional_only=provisional_only,
            findings_already_persisted=findings_already_persisted,
        )
    except ValueError as exc:
        return None, f"targeted declaration context check failed: {exc}"
    tier = "escalation" if escalated else "base"
    result_tier = tier
    exchange_key = _phase1_exchange_start(
        ctx,
        patch_labels,
        prompt=prompt,
        candidate_code=module_code,
        purpose="skeleton_declaration_patch",
        tier=tier,
    )
    if not exchange_key:
        _record(
            ctx.telemetry,
            "phase1_exchange_sample_limit",
            purpose="skeleton_declaration_patch",
            labels=patch_labels,
            tier=tier,
            limit=PHASE1_EXCHANGE_SAMPLE_LIMIT,
        )
        return None, (
            "targeted declaration patch exhausted the persisted three-sample "
            "allowance for this exact statement, plan, model, candidate, and "
            "prompt; routing the retained evidence without another model call"
        )
    result = _call_model(
        ctx,
        prompt,
        purpose="skeleton_declaration_patch",
        timeout=timeout,
        effort=ctx.escalation_effort if escalated else ctx.base_effort,
        labels=patch_labels,
        escalated=escalated,
        sessions=sessions,
    )
    duplicate = _phase1_exchange_finish(
        ctx,
        exchange_key,
        status=result.status,
        response_text=result.text,
    )
    if (
        result.status == "timeout"
        and not escalated
        and escalate_timeout
        and len(patch_labels) == 1
    ):
        result_tier = "escalation"
        exchange_key = _phase1_exchange_start(
            ctx,
            patch_labels,
            prompt=prompt,
            candidate_code=module_code,
            purpose="skeleton_declaration_patch",
            tier="escalation",
        )
        if not exchange_key:
            _record(
                ctx.telemetry,
                "phase1_exchange_sample_limit",
                purpose="skeleton_declaration_patch",
                labels=patch_labels,
                tier="escalation",
                limit=PHASE1_EXCHANGE_SAMPLE_LIMIT,
            )
            return None, (
                "targeted declaration patch exhausted the persisted "
                "three-sample escalation allowance for this exact statement, "
                "plan, model, candidate, and prompt; routing the retained "
                "evidence without another model call"
            )
        result = _call_model(
            ctx,
            prompt,
            purpose="skeleton_declaration_patch",
            timeout=ctx.hard_timeout,
            effort=ctx.escalation_effort,
            labels=patch_labels,
            escalated=True,
            sessions=sessions,
        )
        duplicate = _phase1_exchange_finish(
            ctx,
            exchange_key,
            status=result.status,
            response_text=result.text,
        )
    if duplicate:
        _record(
            ctx.telemetry,
            "duplicate_model_exchange",
            purpose="skeleton_declaration_patch",
            labels=patch_labels,
            escalated=(result_tier == "escalation"),
            exchange_fingerprint=exchange_key,
        )
        return None, (
            "targeted declaration patch replayed a byte-identical response for "
            "the same persisted correction context"
        )
    if result.status != "ok":
        return None, f"targeted declaration patch {result.status}: {result.error}"
    try:
        canonical = _ingest_model_lean(
            ctx,
            # The correction may reference accepted siblings from the owning
            # component. Canonicalize against that complete namespace while
            # keeping replacement authority restricted to ``patch_labels``
            # below. Using only ``patch_labels`` renamed valid sibling names
            # to generated ``_autobp_*`` identifiers.
            labels,
            result.text,
            defer_phase1_bodies=True,
        )
    except ValueError as exc:
        return None, f"targeted declaration patch did not return Lean code: {exc}"
    replacement_parsed = canonical.parsed
    replacement_code, _ = _compose_module(
        replacement_parsed.imports,
        replacement_parsed.preamble,
        [decl.text for decl in replacement_parsed.decls],
    )
    planned_helper_owners = _planned_helper_owner_by_name(ctx, labels)
    required_helper_replacements = {
        finding.lean_name
        for finding in findings
        if finding.lean_name in planned_helper_owners
        and planned_helper_owners[finding.lean_name] in set(patch_labels)
    }
    patched = _apply_skeleton_replacements(
        parsed,
        labels,
        patch_labels,
        replacement_code,
        planned_helper_owners,
        required_helper_replacements,
        ctx.unavailable_imports,
    )
    if patched is None:
        return None, (
            "targeted declaration patch omitted one or more required target/helper "
            "replacement declarations"
        )
    _record(
        ctx.telemetry,
        "skeleton_declaration_patch_result",
        labels=patch_labels,
        status="applied",
    )
    return patched, "patched"


def _retry_statement_patch_compile_once(
    ctx: Ctx,
    owner_labels: list[str],
    allowed_labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    parsed: ParsedModule,
    module_code: str,
    lean_output: str,
    path: Path,
    *,
    sessions: dict[str, str] | None = None,
) -> tuple[ParsedModule | None, str, str]:
    """Give one failed statement correction its exact Lean errors.

    This is an exceptional, base-tier retry after a semantic correction has
    already been produced. It never expands into the hard-timeout ladder: if
    the precise compiler feedback is insufficient, the caller resumes the
    existing repair/decomposition routing instead of spending another long
    agent call.
    """
    _code, ranges = _compose_module(
        parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
    )
    findings = _lean_compile_findings(
        parsed,
        owner_labels,
        ranges,
        lean_output,
        path.name,
        _planned_helper_owner_by_name(ctx, owner_labels),
    )
    allowed = set(allowed_labels)
    findings = [finding for finding in findings if finding.label in allowed]
    patch_labels = _patchable_skeleton_labels(findings, allowed_labels)
    if not patch_labels and len(allowed_labels) == 1:
        patch_labels = list(allowed_labels)
        findings = [
            SkeletonFinding(
                "Lean rejected the corrected declaration:\n" + lean_output[-8000:],
                label=allowed_labels[0],
                lean_name=_lean_name(allowed_labels[0]),
            )
        ]
    if not patch_labels:
        return None, module_code, "compiler error could not be assigned to a corrected declaration"

    _log(
        "  corrected statement failed Lean; giving exact compiler feedback once: "
        + ", ".join(patch_labels)
    )
    patched, note = _targeted_patch_skeleton_decls(
        ctx,
        owner_labels,
        sections,
        import_modules,
        parsed,
        module_code,
        findings,
        timeout=ctx.base_timeout,
        sessions=sessions,
        escalated=False,
        escalate_timeout=False,
    )
    if patched is None:
        return None, module_code, note

    target_kinds = _phase1_target_kinds(ctx, allowed_labels)
    label_by_name = {_lean_name(label): label for label in allowed_labels}
    for decl in patched.decls:
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    corrected_code, _ranges = _compose_module(
        patched.imports, patched.preamble, [decl.text for decl in patched.decls]
    )
    deterministic = _skeleton_code_findings(
        corrected_code,
        target_kinds,
        label_by_name,
        _planned_helper_owner_by_name(ctx, allowed_labels),
    )
    deterministic += _skeleton_deterministic_findings(
        corrected_code, ctx, allowed_labels
    )
    if deterministic:
        return None, module_code, _format_skeleton_findings(deterministic)
    path.write_text(corrected_code, encoding="utf-8")
    ok, output = _check_lean(path, ctx.lean_command)
    if not ok:
        return None, module_code, output[-8000:]
    _record(
        ctx.telemetry,
        "statement_patch_compile_retry",
        labels=patch_labels,
        status="accepted",
    )
    return patched, corrected_code, "patched from exact compiler feedback"


def _design_plan_order(ctx: Ctx, labels: Iterable[str]) -> list[str]:
    """Return labels in root-first planning order, independent of traversal."""
    requested = set(labels)
    ordered = [
        label
        for layer in _top_down_statement_layers(ctx.nodes)
        for label in layer
        if label in requested
    ]
    return ordered + sorted(requested - set(ordered))


def _sync_design_plan(ctx: Ctx) -> None:
    """Rebuild the compatibility text view from structured contracts."""
    entries = getattr(ctx, "design_plan_entries", {})
    ctx.design_plan = "\n".join(
        _render_design_plan_entry(label, entries[label])
        for label in _design_plan_order(ctx, entries)
        if not _uses_blueprint_direct_generation(ctx, label)
        if str(entries[label].get("target_signature") or "").strip()
    )


def _transition_phase1_generation_epoch(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    reason: str,
) -> None:
    """Atomically discard scheduler state owned by an obsolete interface epoch.

    A Phase-1 plan replacement, plan deletion, or switch to blueprint-direct
    generation changes which prompt/candidate contract is authoritative for a
    node.  Every such mutation must invalidate the same state in one place.
    Statement-scoped semantic facts are deliberately retained so the next
    generation call still sees why the prior epoch failed. Candidate- and
    plan-scoped diagnostics expire here with the object they describe.
    """
    ordered = list(dict.fromkeys(str(label) for label in labels))
    if not ordered:
        _sync_design_plan(ctx)
        return
    _migrate_legacy_generation_feedback(ctx)
    with _STATE_LOCK:
        removed_candidates = _clear_generation_candidates(
            ctx,
            ordered,
            reason=reason,
            include_shared_components=True,
        )
        removed_retries = _clear_retry_lifecycle(
            ctx, ordered, stage="phase1_statement"
        )
        removed_exchanges = _clear_phase1_exchange_history(ctx, ordered)
        _release_quarantine(ctx, ordered, reason=reason)
        _release_local_group_partitions(ctx, ordered, reason=reason)
        _sync_design_plan(ctx)
        stale_diagnostics = _prune_stale_diagnostic_evidence(ctx)
        _sync_generation_feedback_projection(ctx)
        active_diagnostics = _active_diagnostic_evidence(ctx, ordered)
    telemetry = getattr(ctx, "telemetry", None)
    if telemetry is not None:
        _record(
            telemetry,
            "phase1_generation_epoch_transition",
            labels=ordered,
            reason=reason,
            removed_candidates=sorted(removed_candidates),
            removed_retry_entries=len(removed_retries),
            removed_exchange_entries=len(removed_exchanges),
            removed_diagnostic_entries=len(stale_diagnostics),
            preserved_diagnostic_kinds=sorted(
                {str(entry.get("kind") or "") for entry in active_diagnostics}
            ),
        )


def _invalidate_descendant_design_plans_for_changed_interfaces(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    reason: str,
) -> set[str]:
    """Drop downstream Phase-1 plans after a provider interface becomes untrusted.

    The global/semantic plan is only guidance. If a dependency's candidate-owned
    surface is rejected and that dependency switches to blueprint-direct
    generation, descendants planned against the old surface are no longer
    authoritative even though their own blueprint statement text did not change.
    Keep the regenerated provider as the source of truth by forcing descendants
    to re-plan/re-generate against the new dependency contract.
    """
    roots = {str(label) for label in labels if str(label) in ctx.nodes}
    descendants = _dependency_descendants(ctx.nodes, roots) - roots
    affected = {
        label
        for label in descendants
        if label in getattr(ctx, "design_plan_entries", {})
        or label in getattr(ctx, "design_plan_alternates", {})
        or label in getattr(ctx, "generation_candidates", {})
        or any(
            entry.get("label") == label
            for entry in getattr(ctx, "retry_lifecycle", {}).values()
        )
    }
    if not affected:
        return set()

    for label in affected:
        getattr(ctx, "design_plan_entries", {}).pop(label, None)
        getattr(ctx, "design_plan_alternates", {}).pop(label, None)
    _transition_phase1_generation_epoch(ctx, sorted(affected), reason=reason)
    _record(
        ctx.telemetry,
        "phase1_descendant_plan_invalidated",
        labels=sorted(affected),
        roots=sorted(roots),
        reason=reason,
    )
    return affected


def _invalidate_blueprint_direct_descendants_after_freeze(
    ctx: Ctx, labels: Iterable[str]
) -> set[str]:
    """Invalidate descendants only if blueprint-direct changed public surface."""
    direct = getattr(ctx, "blueprint_direct_generation", {}) or {}
    changed_roots: set[str] = set()
    for label in labels:
        entry = direct.get(label)
        if not isinstance(entry, dict):
            continue
        if str(entry.get("statement_fp") or "") != ctx.stmt_fps.get(label, ""):
            continue
        previous_fp = str(entry.get("previous_interface_fp") or "")
        current_fp = _design_plan_public_surface_fingerprint(
            (getattr(ctx, "design_plan_entries", {}) or {}).get(label)
        )
        if not current_fp:
            continue
        if str(entry.get("accepted_interface_fp") or "") == current_fp:
            continue
        entry["accepted_interface_fp"] = current_fp
        if previous_fp and previous_fp != current_fp:
            changed_roots.add(label)
            _record(
                ctx.telemetry,
                "phase1_blueprint_direct_interface_changed",
                label=label,
                previous_interface_fp=previous_fp,
                accepted_interface_fp=current_fp,
            )
    if not changed_roots:
        return set()
    return _invalidate_descendant_design_plans_for_changed_interfaces(
        ctx,
        changed_roots,
        reason="blueprint_direct_interface_changed",
    )


def _uses_blueprint_direct_generation(ctx: Ctx, label: str) -> bool:
    """Return whether this exact statement has stopped trusting its plan."""
    entry = (getattr(ctx, "blueprint_direct_generation", {}) or {}).get(label)
    return bool(
        isinstance(entry, dict)
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(label, "")
    )


def _activate_blueprint_direct_generation(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    source: str,
    evidence_by_label: Mapping[str, str] | None = None,
    shared_evidence: bool = False,
) -> set[str]:
    """Bound the damage from an unusable global-plan component.

    The plan remains available for healthy contracts, but these exact
    statement versions are generated from the blueprint and accumulated
    failure evidence instead. This transition costs no model call and is
    monotonic until the blueprint statement changes.
    """
    ordered = list(dict.fromkeys(labels))
    scoped_evidence = (
        {
            label: str(value).strip()[-12000:]
            for label, value in evidence_by_label.items()
            if label in ordered and str(value).strip()
        }
        if evidence_by_label is not None
        else _explicit_generation_evidence_by_label(ordered, evidence)
    )
    if shared_evidence and evidence.strip():
        shared = evidence.strip()[-12000:]
        for label in ordered:
            scoped_evidence.setdefault(label, shared)

    direct = getattr(ctx, "blueprint_direct_generation", {})
    ctx.blueprint_direct_generation = direct
    activated: set[str] = set()
    already_active: set[str] = set()
    for label in ordered:
        statement_fp = ctx.stmt_fps.get(label, "")
        if not statement_fp:
            continue
        previous = direct.get(label) or {}
        if str(previous.get("statement_fp") or "") == statement_fp:
            # Blueprint-direct is a generation strategy for one exact
            # statement version, not a retry attempt. Later compiler/audit
            # findings belong to that strategy's existing correction
            # lifecycle; reactivating here would erase its candidate, retry
            # provenance, and exchange history.
            already_active.add(label)
            continue
        previous_interface_fp = str(
            previous.get("previous_interface_fp") or ""
        ) or _design_plan_public_surface_fingerprint(
            getattr(ctx, "design_plan_entries", {}).get(label)
        )
        label_evidence = scoped_evidence.get(label, "")
        direct[label] = {
            "statement_fp": statement_fp,
            "source": source,
            "evidence": label_evidence,
            "activations": 1,
            "previous_interface_fp": previous_interface_fp,
            "accepted_interface_fp": "",
        }
        activated.add(label)

    if already_active:
        repeated_scoped = {
            label: scoped_evidence[label]
            for label in already_active
            if label in scoped_evidence
        }
        _store_generation_feedback(
            ctx,
            already_active,
            evidence,
            source=source,
            evidence_by_label=repeated_scoped,
        )
        _record(
            ctx.telemetry,
            "phase1_blueprint_direct_generation_reused",
            labels=sorted(already_active),
            source=source,
            statement_fps={
                label: ctx.stmt_fps.get(label, "")
                for label in sorted(already_active)
            },
            lifecycle_preserved=True,
        )
    if not activated:
        return set()

    for label in activated:
        getattr(ctx, "design_plan_alternates", {}).pop(label, None)
        entry = getattr(ctx, "design_plan_entries", {}).get(label)
        if isinstance(entry, dict):
            for key in (
                "audit_fp",
                "rejected_audit_fp",
                "rejected_kind",
                "rejected_reason",
                "rejected_helpers",
                "correction_base_fp",
                "correction_escalation_fp",
                "closure_fp",
                "closure_wave_id",
            ):
                entry.pop(key, None)
    _store_generation_feedback(
        ctx,
        activated,
        evidence,
        source=source,
        evidence_by_label=scoped_evidence,
    )
    _transition_phase1_generation_epoch(
        ctx,
        activated,
        reason=f"blueprint_direct:{source}",
    )
    _record(
        ctx.telemetry,
        "phase1_blueprint_direct_generation_activated",
        labels=sorted(activated),
        source=source,
        avoided_route="repeated_interface_plan_correction",
        evidence_sha256_by_label={
            label: hashlib.sha256(
                scoped_evidence.get(label, "").encode("utf-8")
            ).hexdigest()
            for label in sorted(activated)
            if scoped_evidence.get(label)
        },
        evidence_chars_by_label={
            label: len(scoped_evidence.get(label, ""))
            for label in sorted(activated)
            if scoped_evidence.get(label)
        },
    )
    _log(
        "  interface plan circuit breaker activated; generating directly from "
        "the blueprint for: " + ", ".join(sorted(activated))
    )
    return activated


def _prune_stale_blueprint_direct_generation(ctx: Ctx) -> set[str]:
    """Discard stale state and repair pre-v8 sibling-evidence contamination."""
    direct = getattr(ctx, "blueprint_direct_generation", {})
    stale = {
        label
        for label, entry in direct.items()
        if label not in ctx.nodes
        or str(entry.get("statement_fp") or "") != ctx.stmt_fps.get(label, "")
    }
    for label in stale:
        direct.pop(label, None)

    # Older runs copied one complete multi-node audit into every activated
    # entry.  Repair that persisted state on continuation before its evidence
    # participates in candidate plan fingerprints.  Free-form singleton and
    # genuinely shared operational evidence has no declaration marker and is
    # left untouched.
    repaired: dict[str, tuple[int, int]] = {}
    known_labels = list(ctx.nodes)
    for label, entry in direct.items():
        evidence = str(entry.get("evidence") or "").strip()
        if not evidence:
            continue
        parsed = _explicit_generation_evidence_by_label(known_labels, evidence)
        if not parsed:
            continue
        own_evidence = parsed.get(label, "")
        if own_evidence == evidence:
            continue
        repaired[label] = (len(evidence), len(own_evidence))
        entry["evidence"] = own_evidence
    if repaired:
        _record(
            ctx.telemetry,
            "phase1_blueprint_direct_evidence_migrated",
            labels=sorted(repaired),
            evidence_chars={
                label: {"before": before, "after": after}
                for label, (before, after) in repaired.items()
            },
            reason="remove_sibling_owned_audit_findings",
        )
    return stale


def _preserve_plan_entry_progress(
    previous: dict[str, Any] | None,
    replacement: dict[str, Any],
) -> dict[str, Any]:
    """Carry retry progress across a replacement of the same statement plan.

    Model corrections replace the contract's mathematical payload, but the
    blueprint statement has not changed.  Counters that bound correction
    strategies therefore belong to the statement lifecycle, not to one model
    response.  Dropping them lets closure or alternate-plan correction reset a
    repeatedly rejected node to revision zero and creates an unbounded logical
    retry loop under the global repair budget.
    """
    previous = previous or {}
    # ``origin`` is provenance, not model-owned plan payload.  In particular,
    # a correction response does not echo ``phase1_candidate``.  Losing that
    # marker would make a fresh candidate-derived contract look like resumed
    # legacy typed-plan state and route later failures through the obsolete
    # independent plan-correction loop.
    if previous.get("origin") and not replacement.get("origin"):
        replacement["origin"] = previous["origin"]
    for key in _PLAN_ENTRY_PROGRESS_KEYS:
        prior = int(previous.get(key) or 0)
        current = int(replacement.get(key) or 0)
        if prior or current:
            replacement[key] = max(prior, current)
    return replacement


def _prune_stale_design_plan(ctx: Ctx) -> set[str]:
    """Invalidate only plan entries whose blueprint statement changed."""
    stale_direct = _prune_stale_blueprint_direct_generation(ctx)
    entries = getattr(ctx, "design_plan_entries", {})
    stale = {
        label
        for label, entry in entries.items()
        if label not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        or int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
        or not str(entry.get("target_signature") or "").strip()
    }
    for label in stale:
        entries.pop(label, None)
    alternates = getattr(ctx, "design_plan_alternates", {})
    stale_alternates = {
        label
        for label, entry in alternates.items()
        if label not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        or int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
        or not str(entry.get("target_signature") or "").strip()
    }
    for label in stale_alternates:
        alternates.pop(label, None)
    semantic_entries = getattr(ctx, "semantic_plan_entries", {})
    stale_semantic = {
        label
        for label, entry in semantic_entries.items()
        if label not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        or int(entry.get("schema_version") or 0)
        != SEMANTIC_PLAN_SCHEMA_VERSION
    }
    for label in stale_semantic:
        semantic_entries.pop(label, None)
    invalidated_epoch = stale | stale_direct
    if invalidated_epoch:
        _transition_phase1_generation_epoch(
            ctx,
            invalidated_epoch,
            reason="stale_plan_or_strategy_pruned",
        )
    else:
        _sync_design_plan(ctx)
    telemetry = getattr(ctx, "telemetry", None)
    if stale and telemetry is not None:
        _record(
            telemetry,
            "phase1_design_plan_invalidated",
            labels=sorted(stale),
            reason="statement_fingerprint_changed",
        )
    return stale | stale_alternates | stale_semantic | stale_direct


def _render_semantic_plan_entry(label: str, entry: dict[str, Any]) -> str:
    """Compact advisory guidance for one Phase-1 declaration.

    Unlike ``_render_design_plan_entry``, this is intentionally not Lean. The
    blueprint and deterministic dependency graph remain authoritative; these
    notes only keep independently generated frontiers semantically coherent.
    """
    lines = [
        f"NODE {label}",
        f"REPRESENTATION: {str(entry.get('representation') or '').strip()}",
    ]
    vocabulary = entry.get("vocabulary") or []
    if vocabulary:
        lines.append("STABLE VOCABULARY:")
        lines.extend(
            f"- {str(item.get('name') or '').strip()}: "
            f"{str(item.get('purpose') or '').strip()}"
            for item in vocabulary
            if isinstance(item, dict)
        )
    obligations = [
        str(item).strip()
        for item in entry.get("obligations") or []
        if str(item).strip()
    ]
    if obligations:
        lines.append("MUST PRESERVE:")
        lines.extend(f"- {item}" for item in obligations)
    requirements = entry.get("provider_requirements") or []
    if requirements:
        lines.append("PROVIDER CAPABILITIES:")
        for requirement in requirements:
            if not isinstance(requirement, dict):
                continue
            capabilities = ", ".join(
                str(item).strip()
                for item in requirement.get("capabilities") or []
                if str(item).strip()
            )
            lines.append(
                f"- {str(requirement.get('provider') or '').strip()}: "
                f"{capabilities or '(none specified)'}"
            )
    return "\n".join(lines)


def _repair_json_string_backslashes(text: str) -> tuple[str, int]:
    r"""Escape model-emitted TeX backslashes without changing JSON structure.

    Models occasionally return otherwise valid JSON containing ``\dagger`` or
    another TeX command with only one backslash. JSON rejects most such escapes
    and silently interprets commands beginning with ``b``, ``f``, ``n``, ``r``,
    or ``t`` as control escapes. Repair only backslashes inside quoted strings;
    structural text and already-valid escaped backslashes remain unchanged.
    """
    output: list[str] = []
    in_string = False
    repaired = 0
    index = 0
    while index < len(text):
        char = text[index]
        if char == '"':
            in_string = not in_string
            output.append(char)
            index += 1
            continue
        if not in_string or char != "\\":
            output.append(char)
            index += 1
            continue
        if index + 1 >= len(text):
            output.append("\\\\")
            repaired += 1
            index += 1
            continue
        escaped = text[index + 1]
        if escaped in {'"', "\\", "/"}:
            output.extend((char, escaped))
            index += 2
            continue
        if (
            escaped == "u"
            and index + 5 < len(text)
            and all(
                item in "0123456789abcdefABCDEF"
                for item in text[index + 2 : index + 6]
            )
        ):
            output.extend(text[index : index + 6])
            index += 6
            continue
        # Preserve genuine JSON control escapes, but not TeX commands such as
        # \beta, \frac, \rho, \theta, or \nabla.
        if escaped in "bfnrt" and (
            index + 2 >= len(text) or not text[index + 2].isalpha()
        ):
            output.extend((char, escaped))
            index += 2
            continue
        output.append("\\\\")
        repaired += 1
        index += 1
    return "".join(output), repaired


def _extract_json_object_with_key(
    text: str, required_key: str
) -> tuple[dict[str, Any], int]:
    """Extract only the intended top-level schema object from model output.

    The shared loose extractor accepts the first decodable object anywhere in
    a response. If an outer object is malformed, that can incorrectly select a
    complete nested object. Require the expected top-level key here, then make
    one schema-local recovery pass for malformed TeX backslashes in strings.
    """
    fenced = [
        match.group(1)
        for match in re.finditer(r"```(?:json)?\s*([\s\S]*?)```", text)
    ]
    candidates = [text, *fenced]
    decoder = json.JSONDecoder()
    # Try the string-local repair first. Some TeX commands (for example
    # ``\beta``) begin with a technically valid JSON control escape and would
    # otherwise decode successfully while silently corrupting the mathematics.
    for repair in (True, False):
        for candidate in candidates:
            source = candidate
            repairs = 0
            if repair:
                source, repairs = _repair_json_string_backslashes(source)
                if not repairs:
                    continue
            for start, char in enumerate(source):
                if char != "{":
                    continue
                try:
                    data, _end = decoder.raw_decode(source[start:])
                except json.JSONDecodeError:
                    continue
                if isinstance(data, dict) and required_key in data:
                    return data, repairs
    raise ValueError(
        f"model did not return a JSON object containing {required_key!r}"
    )


def _parse_semantic_plan_entries(
    ctx: Ctx, labels: Iterable[str], text: str
) -> tuple[dict[str, dict[str, Any]], dict[str, list[str]]]:
    """Parse and mechanically sanitize the compact global semantic plan.

    Invalid graph edges are removed and reported rather than repaired by a
    model. The plan is advisory, so a malformed entry can never block Phase 1;
    callers fill missing entries with deterministic blueprint-only guidance.
    """
    requested = {
        label
        for label in labels
        if label in ctx.nodes and ctx.stmt_fps.get(label)
    }
    try:
        payload, repaired_backslashes = _extract_json_object_with_key(
            text, "contracts"
        )
    except ValueError:
        return {}, {
            "<response>": [
                "response was not valid JSON with a top-level contracts array"
            ]
        }
    contracts = payload.get("contracts") if isinstance(payload, dict) else None
    if not isinstance(contracts, list):
        return {}, {"<response>": ["JSON object omitted contracts array"]}

    parsed: dict[str, dict[str, Any]] = {}
    findings: dict[str, list[str]] = {}
    if repaired_backslashes:
        findings["<response>"] = [
            f"repaired {repaired_backslashes} malformed JSON string backslash "
            "escape(s) before parsing"
        ]
    vocabulary_owners: dict[str, set[str]] = {}
    for raw in contracts:
        if not isinstance(raw, dict):
            continue
        label = str(raw.get("label") or "").strip()
        if label not in requested or label in parsed:
            continue
        representation = str(raw.get("representation") or "").strip()[:600]
        vocabulary: list[dict[str, str]] = []
        seen_names: set[str] = set()
        for item in raw.get("vocabulary") or []:
            if not isinstance(item, dict):
                continue
            name = str(item.get("name") or "").strip()
            purpose = str(item.get("purpose") or "").strip()[:240]
            if (
                not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name)
                or name in seen_names
            ):
                findings.setdefault(label, []).append(
                    f"discarded invalid or duplicate vocabulary name {name!r}"
                )
                continue
            seen_names.add(name)
            vocabulary.append({"name": name, "purpose": purpose})
            vocabulary_owners.setdefault(name, set()).add(label)
            if len(vocabulary) >= 8:
                break

        obligations = [
            str(item).strip()[:320]
            for item in raw.get("obligations") or []
            if str(item).strip()
        ][:6]
        readiness = str(raw.get("readiness") or "ready").strip().lower()
        if readiness not in SEMANTIC_READINESS_VALUES:
            findings.setdefault(label, []).append(
                f"discarded invalid readiness value {readiness!r}"
            )
            readiness = "ready"
        gap = str(raw.get("gap") or "").strip()[:500]
        if readiness != "ready" and not gap:
            findings.setdefault(label, []).append(
                "non-ready advisory omitted its gap; treating it as ready"
            )
            readiness = "ready"
        allowed_providers = _statement_uses(ctx.nodes[label])
        provider_requirements: list[dict[str, Any]] = []
        seen_providers: set[str] = set()
        for item in raw.get("provider_requirements") or []:
            if not isinstance(item, dict):
                continue
            provider = str(item.get("provider") or "").strip()
            if provider not in allowed_providers:
                findings.setdefault(label, []).append(
                    f"discarded unauthorized provider {provider!r}"
                )
                continue
            if provider in seen_providers:
                continue
            seen_providers.add(provider)
            capabilities = [
                str(value).strip()[:240]
                for value in item.get("capabilities") or []
                if str(value).strip()
            ][:8]
            provider_requirements.append(
                {"provider": provider, "capabilities": capabilities}
            )
        parsed[label] = {
            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
            "statement_fp": ctx.stmt_fps[label],
            "representation": representation,
            "vocabulary": vocabulary,
            "obligations": obligations,
            "provider_requirements": provider_requirements,
            "readiness": readiness,
            "gap": gap if readiness != "ready" else "",
            "readiness_confirmation": "pending" if readiness != "ready" else "not_needed",
        }

    # A stable helper spelling cannot be owned by two unrelated nodes. Drop
    # only the ambiguous hint; the actual Lean candidate remains free to use a
    # pipeline-namespaced helper and still goes through every normal gate.
    ambiguous = {
        name for name, owners in vocabulary_owners.items() if len(owners) > 1
    }
    if ambiguous:
        for label, entry in parsed.items():
            before = entry["vocabulary"]
            entry["vocabulary"] = [
                item for item in before if item["name"] not in ambiguous
            ]
            removed = sorted(
                item["name"] for item in before if item["name"] in ambiguous
            )
            if removed:
                findings.setdefault(label, []).append(
                    "discarded vocabulary name(s) with multiple owners: "
                    + ", ".join(removed)
                )
    return parsed, findings


def _semantic_plan_fallback_entry(ctx: Ctx, label: str) -> dict[str, Any]:
    """Deterministic advisory entry used when planning output is incomplete."""
    return {
        "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
        "statement_fp": getattr(ctx, "stmt_fps", {}).get(label, ""),
        "representation": (
            "Use the exact mathematical objects and claim in this blueprint node."
        ),
        "vocabulary": [],
        "obligations": [],
        "provider_requirements": [
            {"provider": dep, "capabilities": []}
            for dep in sorted(_statement_uses(ctx.nodes[label]))
        ],
        "readiness": "ready",
        "gap": "",
        "readiness_confirmation": "not_needed",
        "fallback": True,
    }


def _render_design_plan_entry(label: str, entry: dict[str, Any]) -> str:
    """Canonical prompt rendering of one complete structured contract."""
    lines = [
        f"NODE {label}",
        f"TARGET: {str(entry.get('target_signature') or '').strip()}",
    ]
    helpers = entry.get("helpers") or []
    if helpers:
        lines.append("OWNED HELPERS:")
        for helper in helpers:
            purpose = str(helper.get("purpose") or "").strip()
            suffix = f" -- {purpose}" if purpose else ""
            kind = str(helper.get("kind") or "def").strip()
            name = str(helper.get("name") or "").strip()
            lines.append(f"- {kind} {name}{suffix}")
            declaration = str(helper.get("declaration") or "").strip()
            if declaration:
                lines.append("  EXACT DECLARATION:")
                lines.extend(f"    {line}" for line in declaration.splitlines())
                continue
            typed_members = helper.get("members") or []
            if typed_members:
                lines.extend(
                    f"  - {str(member.get('name') or '').strip()} : "
                    f"{str(member.get('type') or '').strip()}"
                    for member in typed_members
                )
            else:
                # Compatibility for hand-built test contexts. Parsed and
                # persisted schema-v6 plans always contain typed members.
                lines.extend(
                    f"  - {str(member).strip()} : <missing type>"
                    for member in helper.get("required_members") or []
                    if str(member).strip()
                )
    decisions = [str(item).strip() for item in entry.get("decisions") or [] if str(item).strip()]
    if decisions:
        lines.append("DECISIONS:")
        lines.extend(f"- {item}" for item in decisions)
    return "\n".join(lines)


def _normalize_plan_helper(raw: Any) -> dict[str, Any] | None:
    """Normalize an auxiliary type interface owned by one blueprint target.

    Helpers requiring executable bodies or proofs are deliberately rejected.
    Their semantic content must be represented by the target declaration and
    implemented in Phase 2, where it remains covered by blueprint alignment.
    """
    if not isinstance(raw, dict):
        return None
    name = str(raw.get("name") or "").strip()
    kind = str(raw.get("kind") or "").strip().lower()
    purpose = str(raw.get("purpose") or "").strip()
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", name):
        return None
    if kind not in DESIGN_PLAN_HELPER_KINDS:
        return None
    raw_members = raw.get("members")
    if not isinstance(raw_members, list) or not raw_members:
        return None
    members: list[dict[str, str]] = []
    for item in raw_members:
        if not isinstance(item, dict):
            return None
        member_name = str(item.get("name") or "").strip()
        member_type = str(item.get("type") or "").strip()
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'.]*", member_name):
            return None
        if not member_type or len(member_type) > 4000:
            return None
        members.append({"name": member_name, "type": member_type})
    member_names = [member["name"] for member in members]
    if (
        len(members) > 32
        or len(member_names) != len(set(member_names))
        or sum(len(member["type"]) for member in members) > 24000
    ):
        return None
    return {
        "name": name[:500],
        "kind": kind,
        "members": members,
        "required_members": member_names,
        "purpose": purpose[:2000],
    }


def _normalize_plan_mathlib_aliases(ctx: Ctx, text: str) -> str:
    r"""Resolve generated spellings for nodes already settled by Mathlib.

    The planner sees both a blueprint label and its authoritative ``\lean``
    declaration. Models nevertheless sometimes derive a generated name from
    the label (for example ``def_affine_map`` instead of ``AffineMap``). That
    translation is exact and deterministic, so it belongs at ingestion rather
    than in a paid contract-correction call.
    """
    normalized = text
    mappings = sorted(
        (
            (_lean_name(label), str(node.lean_decl).strip())
            for label, node in ctx.nodes.items()
            if node.mathlibok
            and str(node.lean_decl or "").strip()
            and _lean_name(label) != str(node.lean_decl).strip()
        ),
        key=lambda item: len(item[0]),
        reverse=True,
    )
    for generated, settled in mappings:
        normalized = _lean_identifier_replace(normalized, generated, settled)
    return normalized


def _parse_design_plan_entries(
    ctx: Ctx, labels: Iterable[str], text: str
) -> dict[str, dict[str, Any]]:
    """Parse a lossless, versioned contract-plan response.

    Free-form signature text is intentionally not accepted: it cannot preserve
    helper ownership and design decisions through persistence and generation.
    """
    requested = {label for label in labels if label in ctx.nodes and ctx.stmt_fps.get(label)}
    try:
        payload = _extract_json(text)
    except ValueError:
        return {}
    contracts = payload.get("contracts") if isinstance(payload, dict) else None
    if not isinstance(contracts, list):
        return {}
    parsed: dict[str, dict[str, Any]] = {}
    for raw in contracts:
        if not isinstance(raw, dict):
            continue
        label = str(raw.get("label") or "").strip()
        signature = _normalize_plan_mathlib_aliases(
            ctx, str(raw.get("target_signature") or "").strip()
        )
        if label not in requested or not signature:
            continue
        expected_name = _lean_name(label)
        if not re.search(
            rf"(?<![A-Za-z0-9_'.]){re.escape(expected_name)}(?![A-Za-z0-9_'.])",
            signature,
        ):
            continue
        raw_helpers = raw.get("helpers") or []
        if not isinstance(raw_helpers, list):
            continue
        helpers = [
            helper
            for helper in (_normalize_plan_helper(item) for item in raw_helpers)
            if helper is not None
        ]
        if len(helpers) != len(raw_helpers):
            continue
        helper_names = [helper["name"] for helper in helpers]
        if len(helper_names) != len(set(helper_names)):
            continue
        for helper in helpers:
            for member in helper["members"]:
                member["type"] = _normalize_plan_mathlib_aliases(
                    ctx, member["type"]
                )
        parsed[label] = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": ctx.stmt_fps[label],
            "target_signature": signature[:12000],
            "helpers": helpers,
            "decisions": [
                str(item).strip()[:4000]
                for item in raw.get("decisions") or []
                if str(item).strip()
            ],
        }
    target_names = {
        _lean_name(label)
        for label, node in ctx.nodes.items()
        if not node.mathlibok
    }
    helper_owners: dict[str, set[str]] = {}
    for label, entry in parsed.items():
        for helper in entry["helpers"]:
            helper_owners.setdefault(helper["name"], set()).add(label)
    invalid_owners = {
        label
        for helper_name, owners in helper_owners.items()
        if len(owners) != 1 or helper_name in target_names
        for label in owners
    }
    for label in invalid_owners:
        parsed.pop(label, None)
    return parsed


def _design_plan_audit_fingerprint(ctx: Ctx, label: str) -> str:
    """Identity of one blueprint contract and its proposed Lean interface."""
    entry = getattr(ctx, "design_plan_entries", {}).get(label) or {}
    material = {
        "label": label,
        "statement_fp": getattr(ctx, "stmt_fps", {}).get(label, ""),
        "contract": {
            "schema_version": int(entry.get("schema_version") or 0),
            "target_signature": str(entry.get("target_signature") or ""),
            "helpers": entry.get("helpers") or [],
            "decisions": entry.get("decisions") or [],
        },
        "paper": hashlib.sha256(
            str(getattr(ctx, "paper_text", "")).encode("utf-8")
        ).hexdigest(),
    }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _findings_require_plan_revision(
    ctx: Ctx | Iterable[SkeletonFinding],
    findings: Iterable[SkeletonFinding] | None = None,
) -> bool:
    """Return whether candidate errors originate in the interface plan.

    Only mechanically invalid accepted contracts belong here. An unplanned
    helper invented by statement generation is a generation error when the
    accepted contract never requested that declaration; routing it back to
    plan correction repeatedly edits an already valid plan without addressing
    the bad output. Every Phase-1 path uses this predicate so actual contract
    closure failures do not fall through to compiler patching.
    """
    if findings is None:
        findings = ctx  # compatibility for direct predicate callers
        entries: dict[str, dict[str, Any]] = {}
    else:
        entries = getattr(ctx, "design_plan_entries", {}) or {}
    return any(
        finding.category in _PLAN_REVISION_FINDING_CATEGORIES
        and (
            finding.label is None
            or (entries.get(finding.label) or {}).get("origin")
            != "phase1_candidate"
        )
        for finding in findings
    )


def _mentions_lean_symbol(text: str, name: str) -> bool:
    """Match a generated Lean name, including its use as a namespace prefix."""
    return bool(
        name
        and re.search(
            rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'])",
            text,
        )
    )


def _design_plan_public_interface_fragments(entry: dict[str, Any]) -> list[str]:
    """Lean-aware text fragments that constitute one planned public interface.

    Target declarations go through the same declaration parser used at the
    model-output boundary. Helper fields and inductive constructors are already
    normalized as typed members by the versioned plan parser. Purposes and
    free-form decisions are intentionally excluded: prose cannot satisfy a
    declaration-level blueprint dependency.
    """
    signature = str(entry.get("target_signature") or "")
    parsed = _parse_module(signature)
    fragments = [decl.text for decl in parsed.decls]
    if not fragments and signature.strip():
        # Preserve useful closure evidence for a malformed declaration; the
        # canonical-target check reports the syntax defect separately.
        fragments.append(signature)
    fragments.extend(
        str(helper.get("declaration") or "")
        for helper in entry.get("helpers") or []
        if str(helper.get("declaration") or "").strip()
    )
    fragments.extend(
        str(member.get("type") or "")
        for helper in entry.get("helpers") or []
        for member in helper.get("members") or []
        if isinstance(member, dict) and str(member.get("type") or "").strip()
    )
    return fragments


def _design_plan_dependency_closure_details(
    ctx: Ctx, label: str
) -> dict[str, list[str]]:
    """Observe every statement dependency on the typed plan surface."""
    entry = getattr(ctx, "design_plan_entries", {}).get(label) or {}
    fragments = _design_plan_public_interface_fragments(entry)
    required: list[str] = []
    represented: list[str] = []
    missing: list[str] = []
    generated_providers: list[str] = []
    node = ctx.nodes.get(label)
    for dependency in sorted(_statement_uses(node) if node is not None else set()):
        dependency_node = ctx.nodes.get(dependency)
        if dependency_node is None:
            continue
        lean_name = (
            str(dependency_node.lean_decl or "").strip()
            if dependency_node.mathlibok
            else _lean_name(dependency)
        )
        rendered = f"{dependency} -> `{lean_name or '<missing Lean mapping>'}`"
        required.append(rendered)
        if lean_name and any(
            _mentions_lean_symbol(fragment, lean_name) for fragment in fragments
        ):
            represented.append(rendered)
            continue
        missing.append(rendered)
        if not dependency_node.mathlibok:
            generated_providers.append(dependency)
    return {
        "required": required,
        "represented": represented,
        "missing": missing,
        "generated_providers": generated_providers,
    }


def _design_plan_owner_helper_cycle_paths(ctx: Ctx, label: str) -> list[str]:
    """Find declaration-order cycles already forced by a target/helper plan."""
    entry = getattr(ctx, "design_plan_entries", {}).get(label) or {}
    target = _lean_name(label)
    helpers = {
        str(helper.get("name") or "").strip(): helper
        for helper in entry.get("helpers") or []
        if str(helper.get("name") or "").strip()
    }
    names = [target, *helpers]
    texts = {target: str(entry.get("target_signature") or "")}
    texts.update(
        {
            name: "\n".join(
                str(member.get("type") or "")
                for member in helper.get("members") or []
                if isinstance(member, dict)
            )
            for name, helper in helpers.items()
        }
    )
    graph = {
        source: {
            destination
            for destination in names
            if destination != source
            and _mentions_lean_symbol(texts.get(source, ""), destination)
        }
        for source in names
    }

    def path(source: str, destination: str) -> list[str] | None:
        todo = [[source]]
        while todo:
            candidate = todo.pop(0)
            current = candidate[-1]
            for neighbor in sorted(graph.get(current, set())):
                if neighbor == destination:
                    return [*candidate, neighbor]
                if neighbor not in candidate:
                    todo.append([*candidate, neighbor])
        return None

    cycles: list[str] = []
    for helper in sorted(helpers):
        outward = path(target, helper)
        returning = path(helper, target)
        if outward and returning:
            cycles.append(" -> ".join([*outward, *returning[1:]]))
    return list(dict.fromkeys(cycles))


def _planned_target_members(signature: str, target_name: str) -> set[str]:
    """Extract the member surface exposed by a planned target declaration.

    This intentionally recognizes only declaration syntax whose dotted public
    surface Lean creates deterministically: structure/class fields and
    inductive constructors. It does not guess methods from prose or decisions.
    """
    match = re.search(
        rf"\b(structure|class|inductive)\s+{re.escape(target_name)}"
        rf"(?![A-Za-z0-9_'])[\s\S]*?\bwhere\b([\s\S]*)",
        signature,
    )
    if not match:
        return set()
    kind, body = match.group(1), match.group(2)
    if kind == "inductive":
        return set(
            re.findall(
                r"(?:^|[;\n])\s*\|\s*([A-Za-z_][A-Za-z0-9_']*)",
                body,
            )
        )
    return set(
        re.findall(
            r"(?:^|[;\n])\s*([A-Za-z_][A-Za-z0-9_']*)\s*:",
            body,
        )
    )


def _planned_target_result_type(signature: str, target_name: str) -> str:
    """Return the top-level result type of a planned target declaration.

    Binder annotations may contain their own colons, so this scans the parsed
    declaration and accepts only a colon outside parentheses, brackets, and
    braces. The result is used only to connect a target value to an interface
    helper already owned by the same plan entry.
    """
    declaration = next(
        (
            decl.text
            for decl in _parse_module(signature).decls
            if decl.name == target_name
        ),
        "",
    )
    deferred = _terminal_sorry_interface_text(declaration)
    declaration_surface = deferred if deferred is not None else declaration
    name_match = re.search(
        rf"\b{re.escape(target_name)}(?![A-Za-z0-9_'])",
        declaration_surface,
    )
    if not name_match:
        return ""

    tail = declaration_surface[name_match.end():]
    depths = {"(": 0, "[": 0, "{": 0}
    closing = {")": "(", "]": "[", "}": "{"}
    for index, char in enumerate(tail):
        if char in depths:
            depths[char] += 1
        elif char in closing:
            opener = closing[char]
            depths[opener] = max(0, depths[opener] - 1)
        elif (
            char == ":"
            and tail[index : index + 2] != ":="
            and not any(depths.values())
        ):
            result = tail[index + 1:]
            if deferred is None:
                result = result.split(":=", 1)[0]
            return result.strip()
    return ""


def _lean_surface_tokens(text: str) -> tuple[str, ...]:
    """Tokenize a declaration surface for conservative exact comparison.

    This is deliberately stricter than Lean equivalence. It ignores formatting
    and comments, but it does not treat alternative types or formulations as
    equal. A false negative merely keeps the ordinary generation-retry route;
    a positive result proves regeneration under the unchanged plan cannot
    repair a semantic omission in that plan.
    """
    without_block_comments = re.sub(r"/-[\s\S]*?-/", " ", text)
    without_comments = re.sub(r"--[^\n]*", " ", without_block_comments)
    return tuple(
        re.findall(
            r"[A-Za-z_][A-Za-z0-9_'.]*|\d+(?:\.\d+)?|:=|=>|->|[^\s]",
            without_comments,
        )
    )


def _contains_token_sequence(
    haystack: tuple[str, ...], needle: tuple[str, ...]
) -> bool:
    """Return whether one exact Lean token sequence occurs contiguously."""
    if not needle or len(needle) > len(haystack):
        return False
    width = len(needle)
    return any(
        haystack[index:index + width] == needle
        for index in range(len(haystack) - width + 1)
    )


def _candidate_exactly_realizes_plan(
    ctx: Ctx,
    label: str,
    code: str,
    *,
    allow_revised_plan: bool = False,
) -> bool:
    """Prove that a compiled Phase-1 interface copied its accepted plan.

    The check covers the target declaration header plus every plan-owned
    helper's kind, complete member set, and typed member declarations. Plan
    prose is intentionally irrelevant: if blueprint content appears only in a
    decision but not in this complete public interface, the plan itself is the
    artifact that must change.
    """
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label) or {}
    if (
        _uses_blueprint_direct_generation(ctx, label)
        or
        int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
        or (
            not allow_revised_plan
            and int(entry.get("semantic_revision_count") or 0) >= 1
        )
    ):
        return False

    target_name = _lean_name(label)
    parsed = _parse_module(code)
    actual_by_name = {decl.name: decl for decl in parsed.decls if decl.name}
    actual_target = actual_by_name.get(target_name)
    planned_target = next(
        (
            decl
            for decl in _parse_module(
                str(entry.get("target_signature") or "")
            ).decls
            if decl.name == target_name
        ),
        None,
    )
    if actual_target is None or planned_target is None:
        return False

    helper_aliases = {
        str(helper.get("name") or "").strip(): _owned_helper_name(
            ctx, str(helper.get("name") or "").strip(), [label]
        )
        for helper in entry.get("helpers") or []
        if str(helper.get("name") or "").strip()
    }

    def canonical_planned_text(text: str) -> str:
        result = text
        for original, canonical in sorted(
            helper_aliases.items(), key=lambda item: len(item[0]), reverse=True
        ):
            result = _lean_identifier_replace(result, original, canonical)
        return result

    expected_target = canonical_planned_text(_decl_interface_text(planned_target))
    actual_target_surface = _decl_interface_text(actual_target)
    if _lean_surface_tokens(expected_target) != _lean_surface_tokens(
        actual_target_surface
    ):
        return False

    for helper in entry.get("helpers") or []:
        helper_name = str(helper.get("name") or "").strip()
        canonical_name = helper_aliases.get(helper_name, helper_name)
        actual_helper = actual_by_name.get(canonical_name) or actual_by_name.get(
            helper_name
        )
        if actual_helper is None:
            return False
        expected_kind = str(helper.get("kind") or "").strip()
        if actual_helper.kind != expected_kind:
            return False
        exact_declaration = str(helper.get("declaration") or "").strip()
        if exact_declaration and _lean_surface_tokens(
            exact_declaration
        ) != _lean_surface_tokens(_decl_interface_text(actual_helper)):
            return False
        expected_members = {
            str(member.get("name") or "").strip()
            for member in helper.get("members") or []
            if isinstance(member, dict)
            and str(member.get("name") or "").strip()
        }
        if exact_declaration and not expected_members:
            expected_members = {
                str(member).strip()
                for member in helper.get("required_members") or []
                if str(member).strip()
            }
        if _planned_target_members(
            actual_helper.text, actual_helper.name or canonical_name
        ) != expected_members:
            return False
        helper_tokens = _lean_surface_tokens(actual_helper.text)
        for member in helper.get("members") or []:
            if not isinstance(member, dict):
                return False
            member_name = str(member.get("name") or "").strip()
            member_type = canonical_planned_text(
                str(member.get("type") or "").strip()
            )
            if not _contains_token_sequence(
                helper_tokens,
                _lean_surface_tokens(f"{member_name} : {member_type}"),
            ):
                return False
    return True


def _candidate_target_exactly_realizes_plan(
    ctx: Ctx, label: str, code: str
) -> bool:
    """Return whether the emitted target header exactly copies its plan.

    A compiler can reject an identifier in the target signature before the
    complete helper surface is usable. Matching only the target is sufficient
    for that narrow diagnosis: if the rejected identifier occurs in the
    accepted target signature too, statement regeneration cannot remove it
    without violating the plan.
    """
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label) or {}
    if (
        _uses_blueprint_direct_generation(ctx, label)
        or int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
    ):
        return False

    target_name = _lean_name(label)
    actual = next(
        (decl for decl in _parse_module(code).decls if decl.name == target_name),
        None,
    )
    planned = next(
        (
            decl
            for decl in _parse_module(
                str(entry.get("target_signature") or "")
            ).decls
            if decl.name == target_name
        ),
        None,
    )
    if actual is None or planned is None:
        return False

    expected = _decl_interface_text(planned)
    for helper in entry.get("helpers") or []:
        helper_name = str(helper.get("name") or "").strip()
        if helper_name:
            expected = _lean_identifier_replace(
                expected,
                helper_name,
                _owned_helper_name(ctx, helper_name, [label]),
            )
    return _lean_surface_tokens(expected) == _lean_surface_tokens(
        _decl_interface_text(actual)
    )


def _plan_owned_unknown_lean_names(
    ctx: Ctx, label: str, output: str
) -> tuple[set[str], set[str]]:
    """Return compiler-unknown names in the target and complete plan surface."""
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label) or {}
    target_tokens = set(
        _lean_surface_tokens(str(entry.get("target_signature") or ""))
    )
    planned_text = "\n".join(
        [str(entry.get("target_signature") or "")]
        + [
            str(member.get("type") or "")
            for helper in entry.get("helpers") or []
            for member in helper.get("members") or []
            if isinstance(member, dict)
        ]
    )
    planned_tokens = set(_lean_surface_tokens(planned_text))
    unknown = {
        name
        for name in _UNKNOWN_LEAN_NAME_RE.findall(output)
        if name in planned_tokens
    }
    return unknown & target_tokens, unknown


def _phase1_compile_plan_defects(
    ctx: Ctx,
    labels: Iterable[str],
    code: str,
    output: str,
) -> dict[str, str]:
    """Classify compile failures that regeneration cannot fix under the plan.

    The direct case requires an unknown Lean name copied by an exact target
    header. Ambiguous failures receive one normal compiler correction; only an
    identical error shape under the same plan fingerprint and an exact full
    public interface is routed to plan correction on recurrence.
    """
    defects: dict[str, str] = {}
    current_shape = _lean_error_shape(output)
    with _STATE_LOCK:
        candidates = copy.deepcopy(
            getattr(ctx, "generation_candidates", {}) or {}
        )
    for label in labels:
        if label not in getattr(ctx, "nodes", {}):
            continue
        if (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            == "phase1_candidate"
        ):
            # The typed contract came from this same candidate. Compiler
            # feedback must revise the candidate and contract together, not
            # invoke the legacy independent plan-correction path.
            continue
        target_unknown, plan_unknown = _plan_owned_unknown_lean_names(
            ctx, label, output
        )
        exact_target = _candidate_target_exactly_realizes_plan(
            ctx, label, code
        )
        exact_interface = _candidate_exactly_realizes_plan(
            ctx, label, code, allow_revised_plan=True
        )
        actionable_unknown = (
            target_unknown if exact_target else set()
        ) | (plan_unknown if exact_interface else set())
        if actionable_unknown:
            defects[label] = (
                "accepted plan contains compiler-unknown Lean name(s): "
                + ", ".join(sorted(actionable_unknown))
            )
            continue

        previous = candidates.get(label) or {}
        if (
            str(previous.get("plan_fp") or "")
            == _candidate_plan_fingerprint(ctx, label)
            and str(previous.get("lean_status") or "") == "failed"
            and str(previous.get("lean_output") or "")
            and _lean_error_shape(str(previous.get("lean_output") or ""))
            == current_shape
            and exact_interface
        ):
            defects[label] = (
                "exact plan realization repeated the same Lean compiler "
                "failure under the unchanged plan"
            )
    return defects


def _plan_realized_semantic_rejections(
    ctx: Ctx, labels: Iterable[str], code: str
) -> set[str]:
    """Return rejected labels that regeneration cannot fix under this plan."""
    return {
        label
        for label in labels
        if label in getattr(ctx, "nodes", {})
        and (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            != "phase1_candidate"
        )
        and _candidate_exactly_realizes_plan(ctx, label, code)
    }


def _revise_audit_reported_plan_defects(
    ctx: Ctx,
    audit: AlignmentAuditResult,
    *,
    layer_no: int,
    source: str,
    skip_labels: Iterable[str] = (),
) -> set[str]:
    """Correct plan-owned semantic defects before retrying stale-plan Lean.

    The independent statement critic sees the blueprint, current plan, and
    emitted Lean together. A ``plan`` or ``both`` origin is actionable only
    when the critic also names concrete blueprint obligations absent from the
    plan; ``_model_alignment_audit`` enforces that evidence requirement. The
    existing plan-correction transaction remains responsible for mechanical
    closure validation, candidate provenance, and the later semantic re-audit.
    """
    eligible = (
        audit.labels_for("lean-generation")
        & audit.labels_for_origin("plan", "both")
    )
    eligible.difference_update(skip_labels)
    eligible = {
        label
        for label in eligible
        if (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            != "phase1_candidate"
        )
    }
    if not eligible:
        return set()
    requirements = audit.plan_requirements_for(sorted(eligible))
    evidence = audit.reason_for(sorted(eligible))
    if requirements:
        evidence += "\nBlueprint requirements absent from the current plan:\n- "
        evidence += "\n- ".join(requirements)
    evidence_identities = {
        label: audit.failure_identity_for(label)
        for label in eligible
        if audit.failure_identity_for(label)
    }
    revision_kwargs = (
        {"evidence_identities_by_label": evidence_identities}
        if evidence_identities
        else {}
    )
    revised = _revise_exhausted_phase1_contracts(
        ctx,
        eligible,
        evidence,
        policy="audit_origin_plan_defect",
        **revision_kwargs,
    )
    if revised:
        origins = {
            label: audit.origins_by_label.get(label, "lean")
            for label in sorted(revised)
        }
        _record(
            ctx.telemetry,
            "phase1_audit_origin_plan_revision",
            layer=layer_no,
            source=source,
            labels=sorted(revised),
            failure_origins=origins,
            missing_plan_requirements={
                label: audit.plan_requirements_by_label.get(label, [])
                for label in sorted(revised)
            },
            avoided_route="stale_plan_generation_retry",
        )
        _log(
            "  statement audit located the mismatch in the current plan; "
            "revised it before another Lean generation attempt: "
            + ", ".join(sorted(revised))
        )
    return revised


def _activate_audit_reported_candidate_plan_defects(
    ctx: Ctx,
    audit: AlignmentAuditResult,
    *,
    layer_no: int,
    source: str,
    skip_labels: Iterable[str] = (),
) -> set[str]:
    """Route candidate-owned plan omissions to blueprint-direct generation.

    ``origin == phase1_candidate`` means the typed contract was derived from a
    generated Lean candidate rather than from the global design-plan table.
    There is therefore no independent plan object for
    ``_revise_exhausted_phase1_contracts`` to repair. If the audit gives
    concrete blueprint requirements missing from that candidate-owned contract,
    regenerating under the same candidate provenance is stale work; switch this
    exact statement fingerprint to the existing blueprint-direct path instead.
    """
    eligible = (
        audit.labels_for("lean-generation")
        & audit.labels_for_origin("plan", "both")
    )
    eligible.difference_update(skip_labels)
    eligible = {
        label
        for label in eligible
        if (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            == "phase1_candidate"
        )
        and audit.plan_requirements_by_label.get(label)
        and not _uses_blueprint_direct_generation(ctx, label)
    }
    if not eligible:
        return set()

    evidence_by_label = {}
    for label in sorted(eligible):
        evidence = audit.reason_for([label])
        requirements = audit.plan_requirements_by_label.get(label, [])
        if requirements:
            evidence += "\nBlueprint requirements absent from the candidate-owned contract:\n- "
            evidence += "\n- ".join(requirements)
        evidence_by_label[label] = evidence

    activated = _activate_blueprint_direct_generation(
        ctx,
        eligible,
        audit.reason_for(sorted(eligible)),
        source=f"{source}_candidate_plan_defect",
        evidence_by_label=evidence_by_label,
    )
    if activated:
        _record(
            ctx.telemetry,
            "phase1_audit_origin_candidate_plan_direct",
            layer=layer_no,
            source=source,
            labels=sorted(activated),
            failure_origins={
                label: audit.origins_by_label.get(label, "lean")
                for label in sorted(activated)
            },
            missing_plan_requirements={
                label: audit.plan_requirements_by_label.get(label, [])
                for label in sorted(activated)
            },
            avoided_route="candidate_owned_stale_generation_retry",
        )
        _log(
            "  statement audit located the mismatch in a candidate-owned "
            "contract; switching to blueprint-direct generation for: "
            + ", ".join(sorted(activated))
        )
    return activated


def _audit_plan_revision_request(
    ctx: Ctx,
    audit: AlignmentAuditResult,
    *,
    layer_no: int,
    source: str,
) -> RepairRequest | None:
    """Build the common retry request after an audit-driven plan revision."""
    revised = _revise_audit_reported_plan_defects(
        ctx, audit, layer_no=layer_no, source=source
    )
    if not revised:
        return None
    ordered = sorted(revised)
    return RepairRequest(
        audit.reason_for(ordered),
        ordered,
        section_labels=ordered,
        authorizes_blueprint_repair=False,
        failure_route=FailureScopeDecision(
            action="independent",
            parts=tuple((label,) for label in ordered),
            failed_labels=tuple(ordered),
            accepted_labels=(),
        ),
        plan_revision_required=True,
    )


def _design_plan_symbol_surfaces(
    ctx: Ctx,
) -> tuple[dict[str, set[str]], dict[str, str]]:
    """Return planned generated symbols and the blueprint node owning each."""
    entries = getattr(ctx, "design_plan_entries", {})
    surfaces: dict[str, set[str]] = {}
    owners: dict[str, str] = {}
    for label, entry in entries.items():
        if label not in ctx.nodes or _uses_blueprint_direct_generation(ctx, label):
            continue
        target_name = _lean_name(label)
        signature = str(entry.get("target_signature") or "")
        target_members = _planned_target_members(signature, target_name)
        result_type = _planned_target_result_type(signature, target_name)
        owners[target_name] = label
        for helper in entry.get("helpers") or []:
            helper_name = str(helper.get("name") or "").strip()
            if not helper_name:
                continue
            members = {
                str(member).strip()
                for member in helper.get("required_members") or []
                if str(member).strip()
            }
            canonical = _owned_helper_name(ctx, helper_name, [label])
            if any(
                _mentions_lean_symbol(result_type, spelling)
                for spelling in (helper_name, canonical)
            ):
                target_members.update(members)
            for spelling in (helper_name, canonical):
                surfaces[spelling] = set(members)
                owners[spelling] = label
        surfaces[target_name] = target_members
    return surfaces, owners


def _design_plan_closure_fingerprint(ctx: Ctx, label: str) -> str:
    """Fingerprint one contract against the complete planned symbol surface."""
    surfaces, owners = _design_plan_symbol_surfaces(ctx)
    material = {
        "closure_version": DESIGN_PLAN_CLOSURE_VERSION,
        "contract": _design_plan_audit_fingerprint(ctx, label),
        "symbols": {
            name: {"owner": owners[name], "members": sorted(members)}
            for name, members in sorted(surfaces.items())
        },
    }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True).encode("utf-8")
    ).hexdigest()


def _design_plan_contract_closure_issues(
    ctx: Ctx, labels: Iterable[str]
) -> list[PlanClosureFinding]:
    """Reject mechanically unrealizable plan references before generation.

    This is a symbol-table check, not a semantic audit. In particular, every
    dotted reference to a generated target/helper must name a member exposed by
    that planned declaration, and a helper reference must remain inside the
    consumer's statement dependency closure.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    surfaces, owners = _design_plan_symbol_surfaces(ctx)
    findings: list[PlanClosureFinding] = []
    for label in labels:
        if _uses_blueprint_direct_generation(ctx, label):
            continue
        entry = entries.get(label) or {}
        signature = str(entry.get("target_signature") or "")
        interface_fragments = _design_plan_public_interface_fragments(entry)
        interface_text = "\n".join(interface_fragments)
        allowed = _transitive_statement_dependencies(ctx.nodes, label)
        local: list[PlanClosureFinding] = []
        target_name = _lean_name(label)
        declared = [
            (decl.kind, decl.name or "<anonymous>")
            for decl in _parse_module(signature).decls
        ]
        target_declarations = [
            (kind, name) for kind, name in declared if name == target_name
        ]
        extra_declarations = [
            (kind, name) for kind, name in declared if name != target_name
        ]
        if len(target_declarations) != 1:
            local.append(
                PlanClosureFinding(
                    label,
                    f"{label}: target signature must declare exactly one canonical "
                    f"target named `{target_name}`; found "
                    + (
                        str(len(target_declarations))
                        if declared
                        else "no declarations"
                    ),
                )
            )
        if extra_declarations:
            rendered = ", ".join(
                f"`{kind} {name}`" for kind, name in extra_declarations
            )
            local.append(
                PlanClosureFinding(
                    label,
                    f"{label}: target signature declares additional public target(s): "
                    f"{rendered}. One blueprint node owns exactly one canonical public "
                    f"declaration, `{target_name}`. If the node defines several "
                    "mathematical operations, package them as fields of one "
                    "plan-owned structure/class interface and make the canonical "
                    "target return that interface",
                )
            )
        generated = {
            _lean_name(other): other
            for other, other_node in ctx.nodes.items()
            if not other_node.mathlibok
        }
        unexpected_dependencies = sorted(
            other
            for lean_name, other in generated.items()
            if other != label
            and other not in allowed
            and _mentions_lean_symbol(interface_text, lean_name)
        )
        if unexpected_dependencies:
            local.append(
                PlanClosureFinding(
                    label,
                    f"{label}: public interface references dependency/dependencies "
                    "outside its statement dependency closure: "
                    + ", ".join(
                        f"{dependency} -> `{_lean_name(dependency)}`"
                        for dependency in unexpected_dependencies
                    ),
                    unauthorized_dependencies=tuple(unexpected_dependencies),
                )
            )
        for symbol, members in surfaces.items():
            owner = owners.get(symbol)
            mentions_symbol = _mentions_lean_symbol(interface_text, symbol)
            unauthorized_owner = bool(
                owner
                and owner != label
                and owner not in allowed
                and mentions_symbol
            )
            if unauthorized_owner:
                # The consumer invented an out-of-closure reference. Do not
                # also claim that the healthy provider is missing the invented
                # member: that would block and rewrite the provider for a
                # defect owned entirely by this consumer.
                if symbol != _lean_name(owner):
                    local.append(
                        PlanClosureFinding(
                            label,
                            f"{label}: public interface references helper `{symbol}` "
                            f"owned by {owner}, outside its statement dependency closure",
                            unauthorized_dependencies=(owner,),
                        )
                    )
                continue
            dotted_members = set(
                re.findall(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(symbol)}\."
                    r"([A-Za-z_][A-Za-z0-9_']*)",
                    interface_text,
                )
            )
            for member in sorted(dotted_members - members):
                local.append(
                    PlanClosureFinding(
                        label,
                        f"{label}: target signature requires `{symbol}.{member}`, "
                        f"but planned declaration `{symbol}` exposes no such member",
                        provider=owners.get(symbol),
                        missing_provider_members=(f"{symbol}.{member}",),
                    )
                )
        cycle_paths = _design_plan_owner_helper_cycle_paths(ctx, label)
        if cycle_paths:
            local.append(
                PlanClosureFinding(
                    label,
                    f"{label}: interface plan creates impossible target/helper "
                    "declaration cycle(s): " + "; ".join(cycle_paths),
                    cycle_paths=tuple(cycle_paths),
                )
            )
        findings.extend(local)
    return findings


def _design_plan_contract_closure_findings(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, list[str]]:
    """Compatibility view of structured closure issues grouped by consumer."""
    findings: dict[str, list[str]] = {}
    for issue in _design_plan_contract_closure_issues(ctx, labels):
        findings.setdefault(issue.consumer, []).append(issue.message)
    return {
        label: list(dict.fromkeys(messages))
        for label, messages in findings.items()
    }


def _design_plan_unauthorized_reference_findings(
    ctx: Ctx, labels: Iterable[str]
) -> list[str]:
    """Reject generated target references outside statement authorization."""
    return [
        issue.message
        for issue in _design_plan_contract_closure_issues(ctx, labels)
        if issue.unauthorized_dependencies
    ]


def _design_plan_invalid_mathlib_alias_findings(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, list[str]]:
    r"""Reject generated aliases for blueprint nodes already settled by Mathlib.

    A ``\mathlibok`` node is not generated by this pipeline: its ``\lean``
    mapping is the authoritative declaration name. The planner may omit a
    proof-only Mathlib dependency from a public contract, but if it mentions
    that dependency it must use the settled name rather than the generated
    spelling derived from the blueprint label.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    mappings = {
        _lean_name(dep): (dep, str(node.lean_decl).strip())
        for dep, node in ctx.nodes.items()
        if node.mathlibok
        and str(node.lean_decl or "").strip()
        and _lean_name(dep) != str(node.lean_decl).strip()
    }
    findings: dict[str, list[str]] = {}
    for label in labels:
        if _uses_blueprint_direct_generation(ctx, label):
            continue
        contract = "\n".join(
            _design_plan_public_interface_fragments(entries.get(label) or {})
        )
        invalid = [
            (generated, dep, settled)
            for generated, (dep, settled) in mappings.items()
            if _mentions_lean_symbol(contract, generated)
        ]
        if invalid:
            findings[label] = [
                f"{label}: contract uses generated alias `{generated}` for "
                f"Mathlib-owned {dep}; use its settled `\\lean` declaration "
                f"`{settled}` instead"
                for generated, dep, settled in sorted(invalid)
            ]
    return findings


def _design_plan_dependency_findings(ctx: Ctx, labels: Iterable[str]) -> list[str]:
    r"""Reject mechanically unauthorized references without semantic guessing.

    Missing ``\uses`` names remain observable in closure telemetry, but they
    are not mechanically conclusive. A theorem used by a proof normally must
    not occur in the theorem's public proposition, while a definition used in
    an equation often must. The mandatory statement-alignment audit decides
    whether the generated contract preserves the actual blueprint text.
    """
    return _design_plan_unauthorized_reference_findings(ctx, labels)


def _validate_design_plan_contract_closure(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, list[str]]:
    """Validate and fingerprint the deterministic plan-to-generation handoff."""
    entries = getattr(ctx, "design_plan_entries", {})
    ordered = [
        label
        for label in labels
        if label in entries and not _uses_blueprint_direct_generation(ctx, label)
    ]
    uncached = [
        label
        for label in ordered
        if str(entries[label].get("closure_fp") or "")
        != _design_plan_closure_fingerprint(ctx, label)
    ]
    if not uncached:
        if ordered:
            _record(
                ctx.telemetry,
                "phase1_design_plan_closure",
                labels=ordered,
                status="cache_hit",
            )
        return {}

    findings = _design_plan_contract_closure_findings(ctx, uncached)
    for label, messages in _design_plan_invalid_mathlib_alias_findings(
        ctx, uncached
    ).items():
        findings[label] = [*messages, *findings.get(label, [])]
    dependency_closure = {
        label: _design_plan_dependency_closure_details(ctx, label)
        for label in uncached
    }
    for label in uncached:
        if label not in findings:
            entries[label]["closure_fp"] = _design_plan_closure_fingerprint(
                ctx, label
            )
        else:
            entries[label].pop("closure_fp", None)
    _sync_design_plan(ctx)
    _record(
        ctx.telemetry,
        "phase1_design_plan_closure",
        labels=uncached,
        status="rejected" if findings else "accepted",
        rejected_labels=sorted(findings),
        statement_fingerprints={
            label: ctx.stmt_fps.get(label, "") for label in uncached
        },
        plan_fingerprints={
            label: _design_plan_audit_fingerprint(ctx, label)
            for label in uncached
        },
        dependency_closure=dependency_closure,
        findings=[
            finding
            for label in sorted(findings)
            for finding in findings[label]
        ],
    )
    return findings


def _design_plan_closure_repair_components(
    ctx: Ctx, findings: dict[str, list[str]]
) -> list[list[str]]:
    """Connected provider-consumer units that must be corrected atomically.

    Findings about a consumer's unauthorized dependency remain consumer-only.
    Missing member-surface findings join the consumer to the provider that
    owns that surface. Shared providers therefore combine all affected
    consumers into one coherent correction instead of letting independent
    calls invent mutually incompatible member names.
    """
    affected = set(findings)
    adjacency: dict[str, set[str]] = {label: set() for label in affected}
    for issue in _design_plan_contract_closure_issues(ctx, findings):
        if issue.consumer not in findings:
            continue
        # A consumer that omits a required dependency is the broken contract;
        # the dependency provider itself is not broken and must remain
        # schedulable. Only a missing member on a provider-owned surface makes
        # provider and consumer an atomic repair unit.
        providers = (
            {issue.provider}
            if issue.provider is not None and issue.missing_provider_members
            else set()
        )
        for provider in providers:
            if provider == issue.consumer or provider not in ctx.nodes:
                continue
            affected.add(provider)
            adjacency.setdefault(issue.consumer, set()).add(provider)
            adjacency.setdefault(provider, set()).add(issue.consumer)

    ordered = _design_plan_order(ctx, affected)
    position = {label: index for index, label in enumerate(ordered)}
    components: list[list[str]] = []
    unseen = set(affected)
    while unseen:
        seed = min(unseen, key=position.get)
        todo = [seed]
        component: set[str] = set()
        while todo:
            label = todo.pop()
            if label in component:
                continue
            component.add(label)
            todo.extend(adjacency.get(label, set()) - component)
        unseen.difference_update(component)
        components.append(
            sorted(component, key=position.get)
        )
    return components


def _closure_blocked_labels(
    ctx: Ctx, findings: dict[str, list[str]]
) -> set[str]:
    """Contracts that cannot freeze while the current closure findings remain."""
    return {
        label
        for component in _design_plan_closure_repair_components(ctx, findings)
        for label in component
    }


def _closure_findings_for_scope(
    ctx: Ctx,
    findings: dict[str, list[str]],
    scope: Iterable[str],
) -> dict[str, list[str]]:
    """Select complete closure components touching the requested labels."""
    requested = set(scope)
    selected_consumers: set[str] = set()
    for component in _design_plan_closure_repair_components(ctx, findings):
        if requested & set(component):
            selected_consumers.update(label for label in component if label in findings)
    return {
        label: findings[label]
        for label in findings
        if label in selected_consumers
    }


def _evaluate_design_plan_candidate(
    ctx: Ctx,
    ordered: list[str],
    entries: dict[str, dict[str, Any]],
    candidate_id: str,
) -> DesignPlanCandidate:
    """Score a plan with the existing closure rules without changing live state."""
    # A losing tournament lane may finish after an admissible sibling has
    # already allowed Phase 1 to continue. Score against an isolated shallow
    # context so that late deterministic evaluation can never swap candidate
    # entries into the live run, even briefly. Graph and statement data remain
    # shared read-only; only plan state is candidate-local.
    candidate_ctx = copy.copy(ctx)
    candidate_ctx.design_plan_entries = entries
    candidate_ctx.design_plan = ""
    missing = [label for label in ordered if label not in entries]
    findings = _design_plan_contract_closure_findings(candidate_ctx, ordered)
    for label, messages in _design_plan_invalid_mathlib_alias_findings(
        candidate_ctx, ordered
    ).items():
        findings.setdefault(label, []).extend(messages)
    findings = {
        label: list(dict.fromkeys(messages))
        for label, messages in findings.items()
    }
    components = _design_plan_closure_repair_components(candidate_ctx, findings)
    blocked = {label for component in components for label in component}
    return DesignPlanCandidate(
        candidate_id=candidate_id,
        entries=copy.deepcopy(entries),
        missing=missing,
        findings=findings,
        blocked=blocked,
        components=components,
    )


def _initial_plan_admission(
    ctx: Ctx,
    ordered: list[str],
    candidate: DesignPlanCandidate,
) -> tuple[bool, list[str], list[str]]:
    """Decide whether a complete plan is safe to start Phase 1 with.

    Requiring zero findings over every future consumer rejected every known
    fast historical plan and recreated the expensive global-correction path.
    The non-arbitrary admission boundary is therefore the same dependency
    boundary Phase 1 can actually execute now: the complete initial bottom-up
    frontier. Every requested contract must exist, and every initial provider
    must be mechanically closed. Future consumers retain their existing
    just-in-time frontier gate before they can generate Lean.
    """
    pending = set(ordered)
    generated = {
        label for label, node in ctx.nodes.items() if not node.mathlibok
    }
    frozen = generated - pending
    frontier = _bottom_up_ready_frontier(ctx.nodes, pending, frozen)
    blocked = sorted(set(frontier) & candidate.blocked)
    complete = not candidate.missing and all(
        label in candidate.entries for label in ordered
    )
    return complete and bool(frontier) and not blocked, frontier, blocked


def _initial_plan_repair_costs(
    candidate: DesignPlanCandidate,
    node_count: int,
) -> tuple[int, int]:
    """Estimate bounded local correction versus another full tournament.

    The estimate is deliberately expressed in contract-work units rather than
    model-specific seconds or prices. A closure repair may use the base and
    escalation tiers for each blocked contract, each finding adds validation
    work, and each disconnected component is a separate correction
    transaction. A fresh tournament asks two lanes to plan every contract.
    """
    finding_count = sum(len(items) for items in candidate.findings.values())
    repair_work = (
        2 * len(candidate.blocked)
        + finding_count
        + len(candidate.components)
    )
    tournament_work = 2 * max(1, node_count)
    return repair_work, tournament_work


def _initial_plan_repair_admission(
    ctx: Ctx,
    ordered: list[str],
    candidate: DesignPlanCandidate,
) -> tuple[bool, list[str], list[str], int, int]:
    """Admit a complete near-good plan only when scoped repair is cheaper.

    Clean initial frontiers are handled by ``_initial_plan_admission`` and may
    start as soon as either lane finishes. This fallback runs only after both
    lanes have settled, so it cannot preempt a clean sibling. The existing
    frontier closure gateway remains responsible for performing and validating
    the repair before statement generation.
    """
    _clean, frontier, blocked = _initial_plan_admission(ctx, ordered, candidate)
    complete = not candidate.missing and all(
        label in candidate.entries for label in ordered
    )
    repair_work, tournament_work = _initial_plan_repair_costs(
        candidate, len(ordered)
    )
    repairable = (
        complete
        and bool(frontier)
        and bool(blocked)
        and repair_work < tournament_work
    )
    return repairable, frontier, blocked, repair_work, tournament_work


def _merge_design_plan_candidates(
    ctx: Ctx,
    ordered: list[str],
    primary: DesignPlanCandidate,
    alternate: DesignPlanCandidate,
) -> tuple[DesignPlanCandidate, list[list[str]]]:
    """Replace defective closure components only when the full plan improves.

    Arbitrary per-node mixing is unsafe because consumers and providers share
    helper surfaces. Components come from the same closure graph used by plan
    repair, and every proposed replacement is rescored in the complete plan.
    """
    pending = set(ordered)
    generated = {
        label for label, node in ctx.nodes.items() if not node.mathlibok
    }
    frozen = generated - pending
    ready_frontier = set(
        _bottom_up_ready_frontier(ctx.nodes, pending, frozen)
    )

    def ready_count(candidate: DesignPlanCandidate) -> int:
        return len(ready_frontier - candidate.blocked)

    current = primary
    accepted_components: list[list[str]] = []
    attempted: set[tuple[str, ...]] = set()
    while current.findings:
        improved = False
        for component in current.components:
            key = tuple(sorted(component))
            if key in attempted:
                continue
            attempted.add(key)
            if any(label not in alternate.entries for label in component):
                continue
            trial_entries = copy.deepcopy(current.entries)
            for label in component:
                trial_entries[label] = copy.deepcopy(alternate.entries[label])
            trial = _evaluate_design_plan_candidate(
                ctx,
                ordered,
                trial_entries,
                f"merge:{primary.candidate_id}+{alternate.candidate_id}",
            )
            if (
                trial.score < current.score
                and ready_count(trial) >= ready_count(current)
            ):
                current = trial
                accepted_components.append(list(component))
                improved = True
                break
        if not improved:
            break
    return current, accepted_components


def _design_plan_audit_prompt(ctx: Ctx, labels: list[str]) -> str:
    """Ask an independent critic to validate contracts before Lean emission."""
    entries = getattr(ctx, "design_plan_entries", {})
    tex_blocks = getattr(ctx, "tex_blocks", {})
    pairs = []
    for label in labels:
        node = ctx.nodes[label]
        statement_uses = _statement_uses(node)
        proof_only_uses = _proof_uses(node) - statement_uses
        pairs.append(
            f"## Node {label}\n"
            f"- kind: {node.kind}\n"
            f"- expected Lean name: {_lean_name(label)}\n"
            f"- statement-interface dependencies: "
            f"{', '.join(sorted(statement_uses)) or '(none)'}\n"
            f"- proof-only dependencies: "
            f"{', '.join(sorted(proof_only_uses)) or '(none)'}\n"
            f"Blueprint text:\n```tex\n{tex_blocks.get(label, '')[:5000]}\n```\n"
            f"Proposed interface contract:\n```text\n"
            f"{_render_design_plan_entry(label, entries.get(label) or {})[:12000]}\n```"
        )
    nearby_labels = _design_plan_context_labels(ctx, labels)
    nearby_text = "\n".join(
        _render_design_plan_entry(label, entries.get(label) or {})
        for label in _design_plan_order(ctx, nearby_labels)
        if str((entries.get(label) or {}).get("target_signature") or "").strip()
    )[:12000]
    nearby = (
        "Related proposed contracts (also untrusted; use only to check local "
        "consistency):\n```text\n" + nearby_text + "\n```"
        if nearby_text
        else ""
    )
    paper = str(getattr(ctx, "paper_text", ""))
    paper_block = (
        f"Original paper context:\n<paper>\n{paper[:12000]}\n</paper>\n"
        if paper
        else ""
    )
    return f"""TASK: BLUEPRINT-INTERFACE-PLAN-AUDIT

You are an independent critic. The proposed contracts below have NOT been
accepted and no Lean has been generated from them yet. Compare each proposed
interface with its blueprint node.

Reject a contract if it drops an object, parameter, hypothesis, equation,
property, inverse/uniqueness requirement, or other declaration-level
obligation from the blueprint; bundles independent obligations that require
separate declarations; or makes a downstream theorem vacuous. Do not require
exact Lean syntax or proof bodies at this stage: judge the mathematical public
interface. Dependency authorization is checked deterministically before this
call. Do not reject a contract merely because a proof-only dependency is absent
from its public signature, and do not infer additional graph requirements.

Return exactly one JSON object. On success:
{{"accepted": true, "classification": "accepted", "issues": []}}

On failure:
{{
  "accepted": false,
  "classification": "lean_translation_issue" | "blueprint_issue" | "needs_decomposition",
  "issues": [
    {{
      "node": "blueprint label",
      "severity": "reject",
      "reason": "precise mismatch",
      "missing_helpers": ["exact helper obligation, only for decomposition"],
      "missing_blueprint_information": [
        "exact mathematical fact absent from the blueprint"
      ]
    }}
  ]
}}

Use `lean_translation_issue` when the blueprint is coherent but the proposed
interface mistranslates it. Use `blueprint_issue` only when the blueprint claim
itself is mathematically inconsistent or missing a necessary hypothesis. Use
`needs_decomposition` only when the blueprint is concrete but one node bundles
multiple declaration-level obligations that must become explicit blueprint
nodes. A model's difficulty expressing a contract is not a blueprint issue.
For every `blueprint_issue`, `missing_blueprint_information` MUST be nonempty and
name the absent mathematical fact. If another Lean representation could encode
the existing blueprint faithfully, this is a `lean_translation_issue`, not
permission to rewrite the blueprint.

{nearby}

Contracts under review:
{chr(10).join(pairs)}

{paper_block}"""


def _audit_phase1_design_plan(
    ctx: Ctx, labels: Iterable[str]
) -> AlignmentAuditResult | None:
    """Validate uncached plan entries before they can guide Lean generation."""
    entries = getattr(ctx, "design_plan_entries", {})
    ordered = [
        label
        for label in _design_plan_order(ctx, labels)
        if label in entries
        and not _uses_blueprint_direct_generation(ctx, label)
        and str(entries[label].get("audit_fp") or "")
        != _design_plan_audit_fingerprint(ctx, label)
    ]
    if not ordered:
        return None

    cached_rejected = [
        label
        for label in ordered
        if str(entries[label].get("rejected_audit_fp") or "")
        == _design_plan_audit_fingerprint(ctx, label)
    ]
    if cached_rejected:
        kinds_by_label = {
            label: str(entries[label].get("rejected_kind") or "lean-generation")
            for label in cached_rejected
        }
        kinds = set(kinds_by_label.values())
        kind = next(iter(kinds)) if len(kinds) == 1 else "mixed"
        reasons_by_label = {
            label: str(entries[label].get("rejected_reason") or "").strip()
            for label in cached_rejected
            if str(entries[label].get("rejected_reason") or "").strip()
        }
        helpers_by_label = {
            label: list(
                dict.fromkeys(
                    str(item)
                    for item in entries[label].get("rejected_helpers") or []
                )
            )
            for label in cached_rejected
        }
        reasons = list(dict.fromkeys(reasons_by_label.values()))
        helpers = list(
            dict.fromkeys(
                item
                for label in cached_rejected
                for item in helpers_by_label.get(label, [])
            )
        )
        cached_reason = "\n".join(reasons) or "Interface-plan audit previously rejected"
        if reasons and all(
            not item.startswith("Interface-plan ") for item in reasons
        ):
            cached_reason = "Interface-plan audit rejected:\n- " + "\n- ".join(
                reasons
            )
        _log(
            "  reusing unchanged interface-plan rejection for: "
            + ", ".join(cached_rejected)
        )
        _record(
            ctx.telemetry,
            "phase1_design_plan_rejection_reused",
            labels=cached_rejected,
            classification=kind,
            contract_fingerprints={
                label: _design_plan_audit_fingerprint(ctx, label)
                for label in cached_rejected
            },
        )
        return AlignmentAuditResult(
            kind,
            cached_reason,
            set(cached_rejected),
            helpers,
            kinds_by_label=kinds_by_label,
            helpers_by_label=helpers_by_label,
            reasons_by_label=reasons_by_label,
        )

    deterministic = _design_plan_dependency_findings(ctx, ordered)
    if deterministic:
        rejected = {
            label
            for label in ordered
            if any(item.startswith(f"{label}:") for item in deterministic)
        }
        reason = "Interface-plan deterministic checks rejected:\n- " + "\n- ".join(
            deterministic
        )
        for label in rejected:
            entries[label]["rejected_audit_fp"] = _design_plan_audit_fingerprint(
                ctx, label
            )
            entries[label]["rejected_kind"] = "lean-generation"
            entries[label]["rejected_reason"] = reason
            entries[label]["rejected_helpers"] = []
        _record(
            ctx.telemetry,
            "phase1_design_plan_audit",
            labels=sorted(rejected),
            accepted=False,
            classification="deterministic_dependency_rejection",
            findings=deterministic,
        )
        return AlignmentAuditResult(
            "lean-generation",
            reason,
            rejected,
            [],
            kinds_by_label={label: "lean-generation" for label in rejected},
            reasons_by_label={label: reason for label in rejected},
        )
    _log(
        f"==> {_contract_work_stage(ctx)} contract-plan audit: checking {len(ordered)} proposed "
        "interface(s) before Lean generation"
    )
    result = _call_model(
        ctx,
        _design_plan_audit_prompt(ctx, ordered),
        purpose="phase1_design_plan_audit",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=ordered,
    )
    if result.status != "ok" and len(ordered) == 1:
        result = _call_model(
            ctx,
            _design_plan_audit_prompt(ctx, ordered),
            purpose="phase1_design_plan_audit",
            timeout=ctx.hard_timeout,
            effort=ctx.escalation_effort,
            labels=ordered,
            escalated=True,
        )
    if result.status != "ok":
        return AlignmentAuditResult(
            "lean-generation",
            f"interface-plan audit call failed: {result.error}",
            set(ordered),
            [],
            kinds_by_label={label: "lean-generation" for label in ordered},
        )
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        return AlignmentAuditResult(
            "lean-generation",
            f"interface-plan audit returned invalid JSON: {exc}",
            set(ordered),
            [],
            kinds_by_label={label: "lean-generation" for label in ordered},
        )
    issues = payload.get("issues") or []
    accepted = bool(payload.get("accepted")) and not any(
        isinstance(issue, dict)
        and str(issue.get("severity", "reject")).lower() == "reject"
        for issue in issues
    )
    _record(
        ctx.telemetry,
        "phase1_design_plan_audit",
        labels=ordered,
        accepted=accepted,
        classification=str(payload.get("classification") or ""),
    )
    if accepted:
        for label in ordered:
            entries[label]["audit_fp"] = _design_plan_audit_fingerprint(ctx, label)
            for key in (
                "rejected_audit_fp",
                "rejected_kind",
                "rejected_reason",
                "rejected_helpers",
                "correction_base_fp",
                "correction_escalation_fp",
            ):
                entries[label].pop(key, None)
        _sync_design_plan(ctx)
        return None

    rejected: set[str] = set()
    formatted: list[str] = []
    kinds_by_label: dict[str, str] = {}
    helpers_by_label: dict[str, list[str]] = {}
    reasons_by_label: dict[str, str] = {}
    missing_info_by_label: dict[str, list[str]] = {}
    global_classification = str(payload.get("classification") or "")
    for issue in issues if isinstance(issues, list) else []:
        if not isinstance(issue, dict):
            continue
        node = str(issue.get("node") or "(unknown)")
        severity = str(issue.get("severity") or "reject")
        issue_line = f"{node} [{severity}]: {issue.get('reason', '')}"
        formatted.append(issue_line)
        if severity.lower() == "reject" and node in ordered:
            rejected.add(node)
            issue_classification = str(
                issue.get("classification") or global_classification
            )
            if issue_classification == "needs_decomposition":
                issue_kind = "decomposition"
                missing_information: list[str] = []
            else:
                issue_kind, missing_information = _authorized_alignment_failure_kind(
                    issue_classification, [issue_line], [issue]
                )
            kinds_by_label[node] = issue_kind
            reasons_by_label[node] = issue_line
            missing_info_by_label[node] = missing_information
            helpers_by_label[node] = list(
                dict.fromkeys(
                    str(item).strip()
                    for item in issue.get("missing_helpers") or []
                    if str(item).strip()
                )
            )
    if not rejected:
        rejected = set(ordered)
        for label in rejected:
            kinds_by_label[label] = "lean-generation"
            reasons_by_label[label] = (
                "The interface-plan critic rejected without attributable "
                "per-node routing evidence."
            )
    for label in set(ordered) - rejected:
        entries[label]["audit_fp"] = _design_plan_audit_fingerprint(ctx, label)
    routed_kinds = set(kinds_by_label.values())
    kind = next(iter(routed_kinds)) if len(routed_kinds) == 1 else "mixed"
    missing_blueprint_information = list(
        dict.fromkeys(
            item
            for label in sorted(rejected)
            for item in missing_info_by_label.get(label, [])
        )
    )
    helpers = list(
        dict.fromkeys(
            helper
            for label in sorted(rejected)
            for helper in helpers_by_label.get(label, [])
        )
    )
    _record(
        ctx.telemetry,
        "phase1_design_plan_audit_routing",
        labels=sorted(rejected),
        reported_classification=global_classification,
        routed_kind=kind,
        routed_kinds={
            label: kinds_by_label.get(label, "lean-generation")
            for label in sorted(rejected)
        },
        blueprint_repair_authorized=any(
            routed in {"blueprint", "decomposition"}
            for routed in kinds_by_label.values()
        ),
        missing_blueprint_information=missing_blueprint_information,
    )
    reason = "Interface-plan audit rejected:\n- " + "\n- ".join(
        formatted or ["critic rejected the proposed interface without node details"]
    )
    if kind == "lean-generation" and global_classification == "blueprint_issue":
        reason += (
            "\nBlueprint repair was not authorized because the audit named no "
            "mathematical information absent from the blueprint."
        )
    for label in rejected:
        entries[label]["rejected_audit_fp"] = _design_plan_audit_fingerprint(ctx, label)
        entries[label]["rejected_kind"] = kinds_by_label.get(
            label, "lean-generation"
        )
        entries[label]["rejected_reason"] = reasons_by_label.get(label, reason)
        entries[label]["rejected_helpers"] = helpers_by_label.get(label, [])
    return AlignmentAuditResult(
        kind,
        reason,
        rejected,
        helpers,
        kinds_by_label=kinds_by_label,
        helpers_by_label=helpers_by_label,
        reasons_by_label=reasons_by_label,
    )


def _try_alternate_design_plan_component(
    ctx: Ctx, labels: list[str], evidence: str
) -> bool:
    """Try the retained candidate once before paying for plan correction."""
    entries = getattr(ctx, "design_plan_entries", {})
    alternates = getattr(ctx, "design_plan_alternates", {})
    if not labels or any(label not in alternates for label in labels):
        return False
    ordered = _design_plan_order(ctx, entries)
    current = _evaluate_design_plan_candidate(ctx, ordered, entries, "selected")
    trial_entries = copy.deepcopy(entries)
    changed = False
    for label in labels:
        replacement = _preserve_plan_entry_progress(
            entries.get(label), copy.deepcopy(alternates[label])
        )
        changed = changed or replacement != trial_entries.get(label)
        trial_entries[label] = replacement
    for label in labels:
        alternates.pop(label, None)
    if not changed:
        return False

    trial = _evaluate_design_plan_candidate(ctx, ordered, trial_entries, "alternate")
    acceptable = trial.score < current.score or (current.closed and trial.closed)
    _record(
        ctx.telemetry,
        "phase1_design_plan_alternate_component",
        labels=labels,
        status="applied" if acceptable else "rejected",
        previous_score=list(current.score),
        alternate_score=list(trial.score),
        evidence_sha256=hashlib.sha256(evidence.encode("utf-8")).hexdigest(),
    )
    if not acceptable:
        return False
    for label in labels:
        entries[label] = trial_entries[label]
    _transition_phase1_generation_epoch(
        ctx,
        labels,
        reason="retained_alternate_plan_applied",
    )
    _log(
        "  reused retained alternate plan component before model correction: "
        + ", ".join(labels)
    )
    return True


def _correct_phase1_design_plan(
    ctx: Ctx,
    labels: list[str],
    evidence: str,
    *,
    evidence_identities_by_label: Mapping[str, Mapping[str, Any]] | None = None,
    escalated: bool = False,
    try_alternate: bool = True,
    context_labels: Iterable[str] | None = None,
    transition_generation_epoch: bool = True,
) -> bool:
    """Revise one connected set of interface contracts using exact evidence."""
    if try_alternate and _try_alternate_design_plan_component(ctx, labels, evidence):
        return True
    entries = getattr(ctx, "design_plan_entries", {})
    context_only = [
        label
        for label in dict.fromkeys(context_labels or [])
        if label not in labels and label in entries
    ]
    fingerprint = hashlib.sha256(
        json.dumps(
            {
                "targets": {
                    label: _design_plan_audit_fingerprint(ctx, label)
                    for label in sorted(labels)
                },
                "context": {
                    label: _design_plan_audit_fingerprint(ctx, label)
                    for label in sorted(context_only)
                },
                "evidence": {
                    label: _diagnostic_failure_signature(
                        kind="semantic",
                        text=evidence,
                        identity=(
                            evidence_identities_by_label.get(label)
                            if evidence_identities_by_label is not None
                            else None
                        ),
                    )
                    for label in sorted(labels)
                },
            },
            sort_keys=True,
        ).encode("utf-8")
    ).hexdigest()
    attempt_key = "correction_escalation_fp" if escalated else "correction_base_fp"
    if labels and all(
        str((entries.get(label) or {}).get(attempt_key) or "") == fingerprint
        for label in labels
    ):
        _log(
            "  skipping unchanged interface-plan correction already attempted at "
            + ("escalation" if escalated else "base")
            + " tier"
        )
        _record(
            ctx.telemetry,
            "phase1_design_plan_correction",
            labels=labels,
            status="reused_unchanged_failure",
            tier="escalation" if escalated else "base",
            contract_fingerprint=fingerprint,
        )
        return False
    _log(
        f"==> {_contract_work_stage(ctx)} contract-plan correction "
        f"({'escalation' if escalated else 'base'}): "
        + ", ".join(labels[:8])
        + ("..." if len(labels) > 8 else "")
    )
    for label in labels:
        if label in entries:
            entries[label][attempt_key] = fingerprint
    tex_blocks = getattr(ctx, "tex_blocks", {})
    targets = "\n\n".join(
        f"## {label}\nBlueprint:\n```tex\n{tex_blocks.get(label, '')[:5000]}\n```\n"
        f"Current contract:\n{_render_design_plan_entry(label, entries.get(label) or {})}"
        for label in labels
    )
    context = "\n\n".join(
        f"## READ-ONLY CONTEXT {label}\n"
        f"{_render_design_plan_entry(label, entries.get(label) or {})}"
        for label in context_only
    )
    prompt = f"""TASK: CORRECT-BLUEPRINT-INTERFACE-PLAN

Correct only the connected interface contracts below. Some requested labels
may be provider contracts included because another requested contract refers
to a missing member on their public surface. Make the complete requested set
mutually consistent rather than merely renaming the consumer's missing member.
The blueprint is the source of truth. Preserve every object, parameter,
hypothesis, equation, and declaration-level property identified by the critic.
Do not edit the blueprint and do not emit Lean bodies or proofs.

Return exactly one JSON object using the same lossless schema as planning:
{{
  "contracts": [
    {{
      "label": "requested blueprint label",
      "target_signature": "complete Lean-ish target signature",
      "helpers": [
        {{"name": "stable helper name", "kind": "structure|inductive|class", "members": [{{"name": "stable_field_or_constructor", "type": "complete Lean-ish member type"}}], "purpose": "brief type-interface role"}}
      ],
      "decisions": ["semantic/interface decision generation must preserve"]
    }}
  ]
}}
Include every requested label and no others. Helpers may only be auxiliary
`structure`, `inductive`, or `class` interfaces needed to state the target.
Every helper member must include its complete Lean-ish type. A list of member
names without types is invalid because statement generation must not invent the
helper interface.
Never introduce a helper `def`, `abbrev`, `theorem`, or `lemma`: equations and
properties belong to the target contract/decisions and are implemented in
Phase 2. Each `target_signature` must contain exactly one top-level declaration,
whose name is the requested node's required Lean name. When one blueprint node
describes several operations, place those operations and their defining laws in
one plan-owned `structure` or `class` helper and make the single canonical
target return that interface. Preserve required type-interface helpers and
decisions; do not emit Lean bodies or proofs.

Contracts under READ-ONLY CONTEXT are supplied only so the requested contracts
can use their already-decided public surfaces consistently. Do not return or
rewrite those context contracts.

Critic evidence:
{evidence}

{targets}

{context}
"""
    result = _call_model(
        ctx,
        prompt,
        purpose="phase1_design_plan_correction",
        timeout=ctx.hard_timeout if escalated else ctx.base_timeout,
        effort=ctx.escalation_effort if escalated else ctx.base_effort,
        labels=labels,
        escalated=escalated,
    )
    if result.status != "ok" or not result.text.strip():
        return False
    corrected = _parse_design_plan_entries(ctx, labels, result.text)
    if set(corrected) != set(labels):
        return False
    old_fingerprints = {
        label: _design_plan_audit_fingerprint(ctx, label) for label in labels
    }
    old_rejection_metadata = {
        label: {
            key: entries[label].get(key)
            for key in (
                "rejected_audit_fp",
                "rejected_kind",
                "rejected_reason",
                "rejected_helpers",
                "correction_base_fp",
                "correction_escalation_fp",
            )
            if key in entries[label]
        }
        for label in labels
    }
    for label, entry in corrected.items():
        entry.pop("audit_fp", None)
        entries[label] = _preserve_plan_entry_progress(entries.get(label), entry)
    if all(
        _design_plan_audit_fingerprint(ctx, label) == old_fingerprints[label]
        for label in labels
    ):
        for label in labels:
            entries[label].update(old_rejection_metadata[label])
            entries[label][attempt_key] = fingerprint
        _record(
            ctx.telemetry,
            "phase1_design_plan_correction",
            labels=labels,
            status="unchanged",
            tier="escalation" if escalated else "base",
        )
        return False
    if transition_generation_epoch:
        _transition_phase1_generation_epoch(
            ctx,
            labels,
            reason="interface_plan_correction_applied",
        )
    else:
        _sync_design_plan(ctx)
    _record(
        ctx.telemetry,
        "phase1_design_plan_correction",
        labels=labels,
        status="applied",
        tier="escalation" if escalated else "base",
    )
    return True


def _phase1_frontier_plan_gateway(
    ctx: Ctx,
    labels: Iterable[str],
    plan_order: list[str],
    closure_findings: dict[str, list[str]],
) -> dict[str, list[str]]:
    """Admit one dependency-ready plan slice to statement generation.

    The full plan is deliberately lightweight and untrusted.  Mechanical
    closure is computed globally, but paid semantic checking happens just in
    time for the next graph frontier.  A rejected contract is corrected with
    its direct provider/consumer slice as read-only context; unrelated plan
    entries are never rewritten.  The accepted audit fingerprint is persisted
    on each entry, so an unchanged frontier pays this gate only once.
    """
    ordered = [
        label
        for label in _design_plan_order(ctx, labels)
        if label in getattr(ctx, "design_plan_entries", {})
        and (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            != "phase1_candidate"
        )
        and not _uses_blueprint_direct_generation(ctx, label)
        and int(
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "schema_version"
            )
            or 0
        )
        == DESIGN_PLAN_SCHEMA_VERSION
    ]
    if not ordered:
        return closure_findings
    context_labels = sorted(
        _design_plan_context_labels(ctx, ordered) - set(ordered)
    )

    def invalidate_exhausted_entries(
        exhausted: Iterable[str], *, reason: str
    ) -> None:
        """Force fresh bounded planning after this contract cannot improve."""
        invalidated = [
            label
            for label in dict.fromkeys(exhausted)
            if label in getattr(ctx, "design_plan_entries", {})
        ]
        if not invalidated:
            return
        entries = ctx.design_plan_entries
        alternates = getattr(ctx, "design_plan_alternates", {})
        for label in invalidated:
            entries.pop(label, None)
            alternates.pop(label, None)
        _transition_phase1_generation_epoch(
            ctx,
            invalidated,
            reason=reason,
        )
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_invalidated",
            labels=invalidated,
            reason=reason,
            next_action="fresh_scoped_planning",
        )
    _record(
        ctx.telemetry,
        "phase1_frontier_plan_gateway",
        labels=ordered,
        context_labels=context_labels,
        status="started",
        contract_fingerprints={
            label: _design_plan_audit_fingerprint(ctx, label)
            for label in ordered
        },
    )

    def correct_direct_closure(
        current: dict[str, list[str]],
    ) -> dict[str, list[str]]:
        """Close defects owned by this frontier without editing future nodes."""
        direct = {
            label: list(current[label])
            for label in ordered
            if label in current
        }
        if not direct:
            return current
        affected = [label for label in ordered if label in direct]
        evidence = (
            "Phase 1 frontier contracts fail deterministic plan closure:\n- "
            + "\n- ".join(
                finding
                for label in affected
                for finding in direct[label]
            )
        )
        corrected = _correct_phase1_design_plan(
            ctx,
            affected,
            evidence,
            escalated=False,
            context_labels=context_labels,
        )
        correction_tier = "base"
        if not corrected:
            corrected = _correct_phase1_design_plan(
                ctx,
                affected,
                evidence,
                escalated=True,
                context_labels=context_labels,
            )
            correction_tier = "escalation"
        if corrected:
            current = _validate_design_plan_contract_closure(ctx, plan_order)
        remaining = {
            label: list(current[label])
            for label in affected
            if label in current
        }
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_closure",
            labels=affected,
            context_labels=context_labels,
            status="accepted" if corrected and not remaining else "rejected",
            correction_tier=correction_tier,
            findings=remaining,
        )
        if corrected and not remaining:
            return current
        invalidate_exhausted_entries(
            affected, reason="frontier_contract_closure_correction_exhausted"
        )
        route = _route_lean_generation_failure(affected)
        raise RepairRequest(
            evidence,
            list(route.failed_labels),
            section_labels=affected,
            context_labels=context_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            plan_revision_required=True,
        )

    # Global closure findings remain useful for future scheduling, but a
    # consumer that is not dependency-ready cannot block or rewrite today's
    # provider. Only defects whose consumer is in this frontier are repaired
    # here; direct providers/consumers are immutable correction context.
    closure_findings = correct_direct_closure(closure_findings)

    audit = _audit_phase1_design_plan(ctx, ordered)
    if audit is None:
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_gateway",
            labels=ordered,
            context_labels=context_labels,
            status="accepted",
            corrected_labels=[],
        )
        return closure_findings

    audit = _coerce_alignment_audit_result(audit)
    kind, reason, rejected, helpers = audit
    rejected_ordered = [label for label in ordered if label in rejected]
    if not rejected_ordered:
        rejected_ordered = list(ordered)

    blueprint_rejected = audit.labels_for("blueprint")
    decomposition_rejected = audit.labels_for("decomposition")
    repair_rejected = blueprint_rejected | decomposition_rejected
    if repair_rejected:
        repair_ordered = [
            label for label in rejected_ordered if label in repair_rejected
        ]
        deferred_plan_labels = [
            label for label in rejected_ordered if label not in repair_rejected
        ]
        repair_kind = "decomposition" if decomposition_rejected else "blueprint"
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_audit_routed",
            labels=rejected_ordered,
            blueprint_repair_labels=repair_ordered,
            deferred_plan_correction_labels=deferred_plan_labels,
            routed_kinds={
                label: audit.kinds_by_label.get(label, "lean-generation")
                for label in rejected_ordered
            },
        )
        raise RepairRequest(
            audit.reason_for(repair_ordered),
            repair_ordered,
            decomposition_helpers=(
                audit.helpers_for(decomposition_rejected)
                if repair_kind == "decomposition"
                else []
            ),
            section_labels=repair_ordered,
            context_labels=context_labels,
            authorizes_blueprint_repair=True,
            model_repair_labels=repair_ordered,
        )

    # An unavailable critic supplies no evidence that the plan is wrong. Route
    # it as infrastructure/generation retry rather than spending a correction
    # call on an arbitrary plan edit.
    if reason.startswith("interface-plan audit call failed:") or reason.startswith(
        "interface-plan audit returned invalid JSON:"
    ):
        route = _route_lean_generation_failure(rejected_ordered)
        raise RepairRequest(
            reason,
            list(route.failed_labels),
            section_labels=rejected_ordered,
            context_labels=context_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
        )

    corrected = _correct_phase1_design_plan(
        ctx,
        rejected_ordered,
        reason,
        escalated=False,
        context_labels=context_labels,
    )
    correction_tier = "base"
    if not corrected:
        corrected = _correct_phase1_design_plan(
            ctx,
            rejected_ordered,
            reason,
            escalated=True,
            context_labels=context_labels,
        )
        correction_tier = "escalation"
    if not corrected:
        route = _route_lean_generation_failure(rejected_ordered)
        invalidate_exhausted_entries(
            rejected_ordered, reason="frontier_semantic_correction_exhausted"
        )
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_gateway",
            labels=ordered,
            context_labels=context_labels,
            status="correction_exhausted",
            rejected_labels=rejected_ordered,
        )
        raise RepairRequest(
            reason,
            list(route.failed_labels),
            section_labels=rejected_ordered,
            context_labels=context_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            plan_revision_required=True,
        )

    # A semantic correction can introduce a mechanically invalid target
    # contract. Re-run closure globally for observability, but repair only the
    # changed frontier; future consumers remain queued for their own gateway.
    closure_findings = _validate_design_plan_contract_closure(ctx, plan_order)
    closure_findings = correct_direct_closure(closure_findings)

    repeated = _audit_phase1_design_plan(ctx, rejected_ordered)
    if repeated is not None:
        repeated = _coerce_alignment_audit_result(repeated)
        repeated_kind, repeated_reason, repeated_rejected, repeated_helpers = repeated
        retry_labels = [
            label for label in rejected_ordered if label in repeated_rejected
        ] or rejected_ordered
        repeated_blueprint = repeated.labels_for("blueprint")
        repeated_decomposition = repeated.labels_for("decomposition")
        repeated_repair = repeated_blueprint | repeated_decomposition
        if repeated_repair:
            repair_labels = [
                label for label in retry_labels if label in repeated_repair
            ]
            repair_kind = (
                "decomposition" if repeated_decomposition else "blueprint"
            )
            raise RepairRequest(
                repeated.reason_for(repair_labels),
                repair_labels,
                decomposition_helpers=(
                    repeated.helpers_for(repeated_decomposition)
                    if repair_kind == "decomposition"
                    else []
                ),
                section_labels=repair_labels,
                context_labels=context_labels,
                authorizes_blueprint_repair=True,
                model_repair_labels=repair_labels,
            )
        route = _route_lean_generation_failure(retry_labels)
        invalidate_exhausted_entries(
            retry_labels, reason="frontier_semantic_reaudit_rejected"
        )
        _record(
            ctx.telemetry,
            "phase1_frontier_plan_gateway",
            labels=ordered,
            context_labels=context_labels,
            status="still_rejected",
            rejected_labels=retry_labels,
            correction_tier=correction_tier,
        )
        raise RepairRequest(
            repeated_reason,
            list(route.failed_labels),
            section_labels=retry_labels,
            context_labels=context_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            plan_revision_required=True,
        )

    _record(
        ctx.telemetry,
        "phase1_frontier_plan_gateway",
        labels=ordered,
        context_labels=context_labels,
        status="accepted_after_correction",
        corrected_labels=rejected_ordered,
        correction_tier=correction_tier,
        remaining_global_closure_labels=sorted(closure_findings),
    )
    return closure_findings


def _closure_component_evidence(
    ctx: Ctx,
    component: list[str],
    findings: dict[str, list[str]],
    *,
    after_alternate: bool = False,
) -> tuple[str, list[str], list[str]]:
    """Render complete evidence for one connected closure component."""
    consumers = [label for label in component if label in findings]
    providers = sorted(
        {
            issue.provider
            for issue in _design_plan_contract_closure_issues(ctx, consumers)
            if issue.provider is not None and issue.provider in ctx.nodes
        }
    )
    prefix = (
        "Phase 1 interface-plan contract closure still rejected after trying "
        "the retained alternate candidate:\n- "
        if after_alternate
        else "Phase 1 interface-plan contract closure rejected:\n- "
    )
    evidence = prefix + "\n- ".join(
        finding for label in consumers for finding in findings[label]
    )
    editable_providers = [provider for provider in providers if provider in component]
    read_only_providers = [
        provider for provider in providers if provider not in component
    ]
    if editable_providers:
        evidence += (
            "\nProvider contract(s) with missing public members: "
            + ", ".join(editable_providers)
            + ". Correct provider and consumer surfaces together."
        )
    if read_only_providers:
        evidence += (
            "\nExisting dependency provider contract(s), supplied as read-only "
            "context: " + ", ".join(read_only_providers)
            + ". Correct the consumer; do not redesign these providers."
        )
    return evidence, consumers, providers


def _closure_component_score(
    ctx: Ctx,
    component: Iterable[str],
    findings: dict[str, list[str]],
) -> tuple[int, int, int]:
    """Monotonic score for one isolated closure-correction transaction."""
    scoped = _closure_findings_for_scope(ctx, findings, component)
    blocked = _closure_blocked_labels(ctx, scoped) if scoped else set()
    return (
        sum(len(messages) for messages in scoped.values()),
        len(blocked),
        len(scoped),
    )


def _closure_correction_stage(
    ctx: Ctx,
    component: list[str],
    findings: dict[str, list[str]],
) -> tuple[list[str], dict[str, list[str]]]:
    """Return the next provider-aware edit set and its exact evidence.

    Missing-member defects are handled first with the provider and only the
    consumers that impose requirements on its surface. Once provider surfaces
    are coherent, remaining authorization/alias/cycle defects edit consumers
    only.
    """
    member_findings: dict[str, list[str]] = {}
    member_targets: set[str] = set()
    for issue in _design_plan_contract_closure_issues(ctx, findings):
        if (
            issue.consumer in findings
            and issue.provider in component
            and issue.missing_provider_members
        ):
            member_targets.update((issue.consumer, issue.provider))
            member_findings.setdefault(issue.consumer, []).append(issue.message)
    stage_findings = member_findings or findings
    targets = member_targets or set(stage_findings)
    ordered_targets = [
        label
        for label in _design_plan_order(ctx, component)
        if label in targets
    ]
    return ordered_targets, stage_findings


def _correct_plan_closure_component_from_snapshot(
    ctx: Ctx,
    ordered: list[str],
    snapshot: dict[str, dict[str, Any]],
    component: list[str],
    evidence: str,
) -> PlanClosureCorrectionResult:
    """Make one bounded correction without mutating the live plan.

    Initial-plan closure is on Phase 1's critical path. Retained alternates are
    tried before this function, so one exact-evidence base call is the only paid
    correction permitted here. A strict partial improvement is preserved as an
    alternate, but unresolved contracts return to selective replanning instead
    of paying for serial base/escalation calls before any contract can freeze.
    """
    isolated = copy.copy(ctx)
    isolated.design_plan_entries = copy.deepcopy(snapshot)
    isolated.design_plan_alternates = {}
    isolated.design_plan = ""
    _sync_design_plan(isolated)
    started = time.time()
    initial = _evaluate_design_plan_candidate(
        isolated, ordered, isolated.design_plan_entries, "component-initial"
    )
    initial_findings = _closure_findings_for_scope(
        isolated, initial.findings, component
    )
    initial_score = _closure_component_score(
        isolated, component, initial_findings
    )
    targets, stage_findings = _closure_correction_stage(
        isolated, component, initial_findings
    )
    if not targets:
        finished = time.time()
        return PlanClosureCorrectionResult(
            tuple(component), {}, "not_corrected", initial_findings,
            finished - started, started, finished,
        )

    residual_evidence, _consumers, providers = _closure_component_evidence(
        isolated, component, stage_findings
    )
    corrected = _correct_phase1_design_plan(
        isolated,
        targets,
        residual_evidence,
        escalated=False,
        try_alternate=False,
        context_labels=[*component, *providers],
        transition_generation_epoch=False,
    )
    if corrected:
        candidate = _evaluate_design_plan_candidate(
            isolated,
            ordered,
            isolated.design_plan_entries,
            "component-correction",
        )
        candidate_findings = _closure_findings_for_scope(
            isolated, candidate.findings, component
        )
        candidate_score = _closure_component_score(
            isolated, component, candidate_findings
        )
    else:
        candidate_findings = initial_findings
        candidate_score = initial_score

    improved = corrected and candidate_score < initial_score
    _record(
        ctx.telemetry,
        "phase1_design_plan_closure_attempt",
        labels=targets,
        component_labels=component,
        context_labels=list(
            dict.fromkeys(
                [label for label in component if label not in targets]
                + [provider for provider in providers if provider not in targets]
            )
        ),
        attempt=1,
        tier="base",
        corrected=corrected,
        improved=improved,
        before_score=list(initial_score),
        after_score=list(candidate_score),
        residual_findings=candidate_findings,
    )

    finished = time.time()
    status = (
        "accepted"
        if corrected and not candidate_findings
        else "partially_improved"
        if improved
        else "still_rejected"
    )
    return PlanClosureCorrectionResult(
        tuple(component),
        (
            {
                label: copy.deepcopy(isolated.design_plan_entries[label])
                for label in component
            }
            if status in {"accepted", "partially_improved"}
            else {}
        ),
        status,
        candidate_findings,
        finished - started,
        started,
        finished,
    )


def _repair_phase1_design_plan_closure(
    ctx: Ctx,
    ordered: list[str],
    closure_findings: dict[str, list[str]],
    *,
    repair_scope: Iterable[str] | None = None,
) -> None:
    """Repair disjoint closure components concurrently from one plan snapshot.

    Retained alternates remain the zero-call first choice. The unresolved
    components are disjoint in the provider-consumer graph, so each model call
    sees the same immutable plan and only successful component entries are
    merged. A failed component cannot roll back a successful sibling.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    scope = set(repair_scope or [])
    remaining = (
        _closure_findings_for_scope(ctx, closure_findings, scope)
        if scope
        else closure_findings
    )

    # Alternates cost no model calls. Apply them first, then rescore once so
    # every paid correction starts from the same selected-plan snapshot.
    alternate_by_component: dict[tuple[str, ...], bool] = {}
    for component in _design_plan_closure_repair_components(ctx, remaining):
        evidence, consumers, _providers = _closure_component_evidence(
            ctx, component, remaining
        )
        if not consumers:
            continue
        alternate_by_component[tuple(component)] = (
            _try_alternate_design_plan_component(ctx, component, evidence)
        )
    if any(alternate_by_component.values()):
        validated = _validate_design_plan_contract_closure(ctx, ordered)
        remaining = (
            _closure_findings_for_scope(ctx, validated, scope)
            if scope
            else validated
        )
        if not remaining:
            return

    components = _design_plan_closure_repair_components(ctx, remaining)
    snapshot = copy.deepcopy(entries)
    pre_merge = _evaluate_design_plan_candidate(
        ctx, ordered, snapshot, "closure-wave-before"
    )
    wave_started = time.time()
    wave_id = hashlib.sha256(
        (
            str(time.time_ns())
            + json.dumps(
                {
                    label: _design_plan_audit_fingerprint(ctx, label)
                    for label in ordered
                    if label in entries
                },
                sort_keys=True,
            )
        ).encode("utf-8")
    ).hexdigest()[:16]
    work: list[tuple[list[str], str, list[str], list[str]]] = []
    for component in components:
        evidence, consumers, providers = _closure_component_evidence(
            ctx,
            component,
            remaining,
            after_alternate=alternate_by_component.get(tuple(component), False),
        )
        if consumers:
            work.append((component, evidence, consumers, providers))

    results: dict[tuple[str, ...], PlanClosureCorrectionResult] = {}
    worker_count = min(max(1, int(getattr(ctx, "workers", 1))), len(work))
    if work:
        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
            futures = {
                pool.submit(
                    _correct_plan_closure_component_from_snapshot,
                    ctx,
                    ordered,
                    snapshot,
                    component,
                    evidence,
                ): (component, consumers, providers)
                for component, evidence, consumers, providers in work
            }
            for future in concurrent.futures.as_completed(futures):
                component, consumers, providers = futures[future]
                result = future.result()
                results[tuple(component)] = result
                _record(
                    ctx.telemetry,
                    "phase1_outline_plan_closure_correction",
                    labels=component,
                    rejected_labels=consumers,
                    provider_labels=providers,
                    alternate_applied=alternate_by_component.get(
                        tuple(component), False
                    ),
                    corrected=result.status == "accepted",
                    correction_status=result.status,
                    reason="deterministic_contract_closure",
                    tier="base",
                    wave_id=wave_id,
                    wave_started_at_s=wave_started,
                    correction_started_at_s=result.started_at_s,
                    correction_finished_at_s=result.finished_at_s,
                    duration_s=result.duration_s,
                    pre_merge_score=list(pre_merge.score),
                    statement_fingerprints={
                        label: ctx.stmt_fps.get(label, "")
                        for label in component
                    },
                    plan_fingerprints={
                        label: _design_plan_audit_fingerprint(ctx, label)
                        for label in component
                    },
                    component_findings=result.findings,
                )

    merged_entries = copy.deepcopy(snapshot)
    merged_labels: set[str] = set()
    for component, _evidence, _consumers, _providers in work:
        result = results.get(tuple(component))
        if result is None or not result.entries:
            continue
        overlap = merged_labels & set(component)
        if overlap:
            raise RuntimeError(
                "closure correction components overlapped unexpectedly: "
                + ", ".join(sorted(overlap))
            )
        for label, entry in result.entries.items():
            merged_entries[label] = copy.deepcopy(entry)
            merged_entries[label]["closure_wave_id"] = wave_id
        merged_labels.update(result.entries)
    ctx.design_plan_entries = merged_entries
    entries = ctx.design_plan_entries
    if merged_labels:
        _transition_phase1_generation_epoch(
            ctx,
            merged_labels,
            reason="contract_closure_wave_merged",
        )
    else:
        _sync_design_plan(ctx)
    validated = _validate_design_plan_contract_closure(ctx, ordered)
    remaining = (
        _closure_findings_for_scope(ctx, validated, scope)
        if scope
        else validated
    )
    post_merge = _evaluate_design_plan_candidate(
        ctx, ordered, entries, "closure-wave-after"
    )
    _record(
        ctx.telemetry,
        "phase1_design_plan_closure_wave",
        labels=[label for component in components for label in component],
        wave_id=wave_id,
        started_at_s=wave_started,
        finished_at_s=time.time(),
        worker_count=worker_count if work else 0,
        component_count=len(work),
        merged_labels=sorted(merged_labels),
        failed_components=[
            list(component)
            for component, _evidence, _consumers, _providers in work
            if results.get(tuple(component)) is None
            or results[tuple(component)].status != "accepted"
        ],
        pre_merge_score=list(pre_merge.score),
        post_merge_score=list(post_merge.score),
    )
    if not remaining:
        return

    failed_components = _design_plan_closure_repair_components(ctx, remaining)
    failed = list(
        dict.fromkeys(label for component in failed_components for label in component)
    )
    alternates = getattr(ctx, "design_plan_alternates", None)
    if alternates is None:
        alternates = {}
        ctx.design_plan_alternates = alternates
    for label in failed:
        # A monotonically improved but not-yet-closed candidate remains a
        # retained alternate. Fresh planning may beat it, but it is no longer
        # silently lost merely because a sibling finding survived the wave.
        if label in entries and label in merged_labels:
            alternates[label] = copy.deepcopy(entries[label])
        entries.pop(label, None)
    _transition_phase1_generation_epoch(
        ctx,
        failed,
        reason="contract_closure_correction_exhausted",
    )
    _record(
        ctx.telemetry,
        "phase1_design_plan_invalidated",
        labels=failed,
        rejected_labels=sorted(remaining),
        reason="contract_closure_correction_exhausted",
    )
    route = _route_lean_generation_failure(failed)
    raise RepairRequest(
        "Phase 1 cannot generate Lean from a mechanically impossible "
        "interface plan. The retained alternate and one bounded correction "
        "did not close these connected provider-consumer contracts; their "
        "plan entries were discarded for fresh planning on the next bounded "
        "retry:\n- "
        + "\n- ".join(
            finding
            for label in sorted(remaining)
            for finding in remaining[label]
        ),
        list(route.failed_labels),
        section_labels=failed,
        authorizes_blueprint_repair=False,
        failure_route=route,
        plan_revision_required=True,
    )


def _design_plan_context_labels(ctx: Ctx, labels: Iterable[str]) -> set[str]:
    """Small complete plan slice: targets plus direct providers/consumers."""
    targets = {label for label in labels if label in ctx.nodes}
    relevant = set(targets)
    for label in targets:
        relevant.update(dep for dep in ctx.nodes[label].uses if dep in ctx.nodes)
    relevant.update(
        label
        for label, node in ctx.nodes.items()
        if set(node.uses) & targets
    )
    return relevant


def _design_plan_block(
    ctx: Ctx, labels: Iterable[str] | None = None, *, budget: int = 9000
) -> str:
    """Render the best available guidance independently for each node.

    Candidate-derived typed contracts take precedence for their own node. A
    newly introduced helper usually has only a compact semantic-plan entry,
    however, so the presence of typed contracts for older neighboring nodes
    must not hide that helper's guidance.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    semantic_entries = getattr(ctx, "semantic_plan_entries", {})
    available = set(entries) | set(semantic_entries)
    target_labels = set(labels or [])
    selected = (
        available
        if labels is None
        else _design_plan_context_labels(ctx, target_labels) & available
    )
    ordered = _design_plan_order(ctx, selected)
    if labels is not None:
        # The target's advisory entry is what prevents a new helper from being
        # invented under an underspecified contract. Dependency interfaces are
        # also supplied separately, so place targets first under the hard
        # prompt-size budget.
        ordered = (
            [label for label in ordered if label in target_labels]
            + [label for label in ordered if label not in target_labels]
        )
    rendered: list[str] = []
    used_typed = False
    used_semantic = False
    for label in ordered:
        if _uses_blueprint_direct_generation(ctx, label):
            continue
        entry = entries.get(label) or {}
        if str(entry.get("target_signature") or "").strip():
            rendered.append(_render_design_plan_entry(label, entry))
            used_typed = True
        elif label in semantic_entries:
            rendered.append(
                _render_semantic_plan_entry(label, semantic_entries[label])
            )
            used_semantic = True
    plan = "\n".join(rendered)
    if not plan:
        plan = getattr(ctx, "design_plan", "")
    direct_labels = sorted(
        label
        for label in target_labels
        if _uses_blueprint_direct_generation(ctx, label)
    )
    blocks: list[str] = []
    if plan:
        if used_typed and used_semantic:
            plan_kind = (
                "Per-node Phase-1 guidance (TARGET entries are exact typed "
                "contracts; REPRESENTATION entries are compact advisory "
                "guidance; the blueprint is authoritative)"
            )
        elif used_typed:
            plan_kind = "Exact typed contracts already realized by Phase-1 candidates"
        else:
            plan_kind = "Compact semantic guidance (advisory; blueprint is authoritative)"
        blocks.append(
            plan_kind
            + " (use only when consistent with the blueprint and frozen Lean):\n```text\n"
            + plan[:budget]
            + "\n```\n"
        )
    if direct_labels:
        direct = getattr(ctx, "blueprint_direct_generation", {})
        evidence = "\n\n".join(
            f"{label}:\n{str((direct.get(label) or {}).get('evidence') or '')[-4000:]}"
            for label in direct_labels
        )
        blocks.append(
            "PLAN CIRCUIT BREAKER ACTIVE for: "
            + ", ".join(direct_labels)
            + ". The saved interface plan for these targets is known to be "
            "unusable. Generate their exact public statements directly from "
            "the blueprint, frozen dependency interfaces, and the rejection "
            "evidence below. Do not preserve or repair the rejected plan.\n"
            "```text\n"
            + evidence[-12000:]
            + "\n```\n"
        )
    return "\n".join(blocks)


def _compact_dependency_contract_table(ctx: Ctx, labels: Iterable[str]) -> str:
    """Lossless graph authority for planning without per-edge prose.

    The verbose compiler-facing table repeats ownership explanations for every
    edge. The semantic planner needs the same information, but only as stable
    names and two adjacency lists.
    """
    rows: list[str] = []
    for label in _design_plan_order(ctx, labels):
        node = ctx.nodes[label]
        statement = sorted(_statement_uses(node))
        proof_only = sorted(_proof_uses(node) - set(statement))
        rows.append(
            json.dumps(
                {
                    "label": label,
                    "lean": (
                        str(node.lean_decl or "").strip()
                        if node.mathlibok
                        else _lean_name(label)
                    ),
                    "statement": statement,
                    "proof_only": proof_only,
                },
                separators=(",", ":"),
                ensure_ascii=True,
            )
        )
    return "\n".join(rows)


def _semantic_plan_prompt(
    ctx: Ctx,
    labels: list[str],
    *,
    timeout_s: int,
) -> str:
    """Request compact root-aware guidance, never a Lean interface plan."""
    roots = _blueprint_roots(ctx.nodes, labels)
    root_text = "\n\n".join(
        f"### {label}\n{ctx.stmt_blocks.get(label, '')[:1800]}"
        for label in roots[:16]
    )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; `{_lean_name(label)}`)\n"
        f"source_notready={str(bool(getattr(ctx.nodes[label], 'notready', False))).lower()}; "
        f"has_blueprint_proof={str(_blueprint_node_has_proof(ctx, label)).lower()}\n"
        f"{ctx.stmt_blocks.get(label, '')[:1400]}"
        for label in labels
    )
    return f"""TASK: COMPACT-BLUEPRINT-SEMANTIC-PLAN

Return JSON only:
{{
  "contracts": [
    {{
      "label": "exact blueprint label",
      "representation": "brief mathematical representation choice",
      "vocabulary": [{{"name": "stable Lean-style name", "purpose": "brief role"}}],
      "obligations": ["mathematical content the later statement must preserve"],
      "provider_requirements": [{{"provider": "direct statement dependency label", "capabilities": ["surface needed from that provider"]}}],
      "readiness": "ready | underspecified | explicitly_unresolved",
      "gap": "empty when ready; otherwise one short concrete reason"
    }}
  ]
}}

This is a lightweight advisory plan for Phase 1, not a Lean declaration pass.
Do NOT write Lean signatures, binder types, structure fields, constructors,
proofs, imports, or definition bodies. The Phase-1 statement generator will
create the exact typed contract together with the actual Lean declaration, and
the compiler plus independent audit will judge that declaration directly.

`readiness` is advisory. Use `underspecified` only when the blueprint omits
mathematical information needed to state this node faithfully, and
`explicitly_unresolved` only when the source itself marks a TODO, `\\notready`,
or an unresolved/open claim. Do not classify a node as non-ready merely because
its eventual proof is difficult or a Lean encoding is uncertain. The harness
independently confirms every non-ready advisory before it can cause a blueprint
edit.

Include exactly one compact entry for every requested label. Keep each
representation under 300 characters, at most 8 vocabulary names, at most 6
obligations, and at most 8 capabilities per provider. Root obligations may
shape representation choices and required semantics, but cannot add graph
edges. The graph table is authoritative:
- only `statement` providers may appear in `provider_requirements` or a public
  Phase-1 signature;
- `proof_only` providers are reserved for Phase 2 and must not shape a public
  signature merely because a proof will use them;
- Mathlib-owned names are already settled under the listed `lean` spelling.

The blueprint remains the sole mathematical source of truth. This plan may
coordinate vocabulary, but it may not weaken, strengthen, replace, or bundle
away any blueprint claim. If uncertain, preserve the obligation in plain
mathematical language and leave exact Lean typing to Phase 1.

This call has a wall-clock budget of about {timeout_s}s. Do not inspect files,
run Lean, or search libraries.

Blueprint: {ctx.name}

Authoritative dependency graph (JSON Lines):
```jsonl
{_compact_dependency_contract_table(ctx, labels)}
```

Root obligations:
{root_text or '- none'}

Nodes to coordinate ({len(labels)}):
{target_text}
"""


def _ensure_phase1_semantic_plan(
    ctx: Ctx, pending: set[str]
) -> None:
    """Create one bounded advisory plan without any pre-Phase-1 repair loop."""
    ordered = _design_plan_order(ctx, pending)
    entries = getattr(ctx, "semantic_plan_entries", {})
    ctx.semantic_plan_entries = entries
    stale = {
        label
        for label, entry in entries.items()
        if label not in ctx.nodes
        or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        or int(entry.get("schema_version") or 0) != SEMANTIC_PLAN_SCHEMA_VERSION
    }
    for label in stale:
        entries.pop(label, None)
    missing = [label for label in ordered if label not in entries]
    if not missing:
        _record(
            ctx.telemetry,
            "phase1_semantic_plan_reused",
            labels=ordered,
            entry_count=len(ordered),
        )
        return

    # Unit-level scheduler callers intentionally use a lightweight context
    # with no runner configuration. They exercise traversal, not planning.
    # Populate the same deterministic fallback a failed advisory call would
    # produce, without requiring every test double to emulate a model runner.
    if not hasattr(ctx, "hard_timeout"):
        for label in missing:
            entries[label] = _semantic_plan_fallback_entry(ctx, label)
        return

    _log(
        f"==> {_contract_work_stage(ctx)} semantic plan: coordinating "
        f"{len(missing)} node(s) in one compact full-context call"
    )
    prompt = _semantic_plan_prompt(ctx, missing, timeout_s=ctx.hard_timeout)

    # ``hard_timeout`` is the hedge threshold for this one unusually large
    # all-node response, not the point at which its producer is destroyed.
    # Give each lane one additional threshold window as a final safety ceiling.
    # The normal Phase-1 and Phase-2 call sites retain ordinary timeout
    # semantics.
    hedge_after_s = ctx.hard_timeout
    planner_call_ceiling_s = max(hedge_after_s + 1, hedge_after_s * 2)
    planner_tier = getattr(ctx, "planner_tier", "escalation")
    planner_escalated = planner_tier == "escalation"
    planner_effort = (
        getattr(ctx, "escalation_effort", None)
        if planner_escalated
        else getattr(ctx, "base_effort", None)
    )
    planner_runner_spec = (
        getattr(ctx, "escalation_runner_spec", "")
        if planner_escalated
        else getattr(ctx, "runner_spec", "")
    )

    def call_plan(
        *,
        force_fresh: bool = False,
        control: _ModelCallControl | None = None,
    ) -> CallResult:
        return _call_model(
            ctx,
            prompt,
            purpose="phase1_semantic_plan",
            timeout=planner_call_ceiling_s,
            effort=planner_effort,
            labels=missing,
            escalated=planner_escalated,
            force_fresh=force_fresh,
            control=control,
        )

    primary_control = _ModelCallControl()
    hedge_control = _ModelCallControl()
    pool = concurrent.futures.ThreadPoolExecutor(max_workers=2)
    primary = pool.submit(call_plan, control=primary_control)
    hedge: concurrent.futures.Future[CallResult] | None = None
    result: CallResult | None = None
    failures: list[CallResult] = []
    usable_results: list[CallResult] = []
    parsed: dict[str, dict[str, Any]] = {}
    findings: dict[str, list[str]] = {}
    response_chars = 0
    winner = ""

    def absorb_candidate(candidate: CallResult, lane: str) -> bool:
        """Merge valid coverage and report whether the requested plan is complete."""
        nonlocal response_chars, result, winner
        plan_text = candidate.text or candidate.partial_text
        candidate_parsed: dict[str, dict[str, Any]] = {}
        if plan_text.strip():
            candidate_parsed, candidate_findings = _parse_semantic_plan_entries(
                ctx, missing, plan_text
            )
            response_chars += len(plan_text)
            usable_results.append(candidate)
            for label, entry in candidate_parsed.items():
                parsed.setdefault(label, entry)
            for label, messages in candidate_findings.items():
                target = findings.setdefault(label, [])
                target.extend(message for message in messages if message not in target)

        if len(parsed) == len(missing):
            result = candidate
            winner = lane if len(candidate_parsed) == len(missing) else "merged"
            return True
        if candidate.status != "ok" or not plan_text.strip():
            failures.append(candidate)
        return False

    try:
        done, _pending = concurrent.futures.wait([primary], timeout=hedge_after_s)
        if not done:
            _record(
                ctx.telemetry,
                "phase1_semantic_plan_hedge_started",
                labels=missing,
                hedge_after_s=hedge_after_s,
                call_ceiling_s=planner_call_ceiling_s,
                planner_tier=planner_tier,
                runner=planner_runner_spec,
            )
            _log(
                "  compact semantic planner exceeded the "
                f"{hedge_after_s}s hedge threshold; keeping it alive and "
                "starting one fresh parallel call"
            )
            hedge = pool.submit(call_plan, force_fresh=True, control=hedge_control)

        active: set[concurrent.futures.Future[CallResult]] = {primary}
        if hedge is not None:
            active.add(hedge)
        while active and result is None:
            completed, _pending = concurrent.futures.wait(
                active, return_when=concurrent.futures.FIRST_COMPLETED
            )
            for future in completed:
                active.remove(future)
                try:
                    candidate = future.result()
                except RunnerError as exc:
                    if is_environment_error(exc):
                        primary_control.cancel()
                        hedge_control.cancel()
                        raise
                    failures.append(
                        CallResult(
                            status=(
                                "transport_exhausted"
                                if is_transient_error(exc)
                                else "error"
                            ),
                            error=str(exc),
                        )
                    )
                    continue
                lane = "hedge" if future is hedge else "primary"
                if absorb_candidate(candidate, lane):
                    break

            # A fast silent or incomplete response should not force us to wait
            # for the hedge threshold merely to start the one recovery lane.
            if result is None and not active and hedge is None:
                _record(
                    ctx.telemetry,
                    "phase1_semantic_plan_hedge_started",
                    labels=missing,
                    hedge_after_s=0,
                    call_ceiling_s=planner_call_ceiling_s,
                    planner_tier=planner_tier,
                    runner=planner_runner_spec,
                    reason="primary_finished_with_incomplete_coverage",
                    planned_count=len(parsed),
                    missing_count=len(missing) - len(parsed),
                )
                _log(
                    "  compact semantic planner covered "
                    f"{len(parsed)}/{len(missing)} node(s); preserving those "
                    "entries and starting one fresh recovery call"
                )
                hedge = pool.submit(
                    call_plan, force_fresh=True, control=hedge_control
                )
                active.add(hedge)

        if result is None:
            result = (
                usable_results[-1]
                if usable_results
                else failures[-1]
                if failures
                else CallResult(
                    status="error", error="semantic planner produced no result"
                )
            )
        else:
            loser_cancelled = bool(active)
            if winner == "primary":
                hedge_control.cancel()
            elif winner == "hedge":
                primary_control.cancel()
            _record(
                ctx.telemetry,
                "phase1_semantic_plan_hedge_result",
                labels=missing,
                winner=winner,
                hedge_started=hedge is not None,
                loser_cancelled=loser_cancelled,
                winner_duration_s=result.duration_s,
            )
            if loser_cancelled:
                _log(
                    f"  compact semantic planner {winner} coverage won; "
                    "cancelled incomplete loser"
                )
    finally:
        if result is None:
            primary_control.cancel()
            hedge_control.cancel()
        pool.shutdown(wait=False, cancel_futures=True)

    if result.status == "transport_exhausted":
        _log(
            "  compact semantic planner unavailable after transport retries; "
            "using blueprint-only fallback guidance"
        )
    entries.update(parsed)
    fallback_labels = [label for label in missing if label not in parsed]
    for label in fallback_labels:
        entries[label] = _semantic_plan_fallback_entry(ctx, label)
    _record(
        ctx.telemetry,
        "phase1_semantic_plan_result",
        labels=missing,
        status=result.status,
        planned_count=len(parsed),
        fallback_count=len(fallback_labels),
        response_chars=response_chars,
        sanitized_findings=findings,
        schema_version=SEMANTIC_PLAN_SCHEMA_VERSION,
        authoritative=False,
        planner_tier=planner_tier,
        runner=planner_runner_spec,
    )
    _log(
        f"  semantic plan stored {len(parsed)}/{len(missing)} model entry/entries; "
        f"{len(fallback_labels)} blueprint-only fallback(s); no planning repair calls"
    )


def _readiness_repair_components(
    ctx: Ctx, evidence_by_label: Mapping[str, str]
) -> list[dict[str, Any]]:
    """Partition readiness repairs only when their blueprint scopes are independent."""
    labels = set(evidence_by_label)
    if len(labels) < 2:
        return []
    related: dict[str, set[str]] = {label: set() for label in labels}
    closures = {
        label: _transitive_dependencies(ctx.nodes, label) & labels
        for label in labels
    }
    for label, dependencies in closures.items():
        for dependency in dependencies:
            related[label].add(dependency)
            related[dependency].add(label)
    components: list[list[str]] = []
    remaining = set(labels)
    while remaining:
        seed = min(remaining)
        stack = [seed]
        component: set[str] = set()
        while stack:
            current = stack.pop()
            if current in component:
                continue
            component.add(current)
            stack.extend(sorted(related[current] - component, reverse=True))
        remaining.difference_update(component)
        components.append(sorted(component))
    if len(components) < 2:
        return []
    return [
        {
            "labels": component,
            "evidence": "\n".join(evidence_by_label[label] for label in component),
        }
        for component in components
    ]


def _phase1_readiness_repair_request(
    ctx: Ctx,
    evidence_by_label: Mapping[str, str],
    *,
    source: str,
) -> RepairRequest:
    """Route confirmed source defects through the normal blueprint transaction."""
    ordered = _design_plan_order(ctx, evidence_by_label)
    evidence = (
        "Phase 1 readiness gate rejected blueprint source before Lean statement "
        "generation. Resolve each exact source defect without weakening its claim. "
        "For a theorem-like node, add a complete blueprint proof and remove "
        "\\notready only after the statement and proof are ready. For a "
        "definition-like node, make its mathematical interface explicit and remove "
        "\\notready only after it is ready to formalize.\n\n"
        + "\n".join(evidence_by_label[label] for label in ordered)
    )
    _record(
        ctx.telemetry,
        "phase1_readiness_repair_requested",
        labels=ordered,
        source=source,
        evidence_by_label=dict(evidence_by_label),
    )
    return RepairRequest(
        evidence,
        ordered,
        section_labels=ordered,
        context_labels=ordered,
        authorizes_blueprint_repair=True,
        model_repair_labels=ordered,
        evidence_by_label=evidence_by_label,
        repair_components=_readiness_repair_components(ctx, evidence_by_label),
    )


def _phase1_source_readiness_request(
    ctx: Ctx, pending: set[str]
) -> RepairRequest | None:
    """Honor source-authoritative unresolved markers before advisory planning."""
    issues: dict[str, str] = {}
    recorded: list[str] = []
    for label in _design_plan_order(ctx, pending):
        node = ctx.nodes[label]
        if _records_conjecture(ctx, label):
            if bool(getattr(node, "notready", False)):
                recorded.append(label)
            continue
        missing_attempted_conjecture_proof = (
            getattr(ctx, "conjecture_policy", "record") == "attempt"
            and _is_conjecture_node(label, node)
            and not _blueprint_node_has_proof(ctx, label)
        )
        if not bool(getattr(node, "notready", False)) and not missing_attempted_conjecture_proof:
            continue
        reasons: list[str] = []
        if bool(getattr(node, "notready", False)):
            reasons.append(
                "the blueprint source explicitly contains \\notready, so this "
                "node is not authorized for ordinary Phase 1 generation"
            )
        if missing_attempted_conjecture_proof:
            reasons.append(
                "conjecture policy `attempt` requires a complete blueprint proof "
                "before its Lean statement is frozen"
            )
        elif _is_theorem_like_kind(node.kind) and not _blueprint_node_has_proof(ctx, label):
            reasons.append(
                "the theorem-like node has no blueprint proof; add one before "
                "removing \\notready"
            )
        issues[label] = f"- {label}: " + "; ".join(reasons)
    if recorded:
        _record(
            ctx.telemetry,
            "phase1_readiness_open_claim_recorded",
            labels=recorded,
            conjecture_policy="record",
            source_notready=True,
        )
    if not issues:
        return None
    return _phase1_readiness_repair_request(
        ctx, issues, source="source_authoritative"
    )


def _readiness_repair_postcondition_findings(
    *,
    before_nodes: Mapping[str, Node],
    after_nodes: Mapping[str, Node],
    before_blocks: Mapping[str, str],
    after_blocks: Mapping[str, str],
    labels: Iterable[str],
    conjecture_policy: str,
) -> list[str]:
    """Reject repairs that erase an unresolved marker without resolving it."""
    findings: list[str] = []
    for label in labels:
        before = before_nodes.get(label)
        if before is None:
            continue
        recorded_open = conjecture_policy == "record" and _is_conjecture_node(
            label, before
        )
        source_notready = bool(getattr(before, "notready", False))
        attempted_conjecture_without_proof = (
            conjecture_policy == "attempt"
            and _is_conjecture_node(label, before)
            and not _blueprint_block_has_proof(str(before_blocks.get(label, "")))
        )
        if recorded_open or not (
            source_notready or attempted_conjecture_without_proof
        ):
            continue
        after = after_nodes.get(label)
        if after is None:
            findings.append(f"{label}: readiness repair deleted the target node")
            continue
        if source_notready and bool(getattr(after, "notready", False)):
            findings.append(
                f"{label}: readiness repair left \\notready in the target node"
            )
        requires_proof = _is_theorem_like_kind(before.kind) and (
            source_notready or attempted_conjecture_without_proof
        )
        if requires_proof and not _blueprint_block_has_proof(
            str(after_blocks.get(label, ""))
        ):
            findings.append(
                f"{label}: readiness repair did not add a blueprint proof"
            )
    return findings


def _phase1_readiness_confirmation_prompt(ctx: Ctx, labels: list[str]) -> str:
    """Ask a separate critic to confirm only planner-reported source gaps."""
    tex_blocks = getattr(ctx, "tex_blocks", None)
    if not isinstance(tex_blocks, Mapping):
        tex_blocks = getattr(ctx, "stmt_blocks", {})
    nodes = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind})\n"
        f"Planner advisory: {str(ctx.semantic_plan_entries[label].get('readiness') or '')}\n"
        f"Planner gap: {str(ctx.semantic_plan_entries[label].get('gap') or '')}\n"
        f"Direct statement dependencies: "
        f"{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or '(none)'}\n"
        f"Complete blueprint node:\n```tex\n{str(tex_blocks.get(label, ''))[:7000]}\n```"
        for label in labels
    )
    return f"""TASK: CONFIRM-BLUEPRINT-READINESS

The compact semantic planner marked the nodes below as potentially not ready.
Independently judge the blueprint source, not the difficulty of Lean encoding
or proof search. Return JSON only:
{{
  "nodes": [
    {{
      "label": "exact requested label",
      "readiness": "ready | underspecified | explicitly_unresolved",
      "gap": "empty when ready; otherwise the concrete missing source information"
    }}
  ]
}}

Use `underspecified` only when the mathematical statement omits information
needed to know exactly what must be formalized. Use `explicitly_unresolved`
only when the source itself leaves a TODO, missing argument, or unresolved
claim. A hard theorem, unfamiliar notation, or uncertain Lean API is still
`ready` when its mathematical contract is clear. Do not write Lean, repair the
blueprint, inspect files, run commands, or search libraries. Include every
requested label exactly once.

Blueprint: {ctx.name}

{nodes}

Relevant paper excerpt:
<paper>
{_paper_excerpt_for(ctx, labels, budget=14000)}
</paper>
"""


def _parse_phase1_readiness_confirmation(
    labels: Iterable[str], text: str
) -> dict[str, dict[str, str]]:
    requested = set(labels)
    payload, _repaired = _extract_json_object_with_key(text, "nodes")
    raw_nodes = payload.get("nodes")
    if not isinstance(raw_nodes, list):
        raise ValueError("readiness confirmation omitted its nodes array")
    parsed: dict[str, dict[str, str]] = {}
    for raw in raw_nodes:
        if not isinstance(raw, dict):
            continue
        label = str(raw.get("label") or "").strip()
        readiness = str(raw.get("readiness") or "").strip().lower()
        gap = str(raw.get("gap") or "").strip()[:1000]
        if label not in requested or label in parsed:
            continue
        if readiness not in SEMANTIC_READINESS_VALUES:
            continue
        if readiness != "ready" and not gap:
            continue
        parsed[label] = {
            "readiness": readiness,
            "gap": gap if readiness != "ready" else "",
        }
    return parsed


def _phase1_advisory_readiness_request(
    ctx: Ctx, pending: set[str]
) -> RepairRequest | None:
    """Confirm planner warnings once; only confirmed source defects may edit TeX."""
    semantic_entries = getattr(ctx, "semantic_plan_entries", {})
    labels = [
        label
        for label in _design_plan_order(ctx, pending)
        if not _records_conjecture(ctx, label)
        and str((semantic_entries.get(label) or {}).get("readiness") or "ready")
        != "ready"
        and str(
            (semantic_entries.get(label) or {}).get(
                "readiness_confirmation"
            )
            or "pending"
        )
        == "pending"
    ]
    if not labels:
        return None
    _log(
        f"==> Phase 1 readiness confirmation: checking {len(labels)} "
        "advisory planner flag(s) before statement generation"
    )
    prompt = _phase1_readiness_confirmation_prompt(ctx, labels)
    result = _call_model(
        ctx,
        prompt,
        purpose="phase1_readiness_confirmation",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=labels,
        tag="readiness",
    )
    parsed: dict[str, dict[str, str]] = {}
    parse_error = ""
    if result.status == "ok":
        try:
            parsed = _parse_phase1_readiness_confirmation(labels, result.text)
        except ValueError as exc:
            parse_error = str(exc)
    else:
        parse_error = result.error or result.status

    issues: dict[str, str] = {}
    for label in labels:
        entry = semantic_entries[label]
        confirmation = parsed.get(label)
        if confirmation is None:
            entry["readiness_confirmation"] = "unavailable"
            entry["readiness_confirmation_reason"] = parse_error or "missing label"
            continue
        readiness = confirmation["readiness"]
        gap = confirmation["gap"]
        entry["readiness"] = readiness
        entry["gap"] = gap
        entry["readiness_confirmation"] = (
            "confirmed_nonready" if readiness != "ready" else "confirmed_ready"
        )
        entry["readiness_confirmation_reason"] = gap
        if readiness != "ready":
            issues[label] = (
                f"- {label}: independent readiness confirmation classified the "
                f"blueprint as {readiness}: {gap}"
            )

    _record(
        ctx.telemetry,
        "phase1_readiness_confirmation",
        labels=labels,
        status=result.status,
        confirmed_nonready_labels=sorted(issues),
        confirmed_ready_labels=sorted(
            label
            for label in labels
            if (semantic_entries[label].get("readiness_confirmation"))
            == "confirmed_ready"
        ),
        unavailable_labels=sorted(
            label
            for label in labels
            if (semantic_entries[label].get("readiness_confirmation"))
            == "unavailable"
        ),
        parse_error=parse_error,
    )
    if not issues:
        return None
    return _phase1_readiness_repair_request(
        ctx, issues, source="independently_confirmed_planner_advisory"
    )


def _blueprint_roots(nodes: dict[str, Node], labels: Iterable[str]) -> list[str]:
    """Theorem-like labels nothing else depends on: the paper's public results."""
    ordered_labels = list(dict.fromkeys(labels))
    consumed = {dep for label in nodes for dep in nodes[label].uses}
    return [
        label
        for label in ordered_labels
        if _is_theorem_like_kind(nodes[label].kind) and label not in consumed
    ]


def _design_plan_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    timeout_s: int,
    root_context_labels: Iterable[str] | None = None,
    feedback: str = "",
) -> str:
    """Ask for the interface plan only — no bodies, no proofs.

    Deciding the vocabulary root-first is cheap reasoning; writing every
    declaration is not. Splitting them keeps this call small enough to always
    land, and the resulting plan is short enough to inject into every later
    skeleton prompt, so all sections share one coherent design instead of each
    re-deriving it.
    """
    roots = _blueprint_roots(
        ctx.nodes, root_context_labels if root_context_labels is not None else labels
    )
    root_text = "\n\n".join(
        f"### ROOT {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`)\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:2500]}\n```"
        for label in roots[:12]
    )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:1200]}\n```"
        for label in labels
    )
    signatures = _frozen_interface_digest(sections, import_modules, budget=10000)
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    return f"""TASK: BLUEPRINT-SKELETON-DESIGN-PLAN

Return a PLAN only. No proofs and no definition bodies. Return exactly one
JSON object in this schema:
{{
  "contracts": [
    {{
      "label": "exact blueprint label",
      "target_signature": "complete Lean-ish target signature using the required Lean name",
      "helpers": [
        {{"name": "stable helper name", "kind": "structure|inductive|class", "members": [{{"name": "stable_field_or_constructor", "type": "complete Lean-ish member type"}}], "purpose": "brief type-interface role"}}
      ],
      "decisions": ["semantic/interface decision generation must preserve"]
    }}
  ]
}}

You are fixing the shared vocabulary for a Lean skeleton before it is written
section by section. Reason ROOT-FIRST: start from the public results under
"Root obligations", decide what each needs in order to be a NON-TRIVIAL,
faithful claim, and let that determine the shape of every definition beneath
it. The declarations themselves will be emitted later in dependency order.

Hard design rule: a definition must never assume the conclusion of a theorem
that depends on it. If a root asserts `X = Y` or `X ⊆ Y`, then `X` and `Y`
must be defined independently — folding the relation into either definition
makes the root vacuous.

Include exactly one contract for every requested node. A helper is permitted
only when the target needs an auxiliary `structure`, `inductive`, or `class`
type interface in order to be stated. Put that helper under its owning node and
give every stable field or constructor its complete Lean-ish type. A member-name
list without types is invalid: the later statement writer must copy the planned
interface rather than invent it. Never create helper `def`, `abbrev`,
`theorem`, or `lemma` declarations: their bodies/proofs would be untracked by
Phase 2. Put equations and semantic properties in the target signature when
they are part of the statement, or in `decisions` when they govern the target's
Phase-2 implementation. Record up to five decisions per node that a later
writer could otherwise get wrong. Do not collapse concrete blueprint objects
into opaque predicates or package names unless the compact helper surface
explicitly exposes the complete promised interface.

Each `target_signature` must contain exactly one top-level declaration and it
must use that node's required Lean name. A blueprint node may describe several
related mathematical operations, but that does not authorize several public
Lean targets for one node. Represent such a bundle with one plan-owned
`structure` or `class` helper whose fields expose the operations and defining
laws, then make the single canonical target return that interface.

The deterministic dependency-contract table below is the sole authoritative
allowed-symbol table for generated dependencies. A `statement interface` entry
may appear in `target_signature`. A `proof only` entry may guide the later
Phase-2 implementation, but it MUST NOT appear in `target_signature` merely
because the proof uses it. Every other non-library name in `target_signature`
must be the target's required Lean name or a structure/inductive/class helper
declared in that same contract. Do not infer another generated dependency from
the root context, surrounding prose, or mathematical convenience. Root context
may shape the meaning and strength of an interface, but it cannot add a
dependency edge absent from the blueprint graph. Do not put an executable
convenience function such as a custom logarithm, conversion, or constructor in
the signature unless it is an authorized statement-interface dependency or a
verified library declaration. Express it directly with available library
vocabulary, or require blueprint decomposition.

Keep signatures and decisions compact. This call has a budget of about
{timeout_s}s; it is a planning call, so do not verify every Mathlib API now —
note the intended type and move on.

{_design_plan_rules(ctx, labels)}

Correction required from a previous invalid planning response:
{feedback[-5000:] if feedback else '- none'}

Blueprint name: {ctx.name}

Frozen Lean interface already available (do not redesign these):
```lean
{signatures or '-- none'}
```

Authoritative direct dependency contracts (generated deterministically from
the blueprint graph; do not infer or invent additional dependency edges):
```text
{dependency_contracts}
```

Root obligations — design everything below to serve these:
{root_text or '- (no unconsumed theorem-like roots in this batch)'}

Target nodes to plan ({len(labels)} node(s), root-first planning order):
{target_text}
"""


def _generate_design_plan_candidate(
    ctx: Ctx,
    ordered: list[str],
    sections: list[Section],
    imports: list[str],
    root_context: list[str],
    candidate_id: str,
    *,
    max_empty_response_retries: int = 1,
    initial_feedback: str = "",
    timeout_s: int | None = None,
) -> DesignPlanCandidate:
    """Generate one independent full-context plan candidate."""
    call_timeout = timeout_s if timeout_s is not None else ctx.base_timeout
    candidate_entries: dict[str, dict[str, Any]] = {}
    missing = list(ordered)
    empty_response_retries = 0
    invalid_response_feedback = initial_feedback
    while missing:
        plan_labels = missing[:DESIGN_PLAN_MAX_NODES]
        result = _call_model(
            ctx,
            _design_plan_prompt(
                ctx,
                plan_labels,
                sections,
                imports,
                timeout_s=call_timeout,
                root_context_labels=root_context,
                feedback=invalid_response_feedback,
            ),
            purpose=f"phase1_design_plan_candidate_{candidate_id.lower()}",
            timeout=call_timeout,
            effort=ctx.base_effort,
            labels=plan_labels,
        )
        if result.status != "ok" or not result.text.strip():
            _record(
                ctx.telemetry,
                "phase1_design_plan_candidate_result",
                candidate_id=candidate_id,
                labels=plan_labels,
                status=result.status,
                planned_count=0,
            )
            break
        parsed = _parse_design_plan_entries(ctx, plan_labels, result.text)
        candidate_entries.update(parsed)
        missing_from_reply = sorted(set(plan_labels) - set(parsed))
        _record(
            ctx.telemetry,
            "phase1_design_plan_candidate_result",
            candidate_id=candidate_id,
            labels=plan_labels,
            status="ok" if parsed else "invalid_empty_contracts",
            planned_labels=sorted(parsed),
            planned_count=len(parsed),
            missing_labels=missing_from_reply,
            chars=len(result.text),
        )
        if not parsed:
            if empty_response_retries < max_empty_response_retries:
                empty_response_retries += 1
                invalid_response_feedback = (
                    "The previous response contained zero usable contracts. "
                    f"Return exactly {len(plan_labels)} contracts, one for each "
                    "requested label, in the required JSON schema. Do not return "
                    "an empty contracts array or any Lean code."
                )
                continue
            break
        empty_response_retries = 0
        invalid_response_feedback = ""
        missing = [label for label in ordered if label not in candidate_entries]

    return _evaluate_design_plan_candidate(
        ctx, ordered, candidate_entries, candidate_id
    )


def _initial_design_plan_tournament(
    ctx: Ctx,
    ordered: list[str],
    sections: list[Section],
    imports: list[str],
    root_context: list[str],
) -> tuple[DesignPlanCandidate, DesignPlanCandidate]:
    """Admit the first complete plan whose initial frontier is executable.

    Two independent full-context candidates hedge model variability. A plan
    with complete JSON coverage is not automatically usable: deterministic
    closure must leave the entire initial dependency-ready frontier open. A
    qualifying lane may start Phase 1 without waiting for a redundant sibling;
    if neither lane qualifies, the outer bounded repair loop restarts the whole
    tournament instead of serially repairing a catastrophic shared plan.
    """
    _log(
        f"==> {_contract_work_stage(ctx)} design plan: generating two independent full-context "
        f"candidates concurrently ({len(ordered)} nodes)"
    )
    candidates: list[DesignPlanCandidate] = []
    # Lightweight callers created before the separate hard-timeout setting may
    # only provide base_timeout. Preserve that compatibility while ensuring a
    # real run gives both full-context lanes the longer configured budget.
    planner_timeout = max(
        ctx.base_timeout,
        getattr(ctx, "hard_timeout", ctx.base_timeout),
    )
    retry_feedback = _generation_feedback_for(ctx, ordered)

    def finish(
        selected: DesignPlanCandidate,
        completed: list[DesignPlanCandidate],
        merged_components: list[list[str]],
        *,
        selection_mode: str = "closed_initial_frontier",
    ) -> tuple[DesignPlanCandidate, DesignPlanCandidate]:
        alternates = [candidate for candidate in completed if candidate is not selected]
        alternate = min(
            alternates or [selected],
            key=lambda item: (item.score, item.candidate_id),
        )
        for candidate in completed:
            clean_admissible, frontier, blocked = _initial_plan_admission(
                ctx, ordered, candidate
            )
            repairable, _frontier, _blocked, repair_work, tournament_work = (
                _initial_plan_repair_admission(ctx, ordered, candidate)
            )
            _record(
                ctx.telemetry,
                "phase1_design_plan_candidate_scored",
                candidate_id=candidate.candidate_id,
                labels=ordered,
                score=list(candidate.score),
                planned_count=len(candidate.entries),
                missing_labels=candidate.missing,
                blocked_labels=sorted(candidate.blocked),
                component_count=len(candidate.components),
                findings=[
                    finding
                    for label in sorted(candidate.findings)
                    for finding in candidate.findings[label]
                ],
                initial_frontier=frontier,
                blocked_initial_frontier=blocked,
                admissible=clean_admissible or repairable,
                clean_initial_frontier=clean_admissible,
                scoped_repair_admissible=repairable,
                estimated_repair_work=repair_work,
                estimated_tournament_work=tournament_work,
                selected=candidate is selected,
            )
        _record(
            ctx.telemetry,
            "phase1_design_plan_tournament",
            labels=ordered,
            primary_candidate=selected.candidate_id,
            alternate_candidate=alternate.candidate_id,
            selected_candidate=selected.candidate_id,
            selected_score=list(selected.score),
            merged_components=merged_components,
            admission_policy="complete_frontier_or_cheaper_scoped_repair",
            selection_mode=selection_mode,
        )
        if selection_mode == "cheaper_scoped_repair":
            repair_work, tournament_work = _initial_plan_repair_costs(
                selected, len(ordered)
            )
            _log(
                "  design-plan tournament admitted "
                f"{selected.candidate_id} for scoped closure repair "
                f"({repair_work} estimated work units vs {tournament_work} "
                "for another tournament); "
                f"merged {len(merged_components)} improving component(s)"
            )
        else:
            _log(
                "  design-plan tournament admitted "
                f"{selected.candidate_id} with score {selected.score}; "
                f"merged {len(merged_components)} improving component(s)"
            )
        fallback_entries: dict[str, dict[str, Any]] = {}
        for label in ordered:
            selected_entry = selected.entries.get(label)
            for candidate in completed:
                candidate_entry = candidate.entries.get(label)
                if candidate_entry is not None and candidate_entry != selected_entry:
                    fallback_entries[label] = copy.deepcopy(candidate_entry)
                    break
        fallback = _evaluate_design_plan_candidate(
            ctx, ordered, fallback_entries, "per-node-alternate"
        )
        return selected, fallback

    pool = concurrent.futures.ThreadPoolExecutor(max_workers=2)
    futures = {
        pool.submit(
            _generate_design_plan_candidate,
            ctx,
            ordered,
            sections,
            imports,
            root_context,
            candidate_id,
            max_empty_response_retries=0,
            initial_feedback=retry_feedback,
            timeout_s=planner_timeout,
        ): candidate_id
        for candidate_id in ("A", "B")
    }
    returned_early = False
    try:
        while futures:
            done, _pending = concurrent.futures.wait(
                futures,
                return_when=concurrent.futures.FIRST_COMPLETED,
            )
            for future in done:
                candidate_id = futures.pop(future)
                candidate = future.result()
                candidates.append(candidate)
                admissible, frontier, blocked = _initial_plan_admission(
                    ctx, ordered, candidate
                )
                _record(
                    ctx.telemetry,
                    "phase1_design_plan_candidate_admission",
                    candidate_id=candidate_id,
                    score=list(candidate.score),
                    initial_frontier=frontier,
                    blocked_initial_frontier=blocked,
                    admissible=admissible,
                )
                if not admissible:
                    _log(
                        "  design-plan tournament rejected "
                        f"{candidate_id}: initial frontier "
                        f"{len(frontier) - len(blocked)}/{len(frontier)} ready"
                    )
                    continue
                for sibling in futures:
                    sibling.cancel()
                returned_early = True
                pool.shutdown(wait=False, cancel_futures=True)
                return finish(candidate, candidates, [])
    finally:
        if not returned_early:
            pool.shutdown(wait=True, cancel_futures=True)

    candidates.sort(key=lambda item: (item.score, item.candidate_id))
    primary = candidates[0]
    alternate = candidates[1] if len(candidates) > 1 else candidates[0]
    selected, merged_components = _merge_design_plan_candidates(
        ctx, ordered, primary, alternate
    )
    admissible, frontier, blocked = _initial_plan_admission(ctx, ordered, selected)
    if admissible:
        return finish(selected, candidates, merged_components)

    repair_options: list[
        tuple[int, tuple[int, int, int, int], str, DesignPlanCandidate]
    ] = []
    seen_options: set[int] = set()
    for option in [selected, *candidates]:
        if id(option) in seen_options:
            continue
        seen_options.add(id(option))
        repairable, _frontier, _blocked, repair_work, _tournament_work = (
            _initial_plan_repair_admission(ctx, ordered, option)
        )
        if repairable:
            repair_options.append(
                (repair_work, option.score, option.candidate_id, option)
            )
    if repair_options:
        repair_selected = min(repair_options)[-1]
        return finish(
            repair_selected,
            candidates,
            merged_components if repair_selected is selected else [],
            selection_mode="cheaper_scoped_repair",
        )

    for candidate in candidates:
        (
            candidate_repairable,
            _frontier,
            candidate_blocked,
            candidate_repair_work,
            candidate_tournament_work,
        ) = _initial_plan_repair_admission(ctx, ordered, candidate)
        _record(
            ctx.telemetry,
            "phase1_design_plan_candidate_scored",
            candidate_id=candidate.candidate_id,
            labels=ordered,
            score=list(candidate.score),
            planned_count=len(candidate.entries),
            missing_labels=candidate.missing,
            blocked_labels=sorted(candidate.blocked),
            component_count=len(candidate.components),
            findings=[
                finding
                for label in sorted(candidate.findings)
                for finding in candidate.findings[label]
            ],
            initial_frontier=frontier,
            blocked_initial_frontier=candidate_blocked,
            admissible=False,
            clean_initial_frontier=False,
            scoped_repair_admissible=candidate_repairable,
            estimated_repair_work=candidate_repair_work,
            estimated_tournament_work=candidate_tournament_work,
            selected=False,
        )
    _record(
        ctx.telemetry,
        "phase1_design_plan_tournament",
        labels=ordered,
        primary_candidate=primary.candidate_id,
        alternate_candidate=alternate.candidate_id,
        selected_candidate="",
        selected_score=list(selected.score),
        merged_components=merged_components,
        admission_policy="complete_frontier_or_cheaper_scoped_repair",
        status="rejected_no_admissible_plan",
    )
    _log(
        "  design-plan tournament produced no admissible plan; restarting "
        "the complete tournament through the bounded repair loop"
    )
    evidence = (
        "The independent initial planning candidates were complete or exhausted, "
        "but none left the entire initial dependency-ready frontier mechanically "
        "closed or had a bounded closure-repair estimate cheaper than another "
        "two-lane full-context tournament. Discard every candidate and restart "
        "the full-context planning tournament; do not enter Phase 1 with a "
        "globally expensive plan.\n"
        + "\n".join(
            f"- candidate {candidate.candidate_id}: score={candidate.score}; "
            f"blocked initial frontier="
            f"{', '.join(sorted(set(frontier) & candidate.blocked)) or 'none'}; "
            f"repair/tournament work={_initial_plan_repair_costs(candidate, len(ordered))}"
            for candidate in candidates
        )
    )
    raise RepairRequest(
        evidence,
        list(ordered),
        section_labels=list(ordered),
        authorizes_blueprint_repair=False,
        failure_route=_route_lean_generation_failure(ordered),
    )


def _ensure_phase1_design_plan(
    ctx: Ctx,
    pending: set[str],
    sections: list[Section],
    *,
    defer_closure_repair: bool = False,
) -> dict[str, list[str]]:
    """Create or extend the shared root-first contract plan for Phase 1.

    Traversal still controls declaration generation. This planning call is
    traversal-independent: it fixes shared contract decisions once so either
    traversal can transcribe them without redesigning each section locally.
    """
    _prune_stale_design_plan(ctx)
    ordered = _design_plan_order(ctx, pending)
    entries = getattr(ctx, "design_plan_entries", None)
    if entries is None:
        entries = {}
        ctx.design_plan_entries = entries
    missing = [
        label
        for label in ordered
        if label not in entries
        and not _uses_blueprint_direct_generation(ctx, label)
    ]
    if not missing:
        if ordered:
            _record(
                ctx.telemetry,
                "phase1_design_plan_reused",
                labels=ordered,
                entry_count=len(ordered),
            )

    imports = _sections_for_deps(ctx, ordered, sections)
    root_context = [
        label for label, node in ctx.nodes.items() if not node.mathlibok
    ]
    if not entries and len(missing) > 1:
        selected, alternate = _initial_design_plan_tournament(
            ctx,
            ordered,
            sections,
            imports,
            root_context,
        )
        entries.update(copy.deepcopy(selected.entries))
        ctx.design_plan_alternates = {
            label: copy.deepcopy(entry)
            for label, entry in alternate.entries.items()
            if label in entries and entry != entries[label]
        }
        _transition_phase1_generation_epoch(
            ctx,
            selected.entries,
            reason="initial_plan_tournament_selected",
        )
        _record(
            ctx.telemetry,
            "phase1_design_plan_result",
            labels=ordered,
            status="tournament_selected",
            planned_labels=sorted(entries),
            planned_count=len(entries),
            missing_labels=[label for label in ordered if label not in entries],
            alternate_count=len(ctx.design_plan_alternates),
            selected_score=list(selected.score),
        )
        missing = [
            label
            for label in ordered
            if label not in entries
            and not _uses_blueprint_direct_generation(ctx, label)
        ]
        if missing:
            _activate_blueprint_direct_generation(
                ctx,
                missing,
                "The full-context planning tournament returned no usable "
                "contract for these labels. Phase 1 must formalize their "
                "statements directly from the blueprint instead of paying "
                "another global planning call.",
                source="initial_plan_missing_contract",
                shared_evidence=True,
            )
            missing = []

    empty_response_retries = 0
    invalid_response_feedback = ""
    while missing:
        # Ordinary papers fit in one call. Very large graphs are bounded here
        # so planning itself cannot become the oversized prompt Phase 1 is
        # intended to eliminate.
        plan_labels = missing[:DESIGN_PLAN_MAX_NODES]
        _log(
            f"==> {_contract_work_stage(ctx)} design plan: fixing {len(plan_labels)} missing contract "
            f"decision(s) root-first ({len(entries)} reused)"
        )
        result = _call_model(
            ctx,
            _design_plan_prompt(
                ctx,
                plan_labels,
                sections,
                imports,
                timeout_s=ctx.base_timeout,
                root_context_labels=root_context,
                feedback=(
                    invalid_response_feedback
                    or _generation_feedback_for(ctx, plan_labels)
                ),
            ),
            purpose="phase1_design_plan",
            timeout=ctx.base_timeout,
            effort=ctx.base_effort,
            labels=plan_labels,
        )
        if result.status != "ok" or not result.text.strip():
            _record(
                ctx.telemetry,
                "phase1_design_plan_result",
                labels=plan_labels,
                status=result.status,
                planned_count=0,
            )
            _log(
                f"  design plan {result.status}; {_contract_work_stage(ctx)} continues with existing "
                "plan entries"
            )
            break

        parsed = _parse_design_plan_entries(ctx, plan_labels, result.text)
        entries.update(parsed)
        if parsed:
            _transition_phase1_generation_epoch(
                ctx,
                parsed,
                reason="scoped_plan_entries_created",
            )
        else:
            _sync_design_plan(ctx)
        missing_from_reply = sorted(set(plan_labels) - set(parsed))
        response_status = "ok" if parsed else "invalid_empty_contracts"
        _record(
            ctx.telemetry,
            "phase1_design_plan_result",
            labels=plan_labels,
            status=response_status,
            planned_labels=sorted(parsed),
            planned_count=len(parsed),
            missing_labels=missing_from_reply,
            chars=len(result.text),
        )
        _log(
            f"  design plan stored {len(parsed)}/{len(plan_labels)} contract "
            f"decision(s); {len(entries)} reusable entry/entries total"
        )
        if not parsed:
            if empty_response_retries < 1:
                empty_response_retries += 1
                invalid_response_feedback = (
                    "The previous response contained zero usable contracts. "
                    f"Return exactly {len(plan_labels)} contracts, one for each "
                    "requested label, in the required JSON schema. Do not return "
                    "an empty contracts array or any Lean code."
                )
                _log(
                    "  invalid zero-contract design plan; retrying once with "
                    "explicit completeness feedback"
                )
                continue
            break
        empty_response_retries = 0
        invalid_response_feedback = ""
        missing = [
            label
            for label in ordered
            if label not in entries
            and not _uses_blueprint_direct_generation(ctx, label)
        ]

    missing = [
        label
        for label in ordered
        if label not in entries
        and not _uses_blueprint_direct_generation(ctx, label)
    ]
    if missing:
        _activate_blueprint_direct_generation(
            ctx,
            missing,
            "The scoped design-plan call omitted these contracts. Generate "
            "their exact statements directly from the blueprint and frozen "
            "dependency interfaces.",
            source="scoped_plan_missing_contract",
            shared_evidence=True,
        )
    closure_findings = _validate_design_plan_contract_closure(ctx, ordered)
    if closure_findings:
        if defer_closure_repair:
            _record(
                ctx.telemetry,
                "phase1_design_plan_closure_deferred",
                labels=sorted(closure_findings),
                blocked_labels=sorted(
                    _closure_blocked_labels(ctx, closure_findings)
                ),
            )
            return closure_findings
        _repair_phase1_design_plan_closure(ctx, ordered, closure_findings)
    # Do not audit the complete proposed plan here. The dependency-ready
    # frontier gateway checks only contracts that are about to reach statement
    # generation, with direct providers and consumers as bounded context.
    # Generated declarations still have to satisfy deterministic checks,
    # compile, and pass the independent statement-alignment audit before they
    # freeze; a frontier-plan verdict is never evidence of Lean correctness.
    _record(
        ctx.telemetry,
        "phase1_design_plan_ready",
        labels=ordered,
        entry_count=len(ordered),
        acceptance_policy="compiled_declarations_final_audit",
    )
    return {}


def _bulk_skeleton_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    timeout_s: int,
    initial_only: bool = False,
) -> str:
    """Emit one chunk of the skeleton using the shared design proposal.

    Statements are compiled leaf-first (Lean cannot elaborate a reference to a
    declaration that does not exist yet), but they were *designed* root-first
    by the plan pass, so this call is transcription rather than design.
    """
    if initial_only:
        return _initial_declaration_prompt(
            ctx,
            labels,
            sections,
            import_modules,
            timeout_s=timeout_s,
        )
    roots = _blueprint_roots(ctx.nodes, labels)
    root_text = "\n\n".join(
        f"### ROOT {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`)\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:3000]}\n```"
        for label in roots[:12]
    )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        # The independent audit sees the complete node.  Fresh generation must
        # see it too: proof prose can impose public interface obligations even
        # though Phase 1 still emits only a statement ending in ``:= sorry``.
        f"```tex\n{ctx.tex_blocks.get(label, '')[:6000]}\n```"
        for label in labels
    )
    signatures = _frozen_interface_digest(sections, import_modules, budget=14000)
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    return f"""TASK: BLUEPRINT-SKELETON-SECTION

Return exactly one Lean 4 file (one code block). No commentary.

Emit the statement of EVERY target node below — statements only, no proofs.
The compact guidance above coordinates semantic choices and vocabulary, but
is not a typed Lean contract. Emit declarations in dependency order. The exact
typed target/helper surfaces in this response are persisted together as the
candidate contract and then checked deterministically, compiled, and audited
against the blueprint.

Per-node rules:
- definition-kind nodes (definition/defn/construction/notation/convention):
  emit the exact public type/interface. For an ordinary definition, output
  only `def NAME ... : TYPE := sorry` (or `abbrev`): do not write the defining
  formula after `:=`, and do not move that formula into `TYPE`. A predicate
  described by conditions or witnesses is an ordinary `def ... : Prop :=
  sorry`, not a structure containing those conditions as fields. Use a
  `structure`/`class`/`inductive` only when the blueprint genuinely defines a
  bundled data object with named stored components; expose its exact
  fields/constructors and do not use `sorry`. A type-valued target
  whose complete contract is a same-node structure/class/inductive returned
  in this response
  may be a transparent alias directly to that helper; this is an interface,
  not an implementation body.
- theorem-like nodes (lemma/proposition/theorem/corollary and EVERY other
  environment kind, e.g. claim/fact/remark): the exact statement as a
  `theorem` ending in `:= sorry`. Do NOT attempt proofs in this pass. Recorded
  conjectures are the explicit exception described below.
- Give each blueprint node exactly the Lean name listed for it.
- Besides same-node `structure`/`inductive`/`class` interfaces, emit no
  auxiliary declarations. Executable helpers are not Phase-1 outline work; a
  separate mathematical obligation requires `NEEDS-DECOMPOSITION`.
- Emit a declaration for EVERY target node listed. Coverage is checked
  deterministically.
{_text_only_budget_rule(timeout_s)}

{_common_rules(ctx, labels)}

Blueprint name: {ctx.name}

Available imports for earlier accepted skeleton declarations:
```lean
{chr(10).join(f'import {m}' for m in import_modules) or '-- none'}
```

Frozen Lean interface of those modules (use these exact names; never redefine).
{FROZEN_INTERFACE_NOTE}
```lean
{signatures or '-- none'}
```

Resolved direct dependency contracts (generated deterministically):
```text
{dependency_contracts}
```

{_design_plan_block(ctx, labels)}

Root obligations these statements must serve:
{root_text or '- (no unconsumed theorem-like roots in this batch)'}

Target nodes for THIS file ({len(labels)} node(s), listed in dependency order):
{target_text}
"""


def _delivered_decl_texts(
    parsed: ParsedModule,
    part_labels: list[str],
    all_target_names: set[str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> list[str] | None:
    """Select a complete helper-connected target component.

    A candidate cannot be split across a helper used by targets on both sides:
    doing so either drops the helper or emits the same global helper in two
    imported modules. Return ``None`` for such a split so routing keeps that
    component atomic.
    """
    part_names = {_lean_name(label) for label in part_labels}
    target_by_name = {name: name for name in all_target_names}
    # This slicing helper represents target identities by Lean declaration
    # name, while the plan ownership map stores blueprint labels. Normalize the
    # latter at this boundary so ownership comparisons use one identity space.
    explicit = {
        name: owner if owner in all_target_names else _lean_name(owner)
        for name, owner in (explicit_owner_by_name or {}).items()
    }
    components = _target_components_from_helpers(
        parsed, target_by_name, explicit
    )
    for component in components:
        if component & part_names and not component <= part_names:
            return None
    consumers = _declaration_target_consumers(
        parsed, target_by_name, explicit
    )
    chosen: list[str] = []
    seen: set[str] = set()
    for index, decl in enumerate(parsed.decls):
        name = decl.name or ""
        if name in part_names:
            chosen.append(decl.text)
            seen.add(name)
        elif name not in all_target_names and consumers.get(index, set()) & part_names:
            chosen.append(decl.text)
    if part_names != seen:
        return None
    return chosen


def _salvage_timeout_declarations(
    ctx: Ctx,
    labels: list[str],
    partial_text: str,
    *,
    realize_contracts: bool = False,
    defer_phase1_bodies: bool = False,
) -> tuple[ParsedModule, list[str]] | None:
    """Recover complete target declarations from a timed-out call's output.

    Timeouts are the largest single category of wasted model time, and the
    output is usually not empty — the backend had already streamed part or all
    of the file when the watchdog killed it. Anything syntactically complete
    for a target label is worth keeping; the caller still puts it through every
    normal gate, so a bad salvage costs a Lean check, not correctness.
    """
    if not partial_text or "```" not in partial_text:
        return None
    try:
        parsed = _ingest_model_lean(
            ctx,
            labels,
            partial_text,
            realize_contracts=realize_contracts,
            defer_phase1_bodies=defer_phase1_bodies,
        ).parsed
    except (ValueError, Exception):
        return None
    delivered_names = {decl.name for decl in parsed.decls if decl.name}
    delivered = [label for label in labels if _lean_name(label) in delivered_names]
    if not delivered:
        return None
    return parsed, delivered


def _freeze_section_from_code(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    decl_texts: list[str],
    imports: list[str],
    preamble: list[str],
    *,
    origin: str = "delivered code",
    allow_patch: bool = False,
    initial_only: bool = False,
    generation_tier: str = "delivered",
    failure_evidence: list[str] | None = None,
    failure_identities: list[dict[str, Any]] | None = None,
    failure_candidate_code: list[str] | None = None,
    route_plan_defects: bool = False,
    complete_bodies: bool = False,
    lean_timeout: int = CANDIDATE_LEAN_CHECK_TIMEOUT,
    defer_object_gate: bool = False,
) -> list[Section] | None:
    """Try to freeze one section from declarations the model already delivered
    (a design-pass chunk, or the healthy remainder beside a refusal/compile
    isolation). Same gates as fresh code — deterministic checks, Lean,
    alignment audit, .olean.

    With ``allow_patch`` the section gets the same single targeted patch the
    normal path gets before being abandoned; without it, any failure returns
    None and the caller regenerates. Discarding a whole delivered file because
    one declaration needs a fix is exactly the rollback-at-95% waste this
    pipeline avoids elsewhere, so callers whose delivered code IS the product
    (the design pass) pass allow_patch=True.
    Raises RepairRequest when the audit blames the blueprint."""
    import_modules = _sections_for_deps(ctx, labels, sections)
    target_kinds = _phase1_target_kinds(ctx, labels)
    label_by_lean_name = {_lean_name(label): label for label in labels}
    next_number = alloc()
    module, path = _section_module(ctx.name, next_number)
    path.parent.mkdir(parents=True, exist_ok=True)
    section_kind = (
        "Phase 2 complete-node candidate"
        if complete_bodies
        else "Initial declaration section"
        if initial_only
        else "Skeleton section"
    )
    _log(
        f"==> {section_kind} {next_number:02d}: {len(labels)} node(s) from "
        f"{origin}: " + ", ".join(labels[:6]) + ("..." if len(labels) > 6 else "")
    )
    missing_imports = _missing_olean_imports(imports)
    if missing_imports:
        ctx.unavailable_imports.update(missing_imports)
        imports = [item for item in imports if item not in set(missing_imports)]
    all_imports = [f"import {m}" for m in import_modules] + imports
    module_code, _ranges = _compose_module(all_imports, preamble, decl_texts)
    parsed = _parse_module(module_code)
    helper_owner_by_name = _planned_helper_owner_by_name(ctx, labels)
    if complete_bodies:
        # Phase 2 may atomically replace a pathological anonymous public
        # representation by a same-node structure/class/inductive.  In that
        # transaction the helper is intentionally newer than the Phase-1 plan,
        # so infer its owner from the canonical declaration group. Executable
        # helpers remain forbidden by the ordinary skeleton audit below.
        inferred = _declaration_owner_map(
            parsed, label_by_lean_name, helper_owner_by_name
        )
        for index, decl in enumerate(parsed.decls):
            if (
                decl.name
                and decl.name not in label_by_lean_name
                and decl.kind in {"structure", "class", "inductive"}
                and inferred.get(index) in set(labels)
            ):
                helper_owner_by_name.setdefault(
                    decl.name, inferred[index]
                )
    if not complete_bodies:
        for decl in parsed.decls:
            if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                decl.text = _normalize_terminal_sorry(decl.text)
    module_code, _ranges = _compose_module(
        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
    )
    sessions: dict[str, str] = {}
    # The initial pass exists only to establish a compilable environment for
    # root-first Phase 1.  Coverage and compilation are required here; exact
    # blueprint-contract alignment is deliberately deferred to Phase 1.
    findings = [] if initial_only else _skeleton_code_findings(
        module_code,
        target_kinds,
        label_by_lean_name,
        helper_owner_by_name,
        allow_deferred_bodies=not complete_bodies,
    )
    defer_alignment = bool(getattr(ctx, "defer_phase1_alignment", False))

    def check_candidate(candidate_path: Path) -> tuple[bool, str]:
        """Typecheck once and retain the object when the audit is deferred.

        The validated-contract pipeline used to elaborate the identical source
        here and again after semantic acceptance.  Emitting the object during
        this mandatory check lets the finalizer reuse it.  A later source edit
        or rejection removes the artifact through the existing section cleanup
        path, while the compile fingerprint prevents stale-object reuse.
        """
        if not defer_object_gate:
            return _check_lean(
                candidate_path, ctx.lean_command, timeout=lean_timeout
            )
        attempt = _compile_module_olean(
            candidate_path,
            ctx.lean_command,
            timeout=lean_timeout,
        )
        _record(
            ctx.telemetry,
            "lean_object_compilation",
            labels=labels,
            owner_phase="phase1",
            status="passed" if attempt.ok else getattr(attempt, "kind", "failed"),
            timeout_s=lean_timeout,
            duration_s=float(getattr(attempt, "duration_s", 0.0)),
            preaudit=True,
        )
        return attempt.ok, attempt.output
    if not initial_only:
        findings += _skeleton_deterministic_findings(module_code, ctx, labels)
    if findings and allow_patch:
        _log(
            f"  {origin} has {len(findings)} deterministic issue(s); patching in place"
        )
        patched, _note = _targeted_patch_skeleton_decls(
            ctx, labels, sections, import_modules, parsed, module_code, findings,
            timeout=ctx.base_timeout, sessions=sessions,
        )
        if patched is not None:
            parsed = patched
            if not complete_bodies:
                for decl in parsed.decls:
                    if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                        decl.text = _normalize_terminal_sorry(decl.text)
            module_code, _ranges = _compose_module(
                [f"import {module}" for module in import_modules]
                + list(parsed.imports),
                parsed.preamble,
                [decl.text for decl in parsed.decls],
            )
            findings = [] if initial_only else _skeleton_code_findings(
                module_code,
                target_kinds,
                label_by_lean_name,
                helper_owner_by_name,
                allow_deferred_bodies=not complete_bodies,
            )
            if not initial_only:
                findings += _skeleton_deterministic_findings(
                    module_code, ctx, labels
                )
    if findings:
        if failure_candidate_code is not None:
            failure_candidate_code.append(module_code)
        if failure_evidence is not None:
            failure_evidence.append(
                "Deterministic checks rejected delivered statements:\n"
                + _format_skeleton_findings(findings)
            )
        if failure_identities is not None:
            failure_identities.append(
                {
                    "source": "deterministic",
                    "obligations": sorted(
                        {
                            obligation
                            for finding in findings
                            for obligation in _finding_obligation_ids(finding)
                        }
                    ),
                }
            )
        _log(
            f"  delivered code failed deterministic checks ({len(findings)} "
            "issue(s)); regenerating the part"
        )
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="deterministic_rejected")
        _discard_section_artifacts(path)
        return None
    path.write_text(module_code, encoding="utf-8")
    ok, output = check_candidate(path)
    if not ok and not initial_only and not complete_bodies:
        interface_evidence = _phase1_interface_usability_evidence(output)
        if interface_evidence:
            # Phase 1 has already replaced every ordinary target body/proof by
            # `sorry` above. A timeout here is therefore an interface
            # elaboration failure, not a declaration-body compiler error.
            # Sending it through the local compiler patch loop paid for up to
            # three model calls that could not address the actual failure and
            # delayed the interface-usability router that owns this case.
            if failure_candidate_code is not None:
                failure_candidate_code.append(module_code)
            if failure_evidence is not None:
                failure_evidence.append(interface_evidence)
            if failure_identities is not None:
                failure_identities.append(
                    {
                        "source": "interface_usability",
                        "error_shape": _lean_error_shape(output),
                    }
                )
            _record(
                ctx.telemetry,
                "phase1_interface_usability_patch_bypassed",
                labels=labels,
                origin=origin,
                error_shape=_lean_error_shape(output),
            )
            _log(
                f"  {origin} exceeded Lean's Phase-1 interface budget; "
                "skipping body/compiler patches and routing the retained "
                "contract to interface correction"
            )
            _discard_section_artifacts(path)
            return None
    if not ok and _lean_failure_may_be_fixed_by_broad_mathlib(output):
        # Diagnose import/environment failures with the identical declarations
        # before paying a model to rewrite them. The broad environment is kept
        # only when it makes the unchanged candidate compile.
        original_output = output
        broad_imports = ["import Mathlib"] + [
            f"import {module}" for module in import_modules
        ] + list(parsed.imports)
        broad_code, broad_ranges = _compose_module(
            broad_imports,
            parsed.preamble,
            [decl.text for decl in parsed.decls],
        )
        path.write_text(broad_code, encoding="utf-8")
        broad_ok, broad_output = check_candidate(path)
        if broad_ok:
            specific_modules = _specific_import_modules_for_missing_names(
                ctx, original_output
            )
            specific_imports = [f"import {module}" for module in specific_modules]
            narrow_code = ""
            narrow_ranges: list[tuple[int, int]] = []
            narrow_ok = False
            narrow_output = ""
            if specific_imports:
                narrow_imports = [
                    f"import {module}" for module in import_modules
                ] + list(dict.fromkeys(list(parsed.imports) + specific_imports))
                narrow_code, narrow_ranges = _compose_module(
                    narrow_imports,
                    parsed.preamble,
                    [decl.text for decl in parsed.decls],
                )
                path.write_text(narrow_code, encoding="utf-8")
                narrow_ok, narrow_output = check_candidate(path)
            if narrow_ok:
                parsed.imports = list(
                    dict.fromkeys(list(parsed.imports) + specific_imports)
                )
                module_code, _ranges = narrow_code, narrow_ranges
                ok, output = True, narrow_output
                _record(
                    ctx.telemetry,
                    "phase1_environment_fallback",
                    labels=labels,
                    status="narrowed_without_model",
                    diagnosed_with="Mathlib",
                    added_imports=specific_modules,
                    missing_names=_missing_lean_surface_names(original_output),
                )
                _log(
                    f"  {origin} resolved missing Lean names with specific "
                    "module import(s): " + ", ".join(specific_modules)
                )
            else:
                path.write_text(broad_code, encoding="utf-8")
                # The failed narrow probe removed the broad candidate's object.
                # Recreate it only in this uncommon import-fallback branch.
                if defer_object_gate:
                    broad_ok, broad_output = check_candidate(path)
                if broad_ok:
                    parsed.imports = list(
                        dict.fromkeys(["import Mathlib"] + list(parsed.imports))
                    )
                    module_code, _ranges = broad_code, broad_ranges
                    ok, output = True, broad_output
                    _record(
                        ctx.telemetry,
                        "phase1_environment_fallback",
                        labels=labels,
                        status="resolved_without_model",
                        added_import="Mathlib",
                        attempted_specific_imports=specific_modules,
                    )
                    _log(
                        f"  {origin} compiled unchanged under the complete "
                        "Mathlib environment"
                    )
                else:
                    module_code, _ranges = _compose_module(
                        [f"import {module}" for module in import_modules]
                        + list(parsed.imports),
                        parsed.preamble,
                        [decl.text for decl in parsed.decls],
                    )
                    path.write_text(module_code, encoding="utf-8")
                    ok, output = False, broad_output
        else:
            path.write_text(module_code, encoding="utf-8")
            output = original_output

    if (
        not ok
        and allow_patch
        and route_plan_defects
        and not initial_only
        and _phase1_compile_plan_defects(ctx, labels, module_code, output)
    ):
        if failure_candidate_code is not None:
            failure_candidate_code.append(module_code)
        if failure_evidence is not None:
            failure_evidence.append(
                "Lean rejected a plan-realizing interface:\n" + output[-12000:]
            )
        if failure_identities is not None:
            failure_identities.append(
                {"source": "lean", "error_shape": _lean_error_shape(output)}
            )
        _record(
            ctx.telemetry,
            "phase1_compile_plan_defect_short_circuit",
            labels=labels,
            error_shape=_lean_error_shape(output),
        )
        _log(
            f"  {origin} copied a compiler-invalid accepted plan; "
            "skipping statement patches"
        )
        _discard_section_artifacts(path)
        return None

    if not ok and allow_patch:
        if not initial_only:
            _store_generation_candidates(
                ctx,
                labels,
                module_code,
                source=f"{origin}_compile_baseline",
                all_labels=labels,
                generation_tier=generation_tier,
                lean_status="failed",
                lean_output=output,
            )
        pending_findings: list[SkeletonFinding] = []
        for correction_round in range(1, COMPILER_CORRECTION_ROUNDS + 1):
            compile_findings = pending_findings or _lean_compile_findings(
                parsed,
                labels,
                _ranges,
                output,
                path.name,
                helper_owner_by_name,
            )
            pending_findings = []
            if not _patchable_skeleton_labels(compile_findings, labels):
                break
            _log(
                f"  {origin} failed Lean; correcting the isolated declaration(s) "
                f"inside the same transaction ({correction_round}/"
                f"{COMPILER_CORRECTION_ROUNDS})"
            )
            patched, _note = _targeted_patch_skeleton_decls(
                ctx,
                labels,
                sections,
                import_modules,
                parsed,
                module_code,
                compile_findings,
                timeout=ctx.base_timeout,
                sessions=sessions,
            )
            if patched is None:
                break
            parsed = patched
            if not complete_bodies:
                for decl in parsed.decls:
                    if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                        decl.text = _normalize_terminal_sorry(decl.text)
            current_imports = [
                f"import {module}" for module in import_modules
            ] + list(parsed.imports)
            module_code, _ranges = _compose_module(
                current_imports,
                parsed.preamble,
                [decl.text for decl in parsed.decls],
            )
            post = [] if initial_only else _skeleton_code_findings(
                module_code,
                target_kinds,
                label_by_lean_name,
                helper_owner_by_name,
                allow_deferred_bodies=not complete_bodies,
            )
            if not initial_only:
                post += _skeleton_deterministic_findings(
                    module_code, ctx, labels
                )
            if not initial_only and post:
                _store_generation_candidates(
                    ctx,
                    labels,
                    module_code,
                    source=f"{origin}_compiler_correction",
                    all_labels=labels,
                    generation_tier=generation_tier,
                    lean_status="unknown",
                )
                retained_code = _retained_generation_candidate_code(ctx, labels)
                if retained_code:
                    module_code = retained_code
                    parsed = _parse_module(module_code)
                    module_code, _ranges = _compose_module(
                        parsed.imports,
                        parsed.preamble,
                        [decl.text for decl in parsed.decls],
                    )
                    post = _skeleton_code_findings(
                        module_code,
                        target_kinds,
                        label_by_lean_name,
                        helper_owner_by_name,
                        allow_deferred_bodies=not complete_bodies,
                    )
                    post += _skeleton_deterministic_findings(
                        module_code, ctx, labels
                    )
            if post:
                pending_findings = post
                output = _format_skeleton_findings(post)
                continue
            path.write_text(module_code, encoding="utf-8")
            ok, output = check_candidate(path)
            if (
                not ok
                and route_plan_defects
                and _phase1_compile_plan_defects(
                    ctx, labels, module_code, output
                )
            ):
                _record(
                    ctx.telemetry,
                    "phase1_compile_plan_defect_short_circuit",
                    labels=labels,
                    error_shape=_lean_error_shape(output),
                    after_correction_round=correction_round,
                )
                _log(
                    f"  {origin} repeated a compiler failure while exactly "
                    "realizing its accepted plan; stopping statement patches"
                )
                break
            if not initial_only:
                _store_generation_candidates(
                    ctx,
                    labels,
                    module_code,
                    source=f"{origin}_compiler_check",
                    all_labels=labels,
                    generation_tier=generation_tier,
                    lean_status="passed" if ok else "failed",
                    lean_output=output,
                )
                # Keep compiling from this deterministic-clean intermediate
                # even when it has the same number of Lean errors as the best
                # candidate. The best remains the rollback point in persisted
                # state; rebasing here would repeat the old error forever.
            if ok:
                break
    if not ok:
        if failure_candidate_code is not None:
            failure_candidate_code.append(module_code)
        if failure_evidence is not None:
            failure_evidence.append("Lean rejected delivered statements:\n" + output[-12000:])
        if failure_identities is not None:
            failure_identities.append(
                {"source": "lean", "error_shape": _lean_error_shape(output)}
            )
        _log("  delivered code failed Lean; regenerating the part")
        _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="lean_rejected")
        _discard_section_artifacts(path)
        return None
    if not initial_only and not defer_alignment:
        audit = _model_alignment_audit(ctx, labels, module_code, tag="delivered")
        if audit is not None:
            kind, reason, rejected, helpers = audit
            if kind in {"blueprint", "decomposition"}:
                _discard_section_artifacts(path)
                raise RepairRequest(
                    reason,
                    sorted(rejected),
                    decomposition_helpers=helpers if kind == "decomposition" else None,
                    section_labels=labels,
                )
            _log("  delivered code rejected by alignment audit; regenerating the part")
            if failure_candidate_code is not None:
                failure_candidate_code.append(module_code)
            if failure_evidence is not None:
                failure_evidence.append(
                    "Statement alignment rejected delivered statements:\n"
                    + reason[-12000:]
                )
            if failure_identities is not None:
                identities = {
                    label: audit.failure_identity_for(label)
                    for label in rejected
                    if audit.failure_identity_for(label)
                }
                if identities:
                    failure_identities.append(
                        {"source": "statement_alignment", "labels": identities}
                    )
            _record(ctx.telemetry, "delivered_code_reuse", labels=labels, status="audit_rejected")
            _discard_section_artifacts(path)
            return None
    if not defer_object_gate:
        object_attempt, object_failure_class, object_evidence = (
            _compile_fast_candidate_object(
                ctx,
                path,
                module_code,
                labels,
                complete_bodies=complete_bodies,
            )
        )
        if not object_attempt.ok:
            if failure_candidate_code is not None:
                failure_candidate_code.append(module_code)
            if failure_evidence is not None:
                failure_evidence.append(object_evidence)
            if failure_identities is not None:
                failure_identities.append(
                    {
                        "source": "object_gate",
                        "failure_class": object_failure_class,
                        "error_shape": _lean_error_shape(object_evidence),
                    }
                )
            _record(
                ctx.telemetry,
                "delivered_code_reuse",
                labels=labels,
                status="olean_failed",
                failure_class=object_failure_class,
            )
            _discard_section_artifacts(path)
            return None
    state_word = (
        "provisioned"
        if initial_only
        else "verified whole node"
        if complete_bodies
        else "compiled candidate"
        if defer_alignment and not defer_object_gate
        else "typechecked candidate"
        if defer_object_gate
        else "frozen"
    )
    _log(
        f"  section {next_number:02d} {state_word} "
        f"({len(parsed.decls)} declaration(s)) from {origin}"
    )
    _record(
        ctx.telemetry,
        "phase2_whole_node_completed"
        if complete_bodies
        else "initial_declaration_section"
        if initial_only
        else "skeleton_section_candidate"
        if defer_alignment and not defer_object_gate
        else "skeleton_section_typechecked"
        if defer_object_gate
        else "skeleton_section_frozen",
        section=next_number,
        labels=labels,
        decls=len(parsed.decls),
        source="delivered",
    )
    if not initial_only and not defer_alignment and not defer_object_gate:
        if complete_bodies:
            _clear_retry_lifecycle(ctx, labels, stage="phase2_body")
            _clear_retry_lifecycle(ctx, labels, stage="phase2_whole_node")
        else:
            _note_frozen_section(ctx, labels)
    section = Section(
        number=next_number,
        labels=list(labels),
        path=path,
        module=module,
        import_modules=import_modules,
        refined_labels=(
            set()
            if initial_only or defer_alignment or defer_object_gate
            else None
        ),
        generation_tier=generation_tier,
    )
    if defer_object_gate and _section_objects_exist(section):
        _mark_section_compiled(section, ctx.lean_command, sections)
    elif not defer_object_gate:
        _mark_section_compiled(section, ctx.lean_command, sections)
    return [section]


def _parallel_initial_emission(
    ctx: Ctx,
    order: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
) -> tuple[list[Section], set[str]]:
    """Emit provisional chunks concurrently, then compile them in topo order.

    Stage zero needs names and compilable provisional signatures, not accepted
    contracts. Model emission is therefore independent enough to parallelize;
    installation remains dependency ordered so Lean sees providers first. A
    non-compiling delivered chunk gets one base-tier regeneration through the
    lightweight ``initial_only`` path. There is no semantic audit or escalation
    runner in this pass.
    """
    chunks = [
        order[start : start + BULK_SKELETON_CHUNK]
        for start in range(0, len(order), BULK_SKELETON_CHUNK)
    ]
    if not chunks:
        return [], set()

    _log(
        f"==> Initial declaration pass: emitting {len(chunks)} provisional "
        f"chunk(s) with {min(ctx.workers, len(chunks))} worker(s)"
    )

    def emit(chunk: list[str]) -> ParsedModule | None:
        imports = _sections_for_deps(ctx, chunk, sections)
        result = _call_model(
            ctx,
            _bulk_skeleton_prompt(
                ctx,
                chunk,
                sections,
                imports,
                timeout_s=ctx.base_timeout,
                initial_only=True,
            ),
            purpose="initial_declaration_generation",
            timeout=ctx.base_timeout,
            effort=ctx.base_effort,
            labels=chunk,
        )
        text = result.text
        if result.status == "timeout" and result.partial_text:
            text = result.partial_text
        if result.status not in {"ok", "timeout"} or not text.strip():
            return None
        try:
            return _ingest_model_lean(
                ctx,
                chunk,
                text,
                defer_phase1_bodies=True,
            ).parsed
        except ValueError:
            return None

    emitted: list[ParsedModule | None] = [None] * len(chunks)
    with concurrent.futures.ThreadPoolExecutor(
        max_workers=max(1, min(ctx.workers, len(chunks)))
    ) as pool:
        futures = {
            pool.submit(emit, chunk): index
            for index, chunk in enumerate(chunks)
        }
        for future in concurrent.futures.as_completed(futures):
            index = futures[future]
            emitted[index] = future.result()

    frozen: list[Section] = []
    covered: set[str] = set()
    for chunk, parsed in zip(chunks, emitted):
        combined = sections + frozen
        added: list[Section] | None = None
        if parsed is not None:
            delivered_names = {decl.name for decl in parsed.decls if decl.name}
            delivered_labels = [
                label for label in chunk if _lean_name(label) in delivered_names
            ]
            decl_texts = _delivered_decl_texts(
                parsed,
                delivered_labels,
                {_lean_name(label) for label in order},
                _planned_helper_owner_by_name(ctx, order),
            )
            if set(delivered_labels) == set(chunk) and decl_texts is not None:
                added = _freeze_section_from_code(
                    ctx,
                    delivered_labels,
                    combined,
                    alloc,
                    decl_texts,
                    list(parsed.imports),
                    list(parsed.preamble),
                    origin="parallel initial emission",
                    allow_patch=False,
                    initial_only=True,
                )

        if added is None:
            # One bounded base-tier regeneration is enough for scaffolding.
            # Failure propagates as generation/compiler evidence; the main loop
            # can retry it within the configured budget without editing TeX.
            added = _freeze_section(
                ctx,
                chunk,
                combined,
                alloc,
                initial_only=True,
            )

        frozen.extend(added)
        covered.update(label for sec in added for label in sec.labels)
        _save_ctx_state(ctx, sections + frozen)

    _record(
        ctx.telemetry,
        "initial_declaration_parallel_emission",
        chunks=len(chunks),
        workers=min(ctx.workers, len(chunks)),
        requested=len(order),
        provisioned=len(covered),
    )
    return frozen, covered


def _bulk_skeleton_pass(
    ctx: Ctx,
    order: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    initial_only: bool = False,
) -> tuple[list[Section], set[str]]:
    """One cheap design pass that states the whole pending graph at once.

    Returns ``(frozen_sections, covered_labels)``. Every declaration still
    goes through the normal gates (deterministic checks, Lean, alignment
    audit, .olean) via ``_freeze_section_from_code``; whatever the pass fails
    to deliver or freeze is simply left to the per-section loop, so the worst
    case is the previous behaviour plus one call.
    """
    if len(order) < BULK_SKELETON_MIN_NODES:
        return [], set()
    # Initial declarations are boilerplate only. Any Phase-1 bulk caller uses
    # the same shared planner as the normal top-down and bottom-up paths.
    if not initial_only:
        _ensure_phase1_semantic_plan(ctx, set(order))
    # Stage 2: transcribe the plan in section-sized chunks.
    if initial_only and ctx.workers > 1:
        return _parallel_initial_emission(ctx, order, sections, alloc)

    frozen: list[Section] = []
    covered: set[str] = set()
    for start in range(0, len(order), BULK_SKELETON_CHUNK):
        chunk = order[start : start + BULK_SKELETON_CHUNK]
        # Do not resume across independent emission chunks. Resume is useful
        # for local repair/patch calls, but here it caused Codex to repeat
        # earlier chunk declarations; those contain skeleton `sorry`s and are
        # correctly rejected as non-target helper declarations.
        chunk_sessions: dict[str, str] = {}
        pass_name = "Initial declaration pass" if initial_only else "Skeleton design pass"
        _log(
            f"==> {pass_name}: stating {len(chunk)} node(s) in one call "
            f"({len(order) - start - len(chunk)} node(s) after this chunk)"
        )
        prompt = _bulk_skeleton_prompt(
            ctx,
            chunk,
            sections + frozen,
            import_modules,
            timeout_s=ctx.base_timeout,
            initial_only=initial_only,
        )
        result = _call_model(
            ctx,
            prompt,
            purpose=(
                "initial_declaration_generation"
                if initial_only
                else "skeleton_design_pass"
            ),
            timeout=ctx.base_timeout,
            effort=ctx.base_effort,
            labels=chunk,
            sessions=chunk_sessions,
        )
        if result.status == "timeout":
            # Same ladder the section loop gets: one retry at the hard budget,
            # resuming the timed-out session so its work is not re-paid.
            _log(
                f"  design pass timed out at {ctx.base_timeout}s; retrying once at "
                f"{ctx.hard_timeout}s"
            )
            result = _call_model(
                ctx,
                prompt,
                purpose=(
                    "initial_declaration_generation"
                    if initial_only
                    else "skeleton_design_pass"
                ),
                timeout=ctx.hard_timeout,
                effort=ctx.base_effort,
                labels=chunk,
                sessions=chunk_sessions,
            )
        if result.status != "ok":
            _log(f"  design pass {result.status}; falling back to per-section generation")
            break
        if _parse_decomposition_refusal(
            result.text, expected_labels=chunk
        ) is not None:
            _log("  design pass returned a decomposition refusal; leaving it to the section loop")
            break
        try:
            parsed = _ingest_model_lean(
                ctx,
                chunk,
                result.text,
                realize_contracts=not initial_only,
                defer_phase1_bodies=True,
            ).parsed
        except ValueError:
            _log("  design pass returned no Lean code; falling back")
            break
        delivered_names = {decl.name for decl in parsed.decls if decl.name}
        delivered_labels = [
            label for label in chunk if _lean_name(label) in delivered_names
        ]
        chunk_decl_texts = _delivered_decl_texts(
            parsed,
            delivered_labels,
            {_lean_name(label) for label, node in ctx.nodes.items() if not node.mathlibok},
            _planned_helper_owner_by_name(
                ctx,
                [label for label, node in ctx.nodes.items() if not node.mathlibok],
            ),
        )
        _log(
            f"  design pass delivered {len(delivered_labels)}/{len(chunk)} target "
            f"declaration(s); verifying them section by section"
        )
        if not delivered_labels or chunk_decl_texts is None:
            break
        # Freeze the chunk as ONE section. The model authored it as a single
        # coherent file, so splitting it strands shared helper declarations in
        # whichever part happened to precede them and breaks cross-part
        # references — the chunk is already section-sized by construction.
        added = _freeze_section_from_code(
            ctx,
            delivered_labels,
            sections + frozen,
            alloc,
            chunk_decl_texts,
            list(parsed.imports),
            list(parsed.preamble),
            origin="initial pass" if initial_only else "design pass",
            # Initial-pass compiler feedback belongs in the lightweight
            # provisional prompt, not the exact-contract patch prompt.
            allow_patch=not initial_only,
            initial_only=initial_only,
        )
        if added is not None:
            frozen.extend(added)
            covered.update(delivered_labels)
            _save_ctx_state(ctx, sections + frozen)
        elif initial_only:
            # A failed broad declaration chunk is evidence that the optimistic
            # sweep is not producing reusable work for this blueprint.  Do not
            # pay for every remaining broad chunk and then regenerate all of
            # them in the compiler-feedback loop, as that duplicates the whole
            # initial pass.  Fall through immediately with smaller groups.
            old_size = ctx.effective_section_size or ctx.section_size
            new_size = max(1, min(old_size, max(1, len(chunk) // 2)))
            ctx.effective_section_size = new_size
            ctx.section_clean_streak = 0
            _log(
                "  initial broad declaration chunk did not compile; "
                f"ending the broad sweep and using {new_size}-node "
                "compiler-feedback groups"
            )
            _record(
                ctx.telemetry,
                "adaptive_section_size",
                previous_size=old_size,
                size=new_size,
                reason="initial_broad_chunk_rejected",
                labels=delivered_labels or chunk,
                pipeline_stage="initial_declaration",
            )
            break
    if frozen:
        _record(
            ctx.telemetry,
            "initial_declaration_pass" if initial_only else "skeleton_design_pass",
            requested=len(order),
            frozen_labels=sorted(covered),
            frozen_count=len(covered),
            sections=len(frozen),
        )
        _log(
            f"  {'initial pass provisioned' if initial_only else 'design pass froze'} "
            f"{len(covered)}/{len(order)} node(s) in "
            f"{len(frozen)} section(s); the rest continue through the normal loop"
        )
    return frozen, covered


def _freeze_parts(
    ctx: Ctx,
    parts: list[list[str]],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    delivered: ParsedModule | None = None,
    delivered_exclude: set[str] | None = None,
    initial_only: bool = False,
) -> list[Section]:
    """Freeze ordered subgroups and carry partial success through repairs.

    ``delivered`` carries declarations the model already produced in the call
    that triggered this split; parts fully covered by them (and not in
    ``delivered_exclude``, e.g. the refused or compile-failing labels) try a
    no-generation freeze first and fall back to normal generation."""
    frozen: list[Section] = []
    combined = list(sections)
    exclude = delivered_exclude or set()
    all_target_names = {_lean_name(label) for part in parts for label in part}
    if exclude:
        # A refused/failing part usually ends in RepairRequest, which aborts
        # the remaining parts. Freeze every part that does not depend on the
        # excluded labels first (relative order preserved), so delivered work
        # lands before the refusal bubbles up to repair.
        def _depends_on_excluded(part: list[str]) -> bool:
            return any(
                label in exclude or exclude & _transitive_dependencies(ctx.nodes, label)
                for label in part
            )

        independent = [part for part in parts if not _depends_on_excluded(part)]
        dependent = [part for part in parts if _depends_on_excluded(part)]
        parts = independent + dependent

    # A bottom-up Phase-1 layer contains no dependencies between its members.
    # When one broad response is routed into independent fragments, process
    # those fragments concurrently instead of serializing the exact workload
    # that routing was meant to isolate. Candidates remain unaudited here; the
    # caller's single layer gate performs the semantic judgment afterwards.
    active_parts = [part for part in parts if part]
    if (
        getattr(ctx, "defer_phase1_alignment", False)
        and len(active_parts) > 1
    ):
        all_names = {_lean_name(label) for part in active_parts for label in part}

        def freeze_candidate(part: list[str]) -> list[Section]:
            added: list[Section] | None = None
            if delivered is not None and not (set(part) & exclude):
                decl_texts = _delivered_decl_texts(
                    delivered,
                    part,
                    all_names,
                    _planned_helper_owner_by_name(
                        ctx, [label for item in active_parts for label in item]
                    ),
                )
                if decl_texts:
                    added = _freeze_section_from_code(
                        ctx,
                        part,
                        sections,
                        alloc,
                        decl_texts,
                        list(delivered.imports),
                        list(delivered.preamble),
                        initial_only=initial_only,
                    )
            if added is None:
                added = _freeze_section(
                    ctx,
                    part,
                    sections,
                    alloc,
                    initial_only=initial_only,
                )
            return added

        worker_count = max(
            1,
            min(
                getattr(ctx, "workers", 1),
                len(active_parts),
            ),
        )
        _log(
            f"  routing {len(active_parts)} independent Phase-1 fragment(s) "
            f"across {worker_count} worker(s)"
        )
        _record(
            ctx.telemetry,
            "phase1_fragments_parallel",
            part_labels=active_parts,
            part_sizes=[len(part) for part in active_parts],
            workers=worker_count,
        )
        results: list[list[Section] | None] = [None] * len(active_parts)
        failures: list[tuple[int, RepairRequest]] = []
        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
            futures = {
                pool.submit(freeze_candidate, part): index
                for index, part in enumerate(active_parts)
            }
            for future in concurrent.futures.as_completed(futures):
                index = futures[future]
                try:
                    results[index] = future.result()
                except RepairRequest as request:
                    failures.append((index, request))
        for result in results:
            if result:
                frozen.extend(result)
        for _index, request in failures:
            frozen.extend(request.frozen_sections)
            request.frozen_sections = []
        if failures:
            failures.sort(key=lambda item: item[0])
            request = failures[0][1]
            request.frozen_sections = frozen
            raise request
        return frozen

    try:
        for part in parts:
            if not part:
                continue
            added: list[Section] | None = None
            if delivered is not None and not (set(part) & exclude):
                decl_texts = _delivered_decl_texts(
                    delivered,
                    part,
                    all_target_names,
                    _planned_helper_owner_by_name(
                        ctx,
                        [label for item in active_parts for label in item],
                    ),
                )
                if decl_texts:
                    added = _freeze_section_from_code(
                        ctx,
                        part,
                        combined,
                        alloc,
                        decl_texts,
                        list(delivered.imports),
                        list(delivered.preamble),
                        initial_only=initial_only,
                    )
            if added is None:
                added = _freeze_section(
                    ctx,
                    part,
                    combined,
                    alloc,
                    initial_only=initial_only,
                )
            frozen.extend(added)
            combined.extend(added)
            # Persist each frozen part (and any scheduler change it caused):
            # a later part can raise RepairRequest or the process can die, and
            # unsaved frozen parts were being pruned as stale artifacts on the
            # next --continue.
            if not getattr(ctx, "defer_phase1_alignment", False):
                _save_ctx_state(ctx, combined)
    except RepairRequest as request:
        request.frozen_sections = frozen + request.frozen_sections
        raise
    return frozen


def _note_frozen_section(ctx: Ctx, labels: list[str]) -> None:
    """Advance the persistent capacity controller after an accepted section."""
    if ctx.effective_section_size <= 0:
        ctx.effective_section_size = ctx.section_size
    old_size = ctx.effective_section_size
    _release_quarantine(ctx, labels)
    _release_local_group_partitions(ctx, labels)
    _clear_generation_feedback(ctx, labels)
    _clear_generation_candidates(ctx, labels)
    _clear_retry_lifecycle(ctx, labels, stage="phase1_statement")
    _invalidate_blueprint_direct_descendants_after_freeze(ctx, labels)
    for label in labels:
        entry = getattr(ctx, "design_plan_entries", {}).get(label) or {}
        wave_id = str(entry.pop("closure_wave_id", ""))
        if wave_id:
            _record(
                ctx.telemetry,
                "phase1_design_plan_closure_outcome",
                labels=[label],
                wave_id=wave_id,
                outcome="statement_frozen",
                statement_fp=ctx.stmt_fps.get(label, ""),
                plan_fp=_design_plan_audit_fingerprint(ctx, label),
            )
    # A routed singleton or short tail proves only that those declarations are
    # acceptable; it is not evidence that the current broad batch capacity is
    # safe. Count clean capacity evidence only when a full-sized group freezes.
    if len(labels) < old_size:
        return
    ctx.proven_section_size = max(ctx.proven_section_size, len(labels))
    ctx.section_clean_streak += 1
    if ctx.section_clean_streak < 2 or old_size >= ctx.section_size:
        return
    # Two clean groups at the current capacity are enough to probe upward.
    # This still recovers exponentially, but an isolated easy declaration can
    # no longer jump the scheduler from 6 straight back to 12.
    new_size = min(ctx.section_size, max(old_size + 1, old_size * 2))
    ctx.effective_section_size = new_size
    ctx.section_clean_streak = 0
    _log(f"  adaptive section size increased to {new_size} after accepted section(s)")
    _record(
        ctx.telemetry,
        "adaptive_section_size",
        previous_size=old_size,
        size=new_size,
        reason="clean_full_sections",
        labels=labels,
    )


def _next_phase1_group(
    order: list[str],
    index: int,
    size: int,
    quarantined: set[str],
    local_partitions: dict[str, dict[str, Any]] | None = None,
) -> list[str]:
    """Choose one group without remixing known-problematic local scopes."""
    if index >= len(order):
        return []
    if order[index] in quarantined:
        return [order[index]]
    local_partitions = local_partitions or {}
    local = local_partitions.get(order[index])
    if local:
        members = set(local.get("group") or [order[index]])
        group: list[str] = []
        for label in order[index:]:
            if label not in members:
                break
            group.append(label)
        return group or [order[index]]

    protected = set(local_partitions)
    group: list[str] = []
    for label in order[index : index + size]:
        if label in quarantined or label in protected:
            break
        group.append(label)
    return group or [order[index]]


def _candidate_component_labels(ctx: Ctx, label: str, available: set[str]) -> list[str]:
    """Return a persisted shared-helper component valid for this frontier."""
    with _STATE_LOCK:
        stored = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
    entry = stored.get(label) or {}
    declared_component = set(entry.get("component_labels") or [label])
    code = str(entry.get("code") or "")
    component = [
        item
        for item in entry.get("component_labels") or [label]
        if item in available
        and getattr(ctx, "stmt_fps", {}).get(item)
        == str((stored.get(item) or {}).get("statement_fp") or "")
        and set((stored.get(item) or {}).get("component_labels") or [item])
        == declared_component
        and str((stored.get(item) or {}).get("code") or "") == code
    ]
    expected = declared_component & available
    if set(component) != expected or label not in component:
        return [label]
    return component


def _coalesce_candidate_components(ctx: Ctx, labels: list[str]) -> list[str]:
    """Place persisted atomic components contiguously without changing a layer."""
    available = set(labels)
    emitted: set[str] = set()
    ordered: list[str] = []
    for label in labels:
        if label in emitted:
            continue
        component = set(_candidate_component_labels(ctx, label, available))
        for item in labels:
            if item in component and item not in emitted:
                ordered.append(item)
                emitted.add(item)
    return ordered


def _freeze_section(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    force_first_escalated: bool = False,
    initial_only: bool = False,
) -> list[Section]:
    """Generate, compile-fix, audit, and freeze one section (possibly bisected).

    Bounded transaction per statement version: attempt 1 (base tier) and, only
    when a stage reports a fixable failure, attempt 2 (escalated tier). Each
    attempt is generate -> deterministic checks (one targeted patch) -> Lean
    compile (one targeted patch) -> alignment audit (one escalated targeted
    correction + one re-audit). Anything the second attempt cannot land raises
    RepairRequest; the timeout ladder (retry at hard budget, bisect, escalate)
    and failing-subset isolation are unchanged.

    Returns the newly frozen Section objects (appended by the caller). Raises
    RepairRequest when the blueprint itself must change first.
    """
    import_modules = _sections_for_deps(ctx, labels, sections)
    target_kinds = _phase1_target_kinds(ctx, labels)
    label_by_lean_name = {_lean_name(label): label for label in labels}
    next_number = alloc()
    module, path = _section_module(ctx.name, next_number)
    path.parent.mkdir(parents=True, exist_ok=True)
    section_kind = "Initial declaration section" if initial_only else "Skeleton section"
    _log(
        f"==> {section_kind} {next_number:02d}: {len(labels)} node(s): "
        + ", ".join(labels[:6])
        + ("..." if len(labels) > 6 else "")
    )

    froze = False
    try:
        # One backend session per runner spec for this section's whole lifecycle
        # (generation, patches, error-fix rounds, audit): follow-up calls keep the
        # Mathlib exploration and module context instead of rebuilding it cold.
        sessions: dict[str, str] = {}
        feedback = _generation_feedback_for(ctx, labels)
        previous_code = (
            "" if initial_only else _generation_candidates_for(ctx, labels)
        )
        escalated_refusals: set[str] = set()
        force_escalated_round = force_first_escalated and not initial_only
        completed_exchanges: set[tuple[str, str, str]] = set()
        invalid_mathlib_refusal_count = 0
        attempt_limit = (
            1
            if initial_only or force_first_escalated
            else SKELETON_GENERATION_ATTEMPTS
        )
        for attempt in range(1, attempt_limit + 1):
            use_escalated_runner = (
                not initial_only and (force_escalated_round or attempt > 1)
            )
            force_escalated_round = False
            effort = ctx.escalation_effort if use_escalated_runner else ctx.base_effort
            timeout = ctx.hard_timeout if use_escalated_runner else ctx.base_timeout
            try:
                prompt = _skeleton_prompt(
                    ctx,
                    labels,
                    sections,
                    import_modules,
                    feedback=feedback,
                    previous_code=previous_code,
                    timeout_s=timeout,
                    initial_only=initial_only,
                )
            except ValueError as exc:
                raise RepairRequest(
                    "Model context could not be made complete deterministically: "
                    + str(exc),
                    labels,
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                ) from exc
            purpose = (
                "initial_declaration_generation"
                if initial_only
                else "skeleton_generation"
            )
            result_tier = "escalation" if use_escalated_runner else "base"
            exchange_key = _phase1_exchange_start(
                ctx,
                labels,
                prompt=prompt,
                candidate_code=previous_code,
                purpose=purpose,
                tier=result_tier,
            )
            if not exchange_key:
                evidence = (
                    "The persisted three-sample allowance is exhausted for "
                    "this exact statement, plan, model, candidate, and prompt. "
                    "No additional model call was launched."
                )
                if feedback:
                    evidence += "\n\nRetained correction evidence:\n" + feedback[-10000:]
                _record(
                    ctx.telemetry,
                    "phase1_exchange_sample_limit",
                    purpose=purpose,
                    labels=labels,
                    tier=result_tier,
                    limit=PHASE1_EXCHANGE_SAMPLE_LIMIT,
                )
                route = _route_lean_generation_failure(labels)
                raise RepairRequest(
                    evidence,
                    list(route.failed_labels),
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                    failure_route=route,
                    retry_attempted_tier=result_tier,
                    evidence_by_label={label: evidence for label in labels},
                )
            result = _call_model(
                ctx,
                prompt,
                purpose=purpose,
                timeout=timeout,
                effort=effort,
                labels=labels,
                escalated=use_escalated_runner,
                sessions=sessions,
            )
            duplicate_persisted_exchange = _phase1_exchange_finish(
                ctx,
                exchange_key,
                status=result.status,
                response_text=result.text,
            )
            result_was_escalated = use_escalated_runner
            if result.status == "timeout":
                # A timed-out request is NEVER re-issued unchanged at a larger
                # budget: that pattern cost 300s + 600s before any subdivision,
                # and timeouts are the largest category of wasted model time.
                # Instead: keep whatever the backend already emitted, then split.
                salvage = _salvage_timeout_declarations(
                    ctx,
                    labels,
                    result.partial_text,
                    realize_contracts=not initial_only,
                    defer_phase1_bodies=True,
                )
                if salvage is not None:
                    parsed_partial, delivered = salvage
                    _log(
                        f"  call timed out but had already emitted "
                        f"{len(delivered)}/{len(labels)} target declaration(s); "
                        "verifying the salvage instead of discarding the call"
                    )
                    _record(
                        ctx.telemetry,
                        "timeout_salvage",
                        labels=labels,
                        salvaged_labels=delivered,
                        salvaged_count=len(delivered),
                    )
                    added = _freeze_section_from_code(
                        ctx,
                        delivered,
                        sections,
                        alloc,
                        [decl.text for decl in parsed_partial.decls],
                        list(parsed_partial.imports),
                        list(parsed_partial.preamble),
                        origin="timeout salvage",
                        allow_patch=not initial_only,
                        initial_only=initial_only,
                        generation_tier=(
                            "escalation" if result_was_escalated else "base"
                        ),
                    )
                    if added:
                        # NOTE: deliberately do not set `froze` — the salvage
                        # allocated its own section number, so this attempt's
                        # `path` is still an orphan and must be discarded by
                        # the finally.
                        remaining = [
                            label for label in labels if label not in set(delivered)
                        ]
                        if not remaining:
                            return added
                        try:
                            rest = _freeze_section(
                                ctx,
                                remaining,
                                sections + added,
                                alloc,
                                initial_only=initial_only,
                            )
                        except RepairRequest as request:
                            request.frozen_sections = added + request.frozen_sections
                            raise
                        return added + rest
                # Nothing salvageable: subdivide rather than re-ask the same
                # question with a bigger stopwatch.
                if len(labels) > 1:
                    route = _route_lean_generation_failure(labels)
                    parts = [list(part) for part in route.parts]
                    mid = len(parts[0])
                    _log(
                        "  section call timed out; shared failure router is "
                        f"bisecting into {len(parts[0])} + {len(parts[1])} node(s)"
                    )
                    # This size demonstrably does not fit the base timeout, so
                    # don't make future groups rediscover that: shrink the
                    # run-scoped section size (Phase 2 already does this for
                    # proof batches).
                    if 0 < mid < (ctx.effective_section_size or ctx.section_size):
                        ctx.effective_section_size = mid
                        ctx.section_clean_streak = 0
                        _log(f"  adaptive section size reduced to {mid} for the rest of this run")
                        _record(
                            ctx.telemetry,
                            "adaptive_section_size",
                            size=mid,
                            reason=(
                                "initial_declaration_timeout"
                                if initial_only
                                else "skeleton_timeout"
                            ),
                            pipeline_stage=(
                                "initial_declaration" if initial_only else "phase1"
                            ),
                            labels=labels,
                        )
                        _save_ctx_state(ctx, sections)
                    return _freeze_parts(
                        ctx,
                        parts,
                        sections,
                        alloc,
                        initial_only=initial_only,
                    )
                if initial_only:
                    raise RepairRequest(
                        "Initial declaration generation timed out for this node. "
                        "Stage zero does not escalate or refine statements; retry "
                        "the provisional declaration within the repair budget.",
                        labels,
                        section_labels=labels,
                    )
                result_tier = "escalation"
                exchange_key = _phase1_exchange_start(
                    ctx,
                    labels,
                    prompt=prompt,
                    candidate_code=previous_code,
                    purpose=purpose,
                    tier=result_tier,
                )
                if not exchange_key:
                    evidence = (
                        "The persisted three-sample escalation allowance is "
                        "exhausted for this exact statement, plan, model, "
                        "candidate, and prompt. No additional model call was "
                        "launched."
                    )
                    _record(
                        ctx.telemetry,
                        "phase1_exchange_sample_limit",
                        purpose=purpose,
                        labels=labels,
                        tier=result_tier,
                        limit=PHASE1_EXCHANGE_SAMPLE_LIMIT,
                    )
                    route = _route_lean_generation_failure(labels)
                    raise RepairRequest(
                        evidence,
                        list(route.failed_labels),
                        section_labels=labels,
                        authorizes_blueprint_repair=False,
                        failure_route=route,
                        retry_attempted_tier=result_tier,
                        evidence_by_label={label: evidence for label in labels},
                    )
                result = _call_model(
                    ctx,
                    prompt,
                    purpose=purpose,
                    timeout=ctx.hard_timeout,
                    effort=ctx.escalation_effort,
                    labels=labels,
                    escalated=True,
                    sessions=sessions,
                )
                duplicate_persisted_exchange = _phase1_exchange_finish(
                    ctx,
                    exchange_key,
                    status=result.status,
                    response_text=result.text,
                )
                result_was_escalated = True
                if result.status == "error":
                    feedback = f"model call failed: {result.error}"
                    continue
                if result.status == "timeout":
                    # Two full timeout budgets on a single-statement call is the one
                    # place a timeout counts as evidence: the node cannot even be
                    # *stated* within a generous budget.
                    raise RepairRequest(
                        "Statement generation for this node timed out twice, including at "
                        "escalated effort; the node is likely too large or underspecified "
                        "to state as one declaration. Decompose it into smaller nodes.",
                        labels,
                        section_labels=labels,
                    )
            elif result.status == "error":
                feedback = f"model call failed: {result.error}"
                if len(labels) > 1:
                    route = _route_lean_generation_failure(labels)
                    _record(
                        ctx.telemetry,
                        "lean_generation_failure_routed",
                        stage=(
                            "initial_declaration"
                            if initial_only
                            else "phase1_generation"
                        ),
                        action=route.action,
                        labels=labels,
                        failing_labels=list(route.failed_labels),
                        accepted_labels=list(route.accepted_labels),
                        part_sizes=[len(part) for part in route.parts],
                        model_status=result.status,
                    )
                    return _freeze_parts(
                        ctx,
                        [list(part) for part in route.parts],
                        sections,
                        alloc,
                        initial_only=initial_only,
                    )
                continue

            # A resumed CLI session can replay its previous final answer when it is
            # given the same correction prompt. The response is then guaranteed to
            # recreate the same candidate, so compiling and asking again only burns
            # another model call. Escalate once from a duplicate base exchange; a
            # duplicate escalation is genuine generation stagnation.
            exchange = (
                ctx.escalation_runner_spec if result_was_escalated else ctx.runner_spec,
                hashlib.sha256(prompt.encode("utf-8")).hexdigest(),
                hashlib.sha256(result.text.encode("utf-8")).hexdigest(),
            )
            if duplicate_persisted_exchange or exchange in completed_exchanges:
                _record(
                    ctx.telemetry,
                    "duplicate_model_exchange",
                    purpose=(
                        "initial_declaration_generation"
                        if initial_only
                        else "skeleton_generation"
                    ),
                    labels=labels,
                    escalated=result_was_escalated,
                    prompt_sha256=exchange[1],
                    response_sha256=exchange[2],
                )
                sessions.pop(exchange[0], None)
                if len(labels) > 1:
                    route = _route_lean_generation_failure(labels)
                    _record(
                        ctx.telemetry,
                        "lean_generation_failure_routed",
                        stage=(
                            "initial_declaration"
                            if initial_only
                            else "phase1_generation"
                        ),
                        action=route.action,
                        labels=labels,
                        failing_labels=list(route.failed_labels),
                        accepted_labels=list(route.accepted_labels),
                        part_sizes=[len(part) for part in route.parts],
                        model_status="duplicate_response",
                    )
                    return _freeze_parts(
                        ctx,
                        [list(part) for part in route.parts],
                        sections,
                        alloc,
                        initial_only=initial_only,
                    )
                if not result_was_escalated:
                    force_escalated_round = True
                    feedback = (
                        "The base generator replayed a byte-identical response to "
                        "the same compiler-feedback prompt. Start fresh at the "
                        "escalation tier and produce a materially corrected Lean "
                        "declaration."
                    )
                    _log(
                        "  duplicate skeleton response detected; skipping the "
                        "redundant compile and escalating once"
                    )
                    continue
                raise RepairRequest(
                    "Skeleton generation repeated a byte-identical response to the "
                    "same correction prompt at escalated effort. The current node "
                    "needs a different formal interface or explicit helper "
                    "decomposition; do not weaken its mathematical claim.",
                    labels,
                    section_labels=labels,
                )
            completed_exchanges.add(exchange)

            refusal = _parse_decomposition_refusal(
                result.text, expected_labels=labels
            )
            if refusal is not None:
                refused = [refusal["label"]]
                invalid_mappings = _invalid_mathlib_refusal_mappings(ctx, refusal)
                if invalid_mappings:
                    invalid_mathlib_refusal_count += 1
                    mapping_text = ", ".join(
                        f"`{generated}` is Mathlib-owned as `{actual}`"
                        for generated, actual in sorted(invalid_mappings.items())
                    )
                    _log(
                        "  rejected false Mathlib dependency refusal for "
                        + ", ".join(refused)
                        + f": {mapping_text}"
                    )
                    _record(
                        ctx.telemetry,
                        "skeleton_refusal_rejected",
                        labels=labels,
                        refused_labels=refused,
                        reason="mathlib_dependency_already_settled",
                        attempt=invalid_mathlib_refusal_count,
                        mappings=invalid_mappings,
                        refusal_reason=refusal.get("reason", ""),
                    )
                if len(labels) > 1 and len(refused) < len(labels):
                    # The response identified a node-specific problem. Isolate
                    # exactly that node while preserving dependency order; it says
                    # nothing about how many unrelated nodes fit in one call.
                    _quarantine_labels(ctx, refused, "model_refusal")
                    parts = _parts_around_labels(labels, refused)
                    _log(
                        "  skeleton generator isolated "
                        + ", ".join(refused)
                        + "; preserving global section size and routing "
                        + " + ".join(str(len(part)) for part in parts)
                        + " node(s)"
                    )
                    _record(
                        ctx.telemetry,
                        "skeleton_refusal_isolated",
                        labels=labels,
                        refused_labels=refused,
                        part_sizes=[len(part) for part in parts],
                        invalid_mathlib_refusal=bool(invalid_mappings),
                        missing_helpers=refusal.get("missing_helpers") or [],
                        refusal_reason=refusal.get("reason", ""),
                    )
                    delivered = None
                    if "```" in result.text:
                        delivered_code = _extract_lean_code(result.text)
                        if delivered_code.strip():
                            candidate = _ingest_model_lean(
                                ctx,
                                labels,
                                delivered_code,
                                defer_phase1_bodies=True,
                            ).parsed
                            if candidate.decls:
                                delivered = candidate
                                _log(
                                    f"  refusal reply also delivered {len(candidate.decls)} "
                                    "declaration(s); reusing them for the healthy parts"
                                )
                    return _freeze_parts(
                        ctx,
                        parts,
                        sections,
                        alloc,
                            delivered=delivered,
                            delivered_exclude=set(refused),
                            initial_only=initial_only,
                        )
                if invalid_mappings:
                    # A singleton refusal based on a nonexistent generated name is
                    # not blueprint-repair evidence. Correct it in-context and use
                    # the escalation runner once before normal fix rounds continue.
                    feedback = (
                        "Your NEEDS-DECOMPOSITION response was invalid because its "
                        "supposedly missing helpers are settled Mathlib dependencies: "
                        + mapping_text
                        + ". Use those exact external declarations and generate the "
                        "requested blueprint statement without changing its meaning."
                    )
                    previous_code = ""
                    if not result_was_escalated:
                        force_escalated_round = True
                    continue
                refusal_key = ",".join(refused)
                if not result_was_escalated and refusal_key not in escalated_refusals:
                    escalated_refusals.add(refusal_key)
                    force_escalated_round = True
                    missing = refusal.get("missing_helpers") or []
                    feedback = (
                        "The base skeleton generator returned NEEDS-DECOMPOSITION. "
                        "Treat that as a statement-generation claim, not blueprint "
                        "repair evidence yet. Before editing the blueprint, make an "
                        "escalated attempt to state the same blueprint node(s) inside "
                        "this section without adding executable helper declarations. "
                        "Do not add a separate mathematical result or "
                        "weaken the blueprint statement.\n\n"
                        f"Refused label(s): {', '.join(refused)}\n"
                        f"Reason: {refusal['reason']}\n"
                        f"Requested helper(s): {', '.join(missing) or '(none)'}"
                    )
                    previous_code = ""
                    _log(
                        "  skeleton generator requested decomposition for "
                        + ", ".join(refused)
                        + "; escalating statement generation before blueprint repair"
                    )
                    continue
                raise RepairRequest(
                    "The escalated statement generator determined node(s) cannot be "
                    "stated 1-1 as written.\n"
                    f"Reason: {refusal['reason']}",
                    refused,
                    decomposition_helpers=refusal["missing_helpers"],
                    section_labels=labels,
                )

            parsed = _ingest_model_lean(
                ctx,
                labels,
                result.text,
                realize_contracts=not initial_only,
                defer_phase1_bodies=True,
            ).parsed
            missing_imports = _missing_olean_imports(parsed.imports)
            if missing_imports:
                ctx.unavailable_imports.update(missing_imports)
                parsed.imports = [item for item in parsed.imports if item not in set(missing_imports)]
            # Normalize `:= by sorry` to the canonical terminal form.
            for decl in parsed.decls:
                if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                    decl.text = _normalize_terminal_sorry(decl.text)
            all_imports = [f"import {m}" for m in import_modules] + parsed.imports
            module_code, _ranges = _compose_module(all_imports, parsed.preamble, [d.text for d in parsed.decls])

            if initial_only:
                delivered_names = {
                    decl.name for decl in parsed.decls if decl.name
                }
                missing_labels = [
                    label
                    for label in labels
                    if _lean_name(label) not in delivered_names
                ]
                if missing_labels:
                    feedback = (
                        "The provisional file omitted required declaration(s): "
                        + ", ".join(
                            f"{label} -> `{_lean_name(label)}`"
                            for label in missing_labels
                        )
                        + ". Emit every requested name; bodies may use `by sorry`."
                    )
                    previous_code = module_code
                    if len(labels) > 1 and set(missing_labels) < set(labels):
                        _log(
                            "  initial declaration coverage isolated "
                            + ", ".join(missing_labels)
                            + "; preserving delivered declarations and routing "
                            "the missing subset separately"
                        )
                        return _freeze_parts(
                            ctx,
                            _parts_around_labels(labels, missing_labels),
                            sections,
                            alloc,
                            delivered=parsed,
                            delivered_exclude=set(missing_labels),
                            initial_only=True,
                        )
                    if attempt < attempt_limit:
                        continue
                    raise RepairRequest(
                        "Initial declaration generation repeatedly omitted a "
                        "required Lean name. This is generation evidence, not an "
                        "accepted statement: " + feedback,
                        missing_labels,
                        section_labels=labels,
                    )
                findings = []
            else:
                findings = _skeleton_code_findings(
                    module_code,
                    target_kinds,
                    label_by_lean_name,
                    _planned_helper_owner_by_name(ctx, labels),
                )
            if not initial_only:
                findings += _skeleton_deterministic_findings(
                    module_code, ctx, labels
                )
            patch_note = ""
            if findings:
                plan_revision_required = _findings_require_plan_revision(
                    ctx, findings
                )
                patched, patch_note = (None, "plan revision required")
                if plan_revision_required:
                    evidence = _format_skeleton_findings(findings)
                    plan_labels = (
                        _isolated_deterministic_failure_labels(findings, labels)
                        or labels
                    )
                    corrected = _correct_phase1_design_plan(
                        ctx, plan_labels, evidence, escalated=False
                    )
                    _record(
                        ctx.telemetry,
                        "phase1_outline_plan_closure_correction",
                        labels=plan_labels,
                        corrected=bool(corrected),
                        reason="deterministic_contract_closure",
                    )
                    if corrected:
                        raise RepairRequest(
                            "Phase 1 outline plan was not closed over its "
                            "generated declarations and was corrected; regenerate "
                            "only these statements under the closed plan.\n"
                            + evidence[-8000:],
                            plan_labels,
                            section_labels=plan_labels,
                            authorizes_blueprint_repair=False,
                        )
                else:
                    patched, patch_note = _targeted_patch_skeleton_decls(
                        ctx,
                        labels,
                        sections,
                        import_modules,
                        parsed,
                        module_code,
                        findings,
                        timeout=ctx.base_timeout,
                        sessions=sessions,
                    )
                if patched is not None:
                    parsed = patched
                    all_imports = [f"import {m}" for m in import_modules] + parsed.imports
                    module_code, _ranges = _compose_module(
                        all_imports, parsed.preamble, [d.text for d in parsed.decls]
                    )
                    findings = _skeleton_code_findings(
                        module_code,
                        target_kinds,
                        label_by_lean_name,
                        _planned_helper_owner_by_name(ctx, labels),
                    )
                    findings += _skeleton_deterministic_findings(module_code, ctx, labels)
            if findings:
                feedback = _format_skeleton_findings(findings)
                if patch_note and patch_note != "not patchable":
                    feedback += f"\n\nTargeted declaration patch result: {patch_note}"
                deterministic_failure_labels = _isolated_deterministic_failure_labels(
                    findings, labels
                )
                route = _route_lean_generation_failure(
                    labels,
                    deterministic_failure_labels
                    if deterministic_failure_labels
                    else None,
                )
                routed_labels = list(route.failed_labels)
                _store_generation_candidates(
                    ctx,
                    routed_labels,
                    module_code,
                    source="deterministic_audit",
                    all_labels=labels,
                    generation_tier=(
                        "escalation" if result_was_escalated else "base"
                    ),
                )
                previous_code = (
                    _generation_candidates_for(ctx, routed_labels) or module_code
                )
                if len(labels) > 1:
                    _store_generation_feedback(
                        ctx,
                        routed_labels,
                        feedback,
                        source="deterministic_audit",
                        evidence_by_label=_generation_evidence_from_findings(
                            routed_labels, findings
                        ),
                    )
                    if route.action == "isolate":
                        _quarantine_labels(
                            ctx, routed_labels, "deterministic_audit"
                        )
                    parts = [list(part) for part in route.parts]
                    retained = list(route.accepted_labels)
                    _log(
                        "  deterministic audit failure routed as "
                        + route.action
                        + " across "
                        + " + ".join(str(len(part)) for part in parts)
                        + " node(s)"
                    )
                    _record(
                        ctx.telemetry,
                        "skeleton_deterministic_routed",
                        labels=labels,
                        action=route.action,
                        failing_labels=routed_labels,
                        retained_labels=retained,
                        part_sizes=[len(part) for part in parts],
                        finding_classes=[
                            _skeleton_finding_class(finding.message)
                            for finding in findings
                        ],
                        statement_fps={
                            label: ctx.stmt_fps.get(label, "")
                            for label in labels
                        },
                    )
                    return _freeze_parts(
                        ctx,
                        parts,
                        sections,
                        alloc,
                        delivered=parsed,
                        delivered_exclude=(
                            set(routed_labels) if route.action == "isolate" else set()
                        ),
                        initial_only=initial_only,
                    )
                if attempt < attempt_limit:
                    _log(
                        f"  deterministic audit failed ({len(findings)} issue(s)) after "
                        "one targeted patch; regenerating once at escalated effort"
                    )
                    continue
                raise RepairRequest(
                    "Targeted skeleton declaration patch made no deterministic "
                    "progress on the same audit failures, including at escalated "
                    "effort.\n" + _format_skeleton_findings(findings)[-10000:],
                    _patchable_skeleton_labels(findings, labels) or labels,
                    section_labels=labels,
                )

            # Compile before paying for a semantic model audit. Most failed
            # candidates in long runs are ordinary Lean encoding errors; auditing
            # those files spends money without producing an acceptable artifact.
            # One targeted patch on the Lean-isolated declarations, then either the
            # failing subset is split out (one bad node must not drag its healthy
            # batchmates into repair) or this attempt is spent.
            path.write_text(module_code, encoding="utf-8")
            ok, output = _check_lean(path, ctx.lean_command)
            patch_labels: list[str] = []
            if not ok:
                compile_findings = _lean_compile_findings(
                    parsed,
                    labels,
                    _ranges,
                    output,
                    path.name,
                    _planned_helper_owner_by_name(ctx, labels),
                )
                patch_labels = _patchable_skeleton_labels(compile_findings, labels)
                if not patch_labels and len(labels) == 1:
                    # With one target declaration, any local compile error belongs
                    # to that declaration or its local helpers even when Lean's
                    # source range cannot be mapped precisely.
                    patch_labels = list(labels)
                patched = None
                patch_note = "not patchable"
                post_findings: list[SkeletonFinding] = []
                if patch_labels and not initial_only:
                    _log(
                        "  Lean isolated compile errors in "
                        + f"{len(patch_labels)} declaration(s); patching in place"
                    )
                    patched, patch_note = _targeted_patch_skeleton_decls(
                        ctx,
                        labels,
                        sections,
                        import_modules,
                        parsed,
                        module_code,
                        compile_findings,
                        timeout=ctx.base_timeout,
                        sessions=sessions,
                    )
                if patched is not None:
                    parsed = patched
                    for decl in parsed.decls:
                        if _may_defer_target_body(
                            decl, target_kinds.get(decl.name or "")
                        ):
                            decl.text = _normalize_terminal_sorry(decl.text)
                    all_imports = [f"import {m}" for m in import_modules] + parsed.imports
                    module_code, _ranges = _compose_module(
                        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
                    )
                    post_findings = [] if initial_only else _skeleton_code_findings(
                        module_code,
                        target_kinds,
                        label_by_lean_name,
                        _planned_helper_owner_by_name(ctx, labels),
                    )
                    if not initial_only:
                        post_findings += _skeleton_deterministic_findings(
                            module_code, ctx, labels
                        )
                    if not post_findings:
                        path.write_text(module_code, encoding="utf-8")
                        ok, output = _check_lean(path, ctx.lean_command)
                        if ok:
                            _record(
                                ctx.telemetry,
                                "skeleton_compile_patch",
                                section=next_number,
                                round=1,
                                labels=patch_labels,
                                status="applied",
                            )
                if not ok:
                    if patched is not None and post_findings:
                        feedback = (
                            "Targeted compile patch introduced deterministic issues:\n"
                            + _format_skeleton_findings(post_findings)
                        )
                    else:
                        feedback = f"Lean rejected the file:\n{output[-12000:]}"
                        if patch_note != "patched":
                            feedback += f"\n\nTargeted compile patch: {patch_note}"
                    attributable_compile_labels = []
                    if not any(finding.label is None for finding in compile_findings):
                        attributable_compile_labels = [
                            label
                            for label in labels
                            if any(finding.label == label for finding in compile_findings)
                        ]
                    route = _route_lean_generation_failure(
                        labels,
                        attributable_compile_labels
                        if attributable_compile_labels
                        else None,
                    )
                    failure_labels = route.failed_labels
                    _store_generation_candidates(
                        ctx,
                        failure_labels,
                        module_code,
                        source="lean_compile_failure",
                        all_labels=labels,
                        generation_tier=(
                            "escalation" if result_was_escalated else "base"
                        ),
                        lean_status="failed",
                        lean_output=output,
                    )
                    previous_code = (
                        _generation_candidates_for(ctx, failure_labels) or module_code
                    )
                    if len(labels) > 1:
                        if route.action == "isolate":
                            _quarantine_labels(
                                ctx, failure_labels, "lean_compile_failure"
                            )
                        _store_generation_feedback(
                            ctx,
                            failure_labels,
                            feedback,
                            source="lean_compile_failure",
                            evidence_by_label=_generation_evidence_from_findings(
                                failure_labels, compile_findings
                            ),
                        )
                        _record(
                            ctx.telemetry,
                            "lean_generation_failure_routed",
                            stage="phase1_compile",
                            action=route.action,
                            labels=labels,
                            failing_labels=list(failure_labels),
                            accepted_labels=list(route.accepted_labels),
                            part_sizes=[len(part) for part in route.parts],
                            lean_error_shape=_lean_error_shape(output),
                            escalated=result_was_escalated,
                        )
                        parts = [list(part) for part in route.parts]
                        _log(
                            "  Lean generation failure routed as "
                            + route.action
                            + "; validating reusable declarations and routing "
                            + " + ".join(str(len(part)) for part in parts)
                            + " node(s)"
                        )
                        return _freeze_parts(
                            ctx,
                            parts,
                            sections,
                            alloc,
                            delivered=parsed,
                            delivered_exclude=(
                                set(failure_labels)
                                if route.action == "isolate"
                                else set()
                            ),
                            initial_only=initial_only,
                        )
                    if attempt < attempt_limit:
                        # The prompt is self-contained; discard the anchored
                        # producer session and give the stronger tier one fresh
                        # attempt.
                        sessions.pop(
                            ctx.escalation_runner_spec
                            if result_was_escalated
                            else ctx.runner_spec,
                            None,
                        )
                        _record(
                            ctx.telemetry,
                            "singleton_compile_escalation",
                            labels=labels,
                            lean_error_shape=_lean_error_shape(output),
                            base_patch_rounds=1 if patch_labels else 0,
                        )
                        _log(
                            "  section still fails Lean after one targeted compile "
                            "patch; starting one fresh escalated attempt"
                        )
                        continue
                    raise RepairRequest(
                        "A statement still does not compile after one base "
                        "generation/patch and one fresh escalated generation/patch. "
                        "Further Lean variants are not useful; repair or decompose "
                        "the formal interface without weakening the blueprint "
                        "claim.\n" + feedback,
                        list(failure_labels),
                        section_labels=labels,
                    )

            # Alignment audit: one verdict, one escalated targeted correction, one
            # re-audit. A second rejection is blueprint evidence, not a reason to
            # generate more Lean variants.
            defer_alignment = bool(getattr(ctx, "defer_phase1_alignment", False))
            audit = None if initial_only or defer_alignment else _model_alignment_audit(
                ctx, labels, module_code
            )
            if audit is not None:
                audit = _coerce_alignment_audit_result(audit)
                plan_request = _audit_plan_revision_request(
                    ctx,
                    audit,
                    layer_no=-1,
                    source="section_alignment",
                )
                if plan_request is not None:
                    raise plan_request
                kind, reason, rejected, helpers = audit
                if kind in {"blueprint", "decomposition"}:
                    raise RepairRequest(
                        reason,
                        sorted(rejected),
                        decomposition_helpers=helpers if kind == "decomposition" else None,
                        section_labels=labels,
                    )
                route = _route_lean_generation_failure(labels, rejected)
                _store_generation_candidates(
                    ctx,
                    route.failed_labels,
                    module_code,
                    source="statement_alignment",
                    all_labels=labels,
                    generation_tier=(
                        "escalation" if result_was_escalated else "base"
                    ),
                    lean_status="passed",
                    semantic_status="rejected",
                    semantic_evidence=reason,
                )
                _record(
                    ctx.telemetry,
                    "lean_generation_failure_routed",
                    stage="phase1_alignment",
                    action=route.action,
                    labels=labels,
                    failing_labels=list(route.failed_labels),
                    accepted_labels=list(route.accepted_labels),
                    part_sizes=[len(part) for part in route.parts],
                )
                if len(labels) > 1:
                    _store_generation_feedback(
                        ctx,
                        route.failed_labels,
                        reason,
                        source="statement_alignment",
                        evidence_by_label={
                            label: audit.reason_for([label])
                            for label in route.failed_labels
                        },
                        evidence_identity_by_label={
                            label: audit.failure_identity_for(label)
                            for label in route.failed_labels
                        },
                    )
                    if route.action == "isolate":
                        _quarantine_labels(
                            ctx, route.failed_labels, "statement_alignment"
                        )
                    parts = [list(part) for part in route.parts]
                    _log(
                        "  statement-alignment failure routed as "
                        + route.action
                        + " across "
                        + " + ".join(str(len(part)) for part in parts)
                        + " node(s)"
                    )
                    return _freeze_parts(
                        ctx,
                        parts,
                        sections,
                        alloc,
                        delivered=parsed,
                        delivered_exclude=(
                            set(route.failed_labels)
                            if route.action == "isolate"
                            else set()
                        ),
                        initial_only=initial_only,
                    )
                audit_findings = [
                    SkeletonFinding(
                        reason,
                        label=label,
                        lean_name=_lean_name(label),
                    )
                    for label in sorted(rejected)
                    if label in labels
                ]
                patched, patch_note = _targeted_patch_skeleton_decls(
                    ctx,
                    labels,
                    sections,
                    import_modules,
                    parsed,
                    module_code,
                    audit_findings,
                    timeout=ctx.hard_timeout,
                    sessions=sessions,
                    escalated=True,
                )
                corrected = False
                if patched is not None:
                    parsed = patched
                    for decl in parsed.decls:
                        if _may_defer_target_body(
                            decl, target_kinds.get(decl.name or "")
                        ):
                            decl.text = _normalize_terminal_sorry(decl.text)
                    all_imports = [f"import {m}" for m in import_modules] + parsed.imports
                    module_code, _ranges = _compose_module(
                        all_imports, parsed.preamble, [decl.text for decl in parsed.decls]
                    )
                    post_patch_findings = _skeleton_code_findings(
                        module_code,
                        target_kinds,
                        label_by_lean_name,
                        _planned_helper_owner_by_name(ctx, labels),
                    )
                    post_patch_findings += _skeleton_deterministic_findings(
                        module_code, ctx, labels
                    )
                    path.write_text(module_code, encoding="utf-8")
                    post_patch_ok, post_patch_output = _check_lean(path, ctx.lean_command)
                    if not post_patch_findings and not post_patch_ok:
                        retry_parsed, retry_code, retry_note = (
                            _retry_statement_patch_compile_once(
                                ctx,
                                labels,
                                sorted(rejected),
                                sections,
                                import_modules,
                                parsed,
                                module_code,
                                post_patch_output,
                                path,
                                sessions=sessions,
                            )
                        )
                        if retry_parsed is not None:
                            parsed = retry_parsed
                            module_code = retry_code
                            post_patch_ok = True
                            post_patch_output = ""
                        else:
                            post_patch_output += (
                                "\nOne compiler-feedback correction failed: "
                                + retry_note
                            )
                    if post_patch_findings or not post_patch_ok:
                        patch_note = (
                            "correction failed deterministic checks:\n"
                            + _format_skeleton_findings(post_patch_findings)
                            if post_patch_findings
                            else "Lean rejected the corrected file:\n"
                            + post_patch_output[-10000:]
                        )
                    else:
                        _store_generation_candidates(
                            ctx,
                            rejected,
                            module_code,
                            source="statement_alignment_correction",
                            all_labels=labels,
                            generation_tier="escalation",
                            repair_stage="semantic_corrected",
                            lean_status="passed",
                            semantic_status="correction_pending",
                            semantic_evidence=reason,
                        )
                        _record(
                            ctx.telemetry,
                            "skeleton_audit_patch",
                            section=next_number,
                            round=attempt,
                            labels=sorted(rejected),
                            status="applied",
                        )
                        _log("  patched audit-rejected declarations; re-auditing the section")
                        reaudit = _model_alignment_audit(
                            ctx, labels, module_code, tag="post-correction"
                        )
                        if reaudit is None:
                            corrected = True
                        else:
                            reaudit = _coerce_alignment_audit_result(reaudit)
                            plan_request = _audit_plan_revision_request(
                                ctx,
                                reaudit,
                                layer_no=-1,
                                source="section_alignment_post_correction",
                            )
                            if plan_request is not None:
                                raise plan_request
                            kind2, reason2, rejected2, helpers2 = reaudit
                            if kind2 in {"blueprint", "decomposition"}:
                                raise RepairRequest(
                                    reason2,
                                    sorted(rejected2),
                                    decomposition_helpers=(
                                        helpers2 if kind2 == "decomposition" else None
                                    ),
                                    section_labels=labels,
                                )
                            _store_generation_candidates(
                                ctx,
                                rejected2,
                                module_code,
                                source="statement_alignment_reaudit",
                                all_labels=labels,
                                generation_tier="escalation",
                                repair_stage="semantic_corrected",
                                lean_status="passed",
                                semantic_status="rejected",
                                semantic_evidence=reason2,
                            )
                            raise RepairRequest(
                                "Blueprint contract audit rejected the section again "
                                "after one escalated targeted correction; the blueprint "
                                "text likely under-determines the statement.\n" + reason2,
                                sorted(rejected2),
                                section_labels=labels,
                            )
                if not corrected:
                    feedback = reason + f"\n\nTargeted audit correction failed: {patch_note}"
                    _store_generation_candidates(
                        ctx,
                        rejected,
                        module_code,
                        source="statement_alignment_correction_failed",
                        all_labels=labels,
                        generation_tier="escalation",
                        repair_stage="semantic_corrected",
                        lean_status=(
                            "passed"
                            if patched is not None
                            and not post_patch_findings
                            and post_patch_ok
                            else "failed"
                            if patched is not None and not post_patch_findings
                            else "unknown"
                        ),
                        lean_output=(
                            post_patch_output
                            if patched is not None and not post_patch_findings
                            else ""
                        ),
                        semantic_status="correction_pending",
                        semantic_evidence=feedback,
                    )
                    previous_code = (
                        _generation_candidates_for(ctx, rejected) or module_code
                    )
                    if attempt < attempt_limit:
                        _log(
                            "  alignment audit correction failed; regenerating once "
                            "at escalated effort"
                        )
                        continue
                    _store_generation_candidates(
                        ctx,
                        rejected,
                        module_code,
                        source="statement_alignment",
                        all_labels=labels,
                        lean_status="passed",
                        semantic_status="rejected",
                        semantic_evidence=reason,
                    )
                    raise RepairRequest(
                        "Blueprint contract audit kept rejecting regenerated "
                        "statements; the blueprint text likely under-determines the "
                        "statement.\n" + reason,
                        sorted(rejected),
                        section_labels=labels,
                    )

            object_attempt, object_failure_class, object_evidence = (
                _compile_fast_candidate_object(
                    ctx,
                    path,
                    module_code,
                    labels,
                    complete_bodies=False,
                )
            )
            if not object_attempt.ok:
                feedback = object_evidence
                previous_code = module_code
                if (
                    object_failure_class == "interface_usability"
                    and not initial_only
                ):
                    _revise_unusable_interface_plan(ctx, labels, feedback)
                    raise RepairRequest(
                        "The exact Phase-1 statement compiled normally but its "
                        "public Lean interface exceeded the object-generation "
                        "usability budget. The blueprint is unchanged; regenerate "
                        "these contracts from a revised interface plan.\n\n"
                        + feedback[-12000:],
                        labels,
                        section_labels=labels,
                        authorizes_blueprint_repair=False,
                        plan_revision_required=True,
                        evidence_by_label={label: feedback for label in labels},
                    )
                if attempt < attempt_limit:
                    continue
                raise RepairRequest(
                    ".olean compilation failed on both bounded attempts for this "
                    "section.\n" + feedback,
                    labels,
                    section_labels=labels,
                )
            state_word = (
                "provisioned"
                if initial_only
                else "compiled candidate"
                if defer_alignment
                else "frozen"
            )
            _log(
                f"  section {next_number:02d} {state_word} "
                f"({len(parsed.decls)} declaration(s))"
            )
            _record(
                ctx.telemetry,
                "initial_declaration_section"
                if initial_only
                else "skeleton_section_candidate"
                if defer_alignment
                else "skeleton_section_frozen",
                section=next_number,
                labels=labels,
                decls=len(parsed.decls),
            )
            if not initial_only and not defer_alignment:
                _note_frozen_section(ctx, labels)
            froze = True
            section = Section(
                number=next_number,
                labels=list(labels),
                path=path,
                module=module,
                import_modules=import_modules,
                refined_labels=set() if initial_only or defer_alignment else None,
                generation_tier=(
                    "initial"
                    if initial_only
                    else "escalation"
                    if result_was_escalated
                    else "base"
                ),
            )
            _mark_section_compiled(section, ctx.lean_command, sections)
            return [section]

        raise RepairRequest(
            "Skeleton generation exhausted its bounded attempts for this section. "
            "Last feedback:\n" + feedback,
            labels,
            section_labels=labels,
        )
    finally:
        # Any exit that is not a frozen section (RepairRequest, bisect via
        # _freeze_parts, runner error) must leave no artifact behind: a
        # later generation call would otherwise find the orphan file and
        # `import` it against a stale .olean.
        if not froze:
            _discard_section_artifacts(path)


def _run_initial_declaration_pass(
    ctx: Ctx, sections: list[Section], pending: set[str]
) -> list[Section]:
    """Create every provisional Lean name once, then hand off to Phase 1.

    This pass exists only because root-first Phase 1 needs every lower-level
    name to exist before it can elaborate root interfaces. It deliberately does
    not run Lean, retry generation, audit statements, edit the blueprint, or
    spend repair budget. Model omissions are filled with deterministic internal
    placeholders; Phase 1 replaces and validates every provisional declaration.
    """
    order = [
        label
        for label in _topo_order(ctx.nodes)
        if label in pending and not ctx.nodes[label].mathlibok
    ]
    if not order:
        return sections

    next_number = max((sec.number for sec in sections), default=0) + 1
    module, path = _section_module(ctx.name, next_number)
    path.parent.mkdir(parents=True, exist_ok=True)
    import_modules = _sections_for_deps(ctx, order, sections)

    _log(
        f"==> Initial declaration pass: creating one complete boilerplate "
        f"file for {len(order)} node(s)"
    )
    result = _call_model(
        ctx,
        _initial_declaration_prompt(
            ctx,
            order,
            sections,
            import_modules,
            timeout_s=ctx.base_timeout,
        ),
        purpose="initial_declaration_generation",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=order,
        escalated=False,
    )

    candidate = result.text or result.partial_text
    parsed = ParsedModule(imports=[], preamble=[], decls=[])
    parse_error = ""
    if candidate.strip():
        try:
            parsed = _ingest_model_lean(
                ctx,
                order,
                candidate,
                defer_phase1_bodies=True,
            ).parsed
        except ValueError as exc:
            parse_error = str(exc)
    elif result.error:
        parse_error = result.error

    missing_imports = _missing_olean_imports(parsed.imports)
    if missing_imports:
        ctx.unavailable_imports.update(missing_imports)
    usable_imports = [
        item for item in parsed.imports if item not in set(missing_imports)
    ]
    delivered = {decl.name: decl for decl in parsed.decls if decl.name}
    decl_texts: list[str] = []
    fallback_labels: list[str] = []
    for label in order:
        lean_name = _lean_name(label)
        decl = delivered.get(lean_name)
        if decl is not None:
            decl_texts.append(decl.text)
            continue
        fallback_labels.append(label)
        if _is_theorem_like_kind(ctx.nodes[label].kind):
            decl_texts.append(f"theorem {lean_name} : True := by trivial")
        else:
            decl_texts.append(f"def {lean_name} : Unit := ()")

    all_imports = [f"import {item}" for item in import_modules] + usable_imports
    module_code, _ranges = _compose_module(
        all_imports, parsed.preamble, decl_texts
    )
    path.write_text(module_code, encoding="utf-8")
    section = Section(
        number=next_number,
        labels=list(order),
        path=path,
        module=module,
        import_modules=import_modules,
        refined_labels=set(),
        provisional_environment=True,
        generation_tier="initial",
    )
    result_sections = sections + [section]
    _save_ctx_state(ctx, result_sections)
    _record(
        ctx.telemetry,
        "initial_declaration_environment",
        labels=order,
        count=len(order),
        module=module,
        model_status=result.status,
        model_declarations=len(order) - len(fallback_labels),
        fallback_labels=fallback_labels,
        parse_error=parse_error,
    )
    if fallback_labels:
        _log(
            f"  filled {len(fallback_labels)} omitted boilerplate name(s) "
            "deterministically; Phase 1 will replace them"
        )
    _log(
        f"==> Initial declaration pass complete: one boilerplate file "
        f"contains all {len(order)} generated names"
    )
    return result_sections


def _add_phase1_boilerplate_names(
    ctx: Ctx, sections: list[Section], pending: set[str]
) -> list[Section]:
    """Add names introduced by a contract repair without rerunning stage zero."""
    environment = next(
        (sec for sec in sections if sec.provisional_environment), None
    )
    if environment is None:
        raise ValueError(
            f"{_contract_work_stage(ctx)} needs new provisional names, but the persisted initial "
            "boilerplate environment is unavailable"
        )
    parsed, index = _module_decl_texts(environment)
    added: list[str] = []
    for label in _topo_order(ctx.nodes):
        if label not in pending or ctx.nodes[label].mathlibok:
            continue
        lean_name = _lean_name(label)
        if lean_name not in index:
            if _is_theorem_like_kind(ctx.nodes[label].kind):
                text = f"theorem {lean_name} : True := by trivial"
            else:
                text = f"def {lean_name} : Unit := ()"
            parsed.decls.append(
                DeclBlock(
                    kind="theorem" if _is_theorem_like_kind(ctx.nodes[label].kind) else "def",
                    name=lean_name,
                    text=text,
                )
            )
            index[lean_name] = len(parsed.decls) - 1
        if label not in environment.labels:
            environment.labels.append(label)
        added.append(label)
    environment.deferred = False
    if environment.refined_labels is None:
        environment.refined_labels = set()
    _write_section(environment, parsed)
    _discard_section_objects(environment.path)
    _save_ctx_state(ctx, sections)
    _record(
        ctx.telemetry,
        "phase1_boilerplate_names_added",
        labels=added,
        count=len(added),
        module=environment.module,
    )
    _log(
        f"==> {_contract_work_stage(ctx)}: added {len(added)} provisional name(s) introduced "
        "by blueprint repair; continuing statement refinement"
    )
    return sections


# ---------------------------------------------------------------------------
# Phase 1: root-first statement refinement


def _generate_phase1_statement_group(
    ctx: Ctx,
    sec: Section,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    parsed: ParsedModule,
    *,
    force_first_escalated: bool = False,
    sessions: dict[str, str] | None = None,
    generation_tier_out: list[str] | None = None,
) -> ParsedModule:
    """Replace stage-zero boilerplate with exact Phase-1 declarations first.

    The initial file exists only to provide names. Its declarations are never
    valid statement-audit evidence. This generation transaction must therefore
    run before deterministic checks, Lean compilation, or blueprint repair.
    """
    sessions = sessions if sessions is not None else {}
    feedback = _generation_feedback_for(ctx, labels)
    previous_code = _generation_candidates_for(ctx, labels)
    independent_decomposition_adjudication = False

    def route_multi_failure(
        evidence: str, attributable_labels: Iterable[str] | None = None
    ) -> None:
        """Return multi-node statement failures to the shared scope router."""
        if len(labels) <= 1:
            return
        route = _route_lean_generation_failure(labels, attributable_labels)
        raise RepairRequest(
            evidence,
            list(route.failed_labels),
            section_labels=labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
        )

    for escalated in ((True,) if force_first_escalated else (False, True)):
        timeout = ctx.hard_timeout if escalated else ctx.base_timeout
        prompt = (
            _bulk_skeleton_prompt(
                ctx,
                labels,
                sections,
                import_modules,
                timeout_s=timeout,
            )
            if not feedback and not previous_code
            else _skeleton_prompt(
                ctx,
                labels,
                sections,
                import_modules,
                feedback=feedback,
                previous_code=previous_code,
                timeout_s=timeout,
            )
        )
        result = _call_model(
            ctx,
            prompt,
            purpose="phase1_statement_generation",
            timeout=timeout,
            effort=ctx.escalation_effort if escalated else ctx.base_effort,
            labels=labels,
            escalated=escalated,
            sessions=sessions,
            force_fresh=independent_decomposition_adjudication,
        )
        candidate = result.text or result.partial_text
        refusal = _parse_decomposition_refusal(
            candidate, expected_labels=labels
        )
        if refusal is not None:
            feedback = (
                "An independent statement generator reported that the blueprint "
                "may need decomposition. Adjudicate that diagnosis from the "
                "authoritative blueprint and frozen interfaces. Do not assume it "
                "is correct and do not try to overturn it. Either emit every exact "
                "Phase 1 declaration if the existing interfaces are sufficient, "
                "or independently return the documented NEEDS-DECOMPOSITION JSON "
                "with the exact missing helpers and reason.\n"
                f"Reported reason: {refusal.get('reason', '')}\n"
                "Reported missing helpers: "
                + ", ".join(refusal.get("missing_helpers") or [])
            )
            previous_code = ""
            if escalated:
                raise RepairRequest(
                    "The escalated Phase 1 statement generator determined that "
                    "the blueprint contract needs decomposition.\n"
                    f"Reason: {refusal.get('reason', '')}",
                    [str(refusal.get("label") or labels[0])],
                    decomposition_helpers=[
                        str(item) for item in refusal.get("missing_helpers") or []
                    ],
                    section_labels=labels,
                )
            _record(
                ctx.telemetry,
                "phase1_decomposition_adjudication",
                labels=labels,
                reported_label=str(refusal.get("label") or ""),
                reported_missing_helpers=[
                    str(item) for item in refusal.get("missing_helpers") or []
                ],
                reported_reason=str(refusal.get("reason") or ""),
                forced_fresh_session=True,
            )
            _log(
                "  base decomposition refusal requires an independent "
                "fresh-session adjudication"
            )
            independent_decomposition_adjudication = True
            continue
        if result.status != "ok" and not candidate.strip():
            feedback = (
                f"The statement-generation call {result.status}: "
                f"{result.error or 'no complete response'}. Return every target "
                "declaration in one Lean code block."
            )
            if not escalated:
                route_multi_failure(feedback)
            continue
        try:
            replacement_module = _ingest_model_lean(
                ctx,
                labels,
                candidate,
                realize_contracts=True,
                defer_phase1_bodies=True,
            ).parsed
            replacement_code, _ = _compose_module(
                replacement_module.imports,
                replacement_module.preamble,
                [decl.text for decl in replacement_module.decls],
            )
        except ValueError as exc:
            feedback = f"The response was not a Lean statement file: {exc}"
            previous_code = candidate
            if not escalated:
                route_multi_failure(feedback)
            continue
        _store_generation_candidates(
            ctx,
            labels,
            replacement_code,
            source="phase1_statement_generation",
            all_labels=labels,
        )
        self_import = f"import {sec.module}"
        if self_import in replacement_module.imports:
            replacement_module.imports = [
                item for item in replacement_module.imports if item != self_import
            ]
            _record(
                ctx.telemetry,
                "phase1_self_import_removed",
                section=sec.number,
                module=sec.module,
                labels=labels,
            )
            replacement_code, _ = _compose_module(
                replacement_module.imports,
                replacement_module.preamble,
                [decl.text for decl in replacement_module.decls],
            )
        patched = _apply_skeleton_replacements(
            parsed,
            labels,
            labels,
            replacement_code,
            _planned_helper_owner_by_name(ctx, labels),
            unavailable_imports=ctx.unavailable_imports,
        )
        if patched is None:
            delivered = {
                decl.name for decl in replacement_module.decls if decl.name
            }
            missing = [
                label for label in labels if _lean_name(label) not in delivered
            ]
            feedback = (
                "The response omitted required Phase 1 declarations: "
                + ", ".join(
                    f"{label} -> `{_lean_name(label)}`" for label in missing
                )
                + ". Return every target statement, not a subset."
            )
            previous_code = candidate
            generation_tier = "escalation" if escalated else "base"
            salvaged = _salvage_partial_phase1_response(
                ctx,
                labels,
                replacement_module,
                sections,
                generation_tier=generation_tier,
            )
            unresolved = [label for label in labels if label not in salvaged]
            if salvaged:
                feedback += (
                    " Preserved deterministically valid returned declarations: "
                    + ", ".join(salvaged)
                    + ". Retry only the unresolved declarations."
                )
            route_multi_failure(
                feedback,
                unresolved if unresolved and len(unresolved) < len(labels) else None,
            )
            continue
        patched.preamble = list(
            dict.fromkeys(
                patched.preamble
                + [
                    line
                    for line in replacement_module.preamble
                    if line.strip().startswith("open")
                ]
            )
        )
        _record(
            ctx.telemetry,
            "phase1_statement_generation",
            section=sec.number,
            labels=labels,
            count=len(labels),
            escalated=escalated,
            status="applied",
        )
        if generation_tier_out is not None:
            generation_tier_out.append("escalation" if escalated else "base")
        return patched

    route = _route_lean_generation_failure(labels)
    raise RepairRequest(
        "Phase 1 statement generation could not deliver every requested "
        "declaration after base and escalation attempts. This is generation "
        "failure evidence, not evidence that provisional placeholders were "
        "mathematically wrong.\n" + feedback,
        list(route.failed_labels),
        section_labels=labels,
        authorizes_blueprint_repair=False,
        failure_route=route,
    )


def _phase1_layer_candidate_code(candidate: Phase1LayerCandidate) -> str:
    imports = [f"import {module}" for module in candidate.import_modules]
    return _compose_module(
        imports + candidate.parsed.imports,
        candidate.parsed.preamble,
        [decl.text for decl in candidate.parsed.decls],
    )[0]


def _phase1_layer_candidates_code(candidates: list[Phase1LayerCandidate]) -> str:
    """Combine candidate declarations for one batched semantic judgment."""
    return "\n\n".join(
        decl.text
        for candidate in candidates
        for decl in candidate.parsed.decls
    )


def _subset_phase1_candidate(
    ctx: Ctx, candidate: Phase1LayerCandidate, labels: Iterable[str]
) -> Phase1LayerCandidate | None:
    """Extract selected targets and their owned local helpers in original order."""
    wanted = [label for label in candidate.labels if label in set(labels)]
    if not wanted:
        return None
    decl_texts = _delivered_decl_texts(
        candidate.parsed,
        wanted,
        {_lean_name(label) for label in candidate.labels},
        _planned_helper_owner_by_name(ctx, candidate.labels),
    )
    if not decl_texts:
        return None
    return Phase1LayerCandidate(
        labels=wanted,
        parsed=ParsedModule(
            imports=list(candidate.parsed.imports),
            preamble=list(candidate.parsed.preamble),
            decls=[
                DeclBlock(decl.kind, decl.name, decl.text)
                for decl in _parse_module(
                    _compose_module([], [], decl_texts)[0]
                ).decls
            ],
        ),
        import_modules=list(candidate.import_modules),
        generation_tier=candidate.generation_tier,
        sessions=candidate.sessions,
        plan_fps={
            label: candidate.plan_fps.get(label, "") for label in wanted
        },
    )


def _generate_uncompiled_phase1_candidate(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
) -> Phase1LayerCandidate:
    """Generate and deterministically validate statements without running Lean."""
    repaired = _semantic_repair_candidate(ctx, labels, sections)
    if repaired is not None:
        return repaired
    reused = _reusable_uncompiled_candidate(ctx, labels, sections)
    if reused is not None:
        return reused
    import_modules = _sections_for_deps(ctx, labels, sections)
    placeholders = ParsedModule(
        imports=[],
        preamble=[],
        decls=[
            DeclBlock(
                "theorem" if _is_theorem_like_kind(ctx.nodes[label].kind) else "def",
                _lean_name(label),
                (
                    f"theorem {_lean_name(label)} : True := sorry"
                    if _is_theorem_like_kind(ctx.nodes[label].kind)
                    else f"def {_lean_name(label)} : Unit := ()"
                ),
            )
            for label in labels
        ],
    )
    fake_section = Section(
        number=0,
        labels=list(labels),
        path=SCRATCH_DIR / ctx.name / "Phase1Uncompiled.lean",
        module=f"AutoBlueprint.Generated.{_module_safe_name(ctx.name)}.Phase1Uncompiled",
        import_modules=import_modules,
        refined_labels=set(),
    )
    sessions: dict[str, str] = {}
    tier: list[str] = []
    parsed = _generate_phase1_statement_group(
        ctx,
        fake_section,
        labels,
        sections,
        import_modules,
        placeholders,
        force_first_escalated=bool(
            len(labels) == 1
            and _retry_next_tier(ctx, labels[0], "phase1_statement") == "escalation"
        ),
        sessions=sessions,
        generation_tier_out=tier,
    )
    # Fresh Phase-1 generation realizes its exact typed contract from this
    # same response.  That candidate-owned refresh is part of the transaction,
    # not a competing plan edit, so salvage must compare against the resulting
    # contract epoch rather than the advisory epoch that preceded generation.
    generation_plan_fps = {
        label: _candidate_plan_fingerprint(ctx, label) for label in labels
    }
    target_kinds = _phase1_target_kinds(ctx, labels)
    label_by_name = {_lean_name(label): label for label in labels}
    for decl in parsed.decls:
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    candidate = Phase1LayerCandidate(
        labels=list(labels),
        parsed=parsed,
        import_modules=import_modules,
        generation_tier=tier[-1] if tier else "base",
        sessions=sessions,
        plan_fps=generation_plan_fps,
    )
    code = _phase1_layer_candidate_code(candidate)
    findings = _skeleton_code_findings(
        code,
        target_kinds,
        label_by_name,
        _planned_helper_owner_by_name(ctx, labels),
    )
    findings += _skeleton_deterministic_findings(code, ctx, labels)
    if findings:
        plan_revision_required = _findings_require_plan_revision(ctx, findings)
        patched, note = (None, "plan revision required")
        if not plan_revision_required:
            patched, note = _targeted_patch_skeleton_decls(
                ctx,
                labels,
                sections,
                import_modules,
                parsed,
                code,
                findings,
                timeout=(
                    ctx.hard_timeout
                    if candidate.generation_tier == "escalation"
                    else ctx.base_timeout
                ),
                sessions=sessions,
                escalated=candidate.generation_tier == "escalation",
            )
        if patched is not None:
            candidate.parsed = patched
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
            evidence = _format_skeleton_findings(findings)
            if note and note != "not patchable":
                evidence += "\n\nTargeted declaration patch result: " + note
            failed = _isolated_deterministic_failure_labels(findings, labels)
            route = _route_lean_generation_failure(labels, failed or None)
            _store_generation_candidates(
                ctx,
                route.failed_labels,
                code,
                source="semantic_first_deterministic",
                all_labels=labels,
            )
            _store_generation_feedback(
                ctx,
                route.failed_labels,
                evidence,
                source="semantic_first_deterministic",
                evidence_by_label=_generation_evidence_from_findings(
                    route.failed_labels, findings
                ),
            )
            raise RepairRequest(
                "Uncompiled Phase-1 candidate failed deterministic checks:\n"
                + evidence[-10000:],
                list(route.failed_labels),
                section_labels=labels,
                authorizes_blueprint_repair=False,
                failure_route=route,
                plan_revision_required=plan_revision_required,
                retry_attempted_tier=(
                    "" if plan_revision_required else candidate.generation_tier
                ),
                evidence_by_label=_generation_evidence_from_findings(
                    route.failed_labels, findings
                ),
            )
    _record(
        ctx.telemetry,
        "phase1_uncompiled_candidate",
        labels=labels,
        count=len(labels),
        generation_tier=candidate.generation_tier,
    )
    _store_generation_candidates(
        ctx,
        labels,
        code,
        source="semantic_first_pre_audit",
        all_labels=labels,
        reusable_uncompiled=True,
        generation_tier=candidate.generation_tier,
        repair_stage="deterministic_valid",
    )
    return candidate


def _revise_semantic_candidates(
    ctx: Ctx,
    candidates: list[Phase1LayerCandidate],
    rejected: set[str],
    reason: str,
    sections: list[Section],
    *,
    required_dependencies: dict[str, set[str]] | None = None,
    reason_by_label: Mapping[str, str] | None = None,
) -> list[Phase1LayerCandidate]:
    """Apply one exact-feedback revision only to audit-rejected candidates."""
    revisions: list[Phase1LayerCandidate] = []
    for candidate in candidates:
        subset = _subset_phase1_candidate(ctx, candidate, rejected)
        if subset is None:
            continue
        findings = [
            SkeletonFinding(
                str((reason_by_label or {}).get(label) or reason),
                label=label,
                lean_name=_lean_name(label),
            )
            for label in subset.labels
        ]
        code = _phase1_layer_candidate_code(subset)
        patched, note = _targeted_patch_skeleton_decls(
            ctx,
            subset.labels,
            sections,
            subset.import_modules,
            subset.parsed,
            code,
            findings,
            timeout=(
                ctx.hard_timeout
                if subset.generation_tier == "escalation"
                else ctx.base_timeout
            ),
            sessions=subset.sessions,
            escalated=subset.generation_tier == "escalation",
            # The semantic-repair path starts from the authoritative evidence
            # ledger. Rendering the synthetic findings as well recursively
            # duplicated that ledger in later retries.
            findings_already_persisted=True,
        )
        if patched is None:
            evidence = (
                "Semantic correction failed for the rejected declaration(s): "
                + note
                + "\n"
                + reason
            )
            # ``reason`` is already stored in the per-node diagnostic ledger.
            # Persist only the new patch failure here; storing reason + note as
            # one new fact recursively embeds the old evidence on every retry.
            patch_failure = "Targeted semantic correction failed: " + note
            raise RepairRequest(
                evidence,
                subset.labels,
                section_labels=subset.labels,
                authorizes_blueprint_repair=False,
                failure_route=_route_lean_generation_failure(subset.labels),
                retry_attempted_tier=subset.generation_tier,
                evidence_by_label={
                    label: patch_failure
                    for label in subset.labels
                },
            )
        subset.parsed = patched
        target_kinds = _phase1_target_kinds(ctx, subset.labels)
        label_by_name = {_lean_name(label): label for label in subset.labels}
        for decl in subset.parsed.decls:
            if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
                decl.text = _normalize_terminal_sorry(decl.text)
        revised_code = _phase1_layer_candidate_code(subset)
        deterministic = _skeleton_code_findings(
            revised_code,
            target_kinds,
            label_by_name,
            _planned_helper_owner_by_name(ctx, subset.labels),
        )
        deterministic += _skeleton_deterministic_findings(
            revised_code, ctx, subset.labels
        )
        if deterministic:
            evidence = _format_skeleton_findings(deterministic)
            plan_revision_required = _findings_require_plan_revision(
                ctx, deterministic
            )
            confirmed_dependencies: dict[str, set[str]] = {}
            for finding in deterministic:
                if not finding.label or not finding.dependencies:
                    continue
                certified = set(
                    (required_dependencies or {}).get(finding.label, set())
                )
                matched = set(finding.dependencies) & certified
                if matched:
                    confirmed_dependencies.setdefault(
                        finding.label, set()
                    ).update(matched)
            if confirmed_dependencies:
                _record(
                    ctx.telemetry,
                    "phase1_dependency_repair_authorized",
                    labels=sorted(confirmed_dependencies),
                    required_dependencies={
                        label: sorted(dependencies)
                        for label, dependencies in confirmed_dependencies.items()
                    },
                    evidence=evidence[-4000:],
                    authorization=(
                        "statement critic and deterministic closure finding agree"
                    ),
                )
                raise RepairRequest(
                    "Semantic correction requires missing blueprint statement "
                    "dependency edge(s):\n" + evidence,
                    sorted(confirmed_dependencies),
                    section_labels=subset.labels,
                    authorizes_blueprint_repair=True,
                    required_dependencies=confirmed_dependencies,
                )
            raise RepairRequest(
                "Semantic correction introduced deterministic statement errors:\n"
                + evidence,
                subset.labels,
                section_labels=subset.labels,
                authorizes_blueprint_repair=False,
                failure_route=_route_lean_generation_failure(subset.labels),
                plan_revision_required=plan_revision_required,
                retry_attempted_tier=(
                    "" if plan_revision_required else subset.generation_tier
                ),
                evidence_by_label=_generation_evidence_from_findings(
                    subset.labels, deterministic
                ),
            )
        revisions.append(subset)
        _record(
            ctx.telemetry,
            "phase1_semantic_revision",
            labels=subset.labels,
            producing_tier=subset.generation_tier,
            status="delivered",
        )
    return revisions


def _revise_unusable_interface_plan(
    ctx: Ctx, labels: Iterable[str], evidence: str
) -> bool:
    """Change strategy once when an exact interface cannot build efficiently.

    The failure is operational evidence about the Lean representation, not
    mathematical evidence against the blueprint.  Prefer the retained
    alternate, then one focused base-tier correction.  If neither changes the
    plan, invalidate only these entries so the next frontier obtains a fresh
    scoped plan instead of regenerating forever under the same interface.
    """
    targets = list(dict.fromkeys(label for label in labels if label in ctx.nodes))
    if not targets:
        return False
    corrected = _correct_phase1_design_plan(
        ctx,
        targets,
        evidence,
        escalated=False,
        try_alternate=True,
    )
    if corrected:
        _record(
            ctx.telemetry,
            "phase1_interface_usability_plan",
            labels=targets,
            status="revised",
            next_action="regenerate_exact_statements",
        )
        return True

    entries = getattr(ctx, "design_plan_entries", {})
    alternates = getattr(ctx, "design_plan_alternates", {})
    invalidated = [label for label in targets if label in entries]
    for label in invalidated:
        entries.pop(label, None)
        alternates.pop(label, None)
    if invalidated:
        _transition_phase1_generation_epoch(
            ctx,
            invalidated,
            reason="interface_usability_plan_invalidated",
        )
    _record(
        ctx.telemetry,
        "phase1_interface_usability_plan",
        labels=targets,
        status="invalidated" if invalidated else "unavailable",
        next_action="fresh_scoped_planning",
    )
    return bool(invalidated)


def _route_phase1_compile_failure(
    ctx: Ctx,
    failed: Phase1LayerCandidate,
    evidence: str,
    failed_code: str,
    *,
    layer_no: int,
) -> RepairRequest:
    """Persist and route one completed Phase-1 compile failure immediately.

    Candidate groups compile independently.  Once one worker has produced a
    complete failure, neither its diagnostics nor its next action depends on
    slower siblings.  Keeping this routing in one helper lets the coordinator
    overlap plan correction/retry bookkeeping with those still-running workers
    without changing any of the existing failure classification rules.
    """
    interface_evidence = _phase1_interface_usability_evidence(evidence)
    if interface_evidence:
        # Persist the failure only in the strategy epoch that produced it.
        # Revising the plan below prunes this candidate.  Storing afterward
        # would incorrectly stamp the old Lean declaration with the revised
        # plan fingerprint and make it eligible for a zero-call retry.
        _store_generation_candidates(
            ctx,
            failed.labels,
            failed_code,
            source="phase1_interface_usability_gate",
            all_labels=failed.labels,
            lean_status="failed",
            lean_output=interface_evidence,
            expected_plan_fps=failed.plan_fps,
        )
        _store_generation_feedback(
            ctx,
            failed.labels,
            interface_evidence,
            source="phase1_interface_usability_gate",
        )

        # This lifecycle is intentionally separate from ordinary malformed-Lean
        # retries and survives plan epoch changes. Otherwise each corrected plan
        # looks like a first failure and can trigger another correction forever.
        lifecycle = getattr(ctx, "retry_lifecycle", {}) or {}
        prior_labels = {
            label
            for label in failed.labels
            if getattr(ctx, "stmt_fps", {}).get(label)
            and lifecycle.get(
                _retry_lifecycle_key("phase1_interface_usability", label), {}
            ).get("statement_fp")
            == getattr(ctx, "stmt_fps", {}).get(label)
        }
        direct_labels = {
            label
            for label in failed.labels
            if _uses_blueprint_direct_generation(ctx, label)
        }
        first_plan_correction = [
            label
            for label in failed.labels
            if label not in prior_labels and label not in direct_labels
        ]
        if first_plan_correction:
            _record_retry_failure(
                ctx,
                first_plan_correction,
                stage="phase1_interface_usability",
                attempted_tier="base",
                evidence=interface_evidence,
                source="phase1_interface_plan_correction",
            )
            revised = _revise_unusable_interface_plan(
                ctx, first_plan_correction, interface_evidence
            )
            if revised:
                return RepairRequest(
                    "The Phase-1 public interface exhausted Lean's elaboration "
                    "budget after all target bodies were replaced by `sorry`. "
                    "The blueprint is unchanged; retry only these contracts "
                    "under the one bounded interface-plan correction.\n\n"
                    + interface_evidence[-12000:],
                    first_plan_correction,
                    section_labels=failed.labels,
                    authorizes_blueprint_repair=False,
                    plan_revision_required=True,
                    evidence_by_label={
                        label: interface_evidence
                        for label in first_plan_correction
                    },
                )

        switch_direct = [
            label
            for label in failed.labels
            if not _uses_blueprint_direct_generation(ctx, label)
        ]
        if switch_direct:
            _record_retry_failure(
                ctx,
                switch_direct,
                stage="phase1_interface_usability",
                attempted_tier="escalation",
                evidence=interface_evidence,
                source="phase1_interface_blueprint_direct",
            )
            activated = _activate_blueprint_direct_generation(
                ctx,
                switch_direct,
                interface_evidence,
                source="phase1_interface_usability_exhaustion",
                shared_evidence=True,
            )
            if activated:
                return RepairRequest(
                    "The one bounded interface-plan correction remained "
                    "unusable. The blueprint is unchanged; generate a bounded "
                    "same-node interface directly from the blueprint and exact "
                    "Lean evidence.\n\n"
                    + interface_evidence[-12000:],
                    sorted(activated),
                    section_labels=failed.labels,
                    authorizes_blueprint_repair=False,
                    plan_revision_required=True,
                    evidence_by_label={
                        label: interface_evidence for label in activated
                    },
                )

        # Blueprint-direct generation is the final non-mutating strategy. A
        # compiler budget failure cannot itself prove that the mathematical
        # blueprint needs helper nodes. Retry the exact node through the normal
        # bounded generation lifecycle; only an explicit, independently
        # adjudicated NEEDS-DECOMPOSITION response may authorize mutation.
        attempted_tier = (
            failed.generation_tier
            if failed.generation_tier in {"base", "escalation"}
            else "base"
        )
        _record_retry_failure(
            ctx,
            failed.labels,
            stage="phase1_statement",
            attempted_tier=attempted_tier,
            evidence=interface_evidence,
            source="phase1_interface_blueprint_direct_retry",
        )
        route = _route_lean_generation_failure(failed.labels)
        return RepairRequest(
            "Blueprint-direct Phase-1 generation still exceeded Lean's public-"
            "interface budget. The blueprint remains unchanged. Regenerate the "
            "same node with the exact evidence, or explicitly return "
            "NEEDS-DECOMPOSITION if no faithful bounded same-node representation "
            "exists.\n\n"
            + interface_evidence[-12000:],
            list(route.failed_labels),
            section_labels=failed.labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            retry_attempted_tier=attempted_tier,
            evidence_by_label={
                label: interface_evidence for label in failed.labels
            },
        )
    plan_defects = _phase1_compile_plan_defects(
        ctx, failed.labels, failed_code, evidence
    )
    scoped_evidence = _compiler_generation_evidence_by_label(
        ctx, failed.labels, failed_code, evidence
    )
    _store_generation_candidates(
        ctx,
        failed.labels,
        failed_code,
        source="validated_contract_compile",
        all_labels=failed.labels,
        lean_status="failed",
        lean_output=evidence,
    )
    _store_generation_feedback(
        ctx,
        failed.labels,
        evidence,
        source="validated_contract_compile",
        evidence_by_label=scoped_evidence,
    )
    revised: set[str] = set()
    if plan_defects:
        plan_evidence = (
            "A generated Phase-1 target copied its accepted plan, but "
            "Lean rejected that plan-owned interface. Correct the plan "
            "to use verified Lean/Mathlib declarations or a faithful "
            "plan-owned helper; do not weaken the blueprint claim.\n"
            + "\n".join(
                f"- {label}: {reason}"
                for label, reason in sorted(plan_defects.items())
            )
            + "\n\nCompiler evidence:\n"
            + evidence[-10000:]
        )
        revised = _revise_exhausted_phase1_contracts(
            ctx,
            plan_defects,
            plan_evidence,
            policy="post_compile_plan_realization",
        )
        _record(
            ctx.telemetry,
            "phase1_plan_realized_compile_rejection",
            layer=layer_no,
            labels=sorted(plan_defects),
            revised_labels=sorted(revised),
            reasons=plan_defects,
            error_shape=_lean_error_shape(evidence),
        )

    ordinary_labels = [
        label for label in failed.labels if label not in revised
    ]
    # A multi-target compiler command can fail because of one declaration.
    # Declaration-range attribution above identifies that owner.  Do not make
    # unrelated siblings consume a retry (or inherit somebody else's error)
    # merely because they shared the command.  When Lean output cannot be
    # attributed at all, retain the existing group route so its bisection
    # policy can isolate the failure.
    retry_labels = (
        [label for label in ordinary_labels if label in scoped_evidence]
        if scoped_evidence
        else list(ordinary_labels)
    )
    preserved_labels = [
        label for label in ordinary_labels if label not in retry_labels
    ]
    if preserved_labels:
        _record(
            ctx.telemetry,
            "phase1_compile_unattributed_siblings_preserved",
            layer=layer_no,
            failed_labels=retry_labels,
            preserved_labels=preserved_labels,
            generation_tier=failed.generation_tier,
        )
    if retry_labels:
        attempted_tier = (
            failed.generation_tier
            if failed.generation_tier in {"base", "escalation"}
            else "base"
        )
        exhausted: set[str] = set()
        for label in retry_labels:
            exhausted.update(
                _record_retry_failure(
                    ctx,
                    [label],
                    stage="phase1_statement",
                    attempted_tier=attempted_tier,
                    evidence=scoped_evidence.get(label, evidence),
                    source=f"phase1_layer_{layer_no}_compile",
                )
            )

        if exhausted:
            decomposition, strategy_changed, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    exhausted,
                    evidence,
                    layer_no=layer_no,
                    source="integrated_compile",
                    failure_kind="compile",
                    evidence_by_label=scoped_evidence,
                )
            )
            if decomposition:
                _record(
                    ctx.telemetry,
                    "phase1_compile_failure_routed",
                    layer=layer_no,
                    labels=sorted(decomposition),
                    classification="decomposition",
                    route="blueprint_decomposition",
                    attempted_tier=attempted_tier,
                )
                return RepairRequest(
                    "Repeated statement-generation and compiler correction "
                    "could not express these blueprint contracts as bounded "
                    "Lean declarations. Decompose only the listed contracts "
                    "into explicit blueprint helper definitions or lemmas, "
                    "then regenerate their interfaces.\n\nCompiler evidence:\n"
                    + evidence[-12000:],
                    sorted(decomposition),
                    decomposition_helpers=[
                        "split the failing public contract into explicit "
                        "blueprint-owned helper definitions or lemmas whose "
                        "Lean interfaces can be generated and compiled "
                        "independently"
                    ],
                    section_labels=sorted(decomposition),
                    authorizes_blueprint_repair=True,
                    evidence_by_label={
                        label: scoped_evidence[label]
                        for label in decomposition
                        if label in scoped_evidence
                    },
                )
            if strategy_changed:
                route = _route_lean_generation_failure(strategy_changed)
                _record(
                    ctx.telemetry,
                    "phase1_compile_failure_routed",
                    layer=layer_no,
                    labels=sorted(strategy_changed),
                    classification="strategy_changed",
                    route="plan_revision_or_blueprint_direct",
                    attempted_tier=attempted_tier,
                )
                return RepairRequest(
                    "The compiler retry lifecycle was exhausted, so the "
                    "statement-generation strategy was changed before another "
                    "candidate is attempted.\n\nCompiler evidence:\n"
                    + evidence[-12000:],
                    sorted(strategy_changed),
                    section_labels=sorted(strategy_changed),
                    authorizes_blueprint_repair=False,
                    failure_route=route,
                    plan_revision_required=True,
                    evidence_by_label={
                        label: scoped_evidence[label]
                        for label in strategy_changed
                        if label in scoped_evidence
                    },
                )
            retry_labels = [
                label
                for label in retry_labels
                if label not in exhausted or label in unresolved
            ]

        if not retry_labels:
            # Defensive fallback: the exhaustion router normally returns as
            # soon as every label changes strategy.  If a future policy leaves
            # an exhausted label unresolved, keep it in the bounded retry path
            # instead of terminating the entire run on bookkeeping state.
            retry_labels = sorted(exhausted)
        route = _route_lean_generation_failure(retry_labels)
        _record(
            ctx.telemetry,
            "phase1_compile_failure_routed",
            layer=layer_no,
            labels=retry_labels,
            classification="lean_generation",
            route=route.action,
            attempted_tier=attempted_tier,
            exhausted_labels=sorted(exhausted),
        )
        return RepairRequest(
            "A contract-planned statement candidate failed Lean "
            "compilation:\n" + evidence[-12000:],
            list(route.failed_labels),
            section_labels=retry_labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            evidence_by_label={
                label: scoped_evidence[label]
                for label in route.failed_labels
                if label in scoped_evidence
            },
        )
    _record(
        ctx.telemetry,
        "phase1_compile_failure_routed",
        layer=layer_no,
        labels=sorted(revised),
        classification="plan_revision",
        route="plan_revision_required",
    )
    return RepairRequest(
        "The accepted Phase-1 plan was corrected after its "
        "exact emitted interface failed Lean compilation:\n"
        + evidence[-12000:],
        sorted(revised),
        section_labels=sorted(revised),
        authorizes_blueprint_repair=False,
        plan_revision_required=True,
    )


def _finalize_phase1_accepted_sections(
    ctx: Ctx,
    layer_no: int,
    candidates: list[Section],
    existing_sections: list[Section] | None = None,
) -> list[Section]:
    """Build objects and run the import gate only after semantic acceptance.

    Ordinary Lean checking happens before the statement audit.  Object
    generation is a second, materially more expensive compiler operation and
    is not evidence used by that audit.  Delaying it until acceptance prevents
    rejected candidates from consuming the object-build budget while retaining
    the exact same object and integrated-import gates for every frozen section.
    """
    if not candidates:
        return []
    all_sections = list(existing_sections or []) + list(candidates)
    failures: list[RepairRequest] = []
    accepted: list[Section] = []
    worker_count = max(1, min(getattr(ctx, "workers", 1), len(candidates)))

    def build_one(section: Section) -> tuple[Section, str, str, str]:
        code = section.path.read_text(encoding="utf-8")
        expected = _section_compile_fingerprint(
            section, ctx.lean_command, all_sections
        )
        if (
            section.compile_fingerprint == expected
            and _section_objects_exist(section)
        ):
            return section, code, "", ""
        attempt, failure_class, evidence = _compile_fast_candidate_object(
            ctx,
            section.path,
            code,
            section.labels,
            complete_bodies=False,
        )
        if attempt.ok:
            _mark_section_compiled(section, ctx.lean_command, all_sections)
            return section, code, "", ""
        section.compile_fingerprint = ""
        return section, code, failure_class, evidence

    with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
        futures = [pool.submit(build_one, section) for section in candidates]
        for future in concurrent.futures.as_completed(futures):
            section, code, failure_class, evidence = future.result()
            if not failure_class:
                accepted.append(section)
                continue
            parsed = _parse_module(code)
            failed = Phase1LayerCandidate(
                labels=list(section.labels),
                parsed=parsed,
                import_modules=list(section.import_modules),
                generation_tier=section.generation_tier,
            )
            failures.append(
                _route_phase1_compile_failure(
                    ctx,
                    failed,
                    evidence,
                    code,
                    layer_no=layer_no,
                )
            )
            _discard_section_artifacts(section.path)

    accepted.sort(key=lambda section: section.number)
    if accepted:
        gate = SCRATCH_DIR / ctx.name / f"Phase1Layer{layer_no:02d}Gate.lean"
        gate.parent.mkdir(parents=True, exist_ok=True)
        gate.write_text(
            "\n".join(f"import {section.module}" for section in accepted)
            + "\n\nset_option autoImplicit false\n\n"
            "theorem phase1_layer_gate : True := by trivial\n",
            encoding="utf-8",
        )
        try:
            integrated, output = _check_lean(gate, ctx.lean_command)
        finally:
            with contextlib.suppress(OSError):
                gate.unlink(missing_ok=True)
        if not integrated:
            for section in accepted:
                _discard_section_artifacts(section.path)
            failures.append(
                RepairRequest(
                    "Semantically accepted Phase-1 candidates conflict when "
                    "imported together:\n" + output[-12000:],
                    [label for section in accepted for label in section.labels],
                    section_labels=[
                        label for section in accepted for label in section.labels
                    ],
                    authorizes_blueprint_repair=False,
                )
            )
            accepted = []

    for section in accepted:
        section.refined_labels = set(section.labels)
        _note_frozen_section(ctx, section.labels)

    if failures:
        raise _aggregate_retry_requests(
            failures,
            frozen_sections=accepted,
        )
    return accepted


def _compile_semantic_phase1_candidate(
    ctx: Ctx,
    candidate: Phase1LayerCandidate,
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    layer_no: int,
) -> tuple[list[Section] | None, str, str]:
    """Typecheck one generated contract candidate without auditing it."""
    evidence: list[str] = []
    failed_code: list[str] = []
    result = _freeze_section_from_code(
        ctx,
        candidate.labels,
        sections,
        alloc,
        [decl.text for decl in candidate.parsed.decls],
        list(candidate.parsed.imports),
        list(candidate.parsed.preamble),
        origin=f"validated-contract layer {layer_no}",
        allow_patch=True,
        generation_tier=candidate.generation_tier,
        failure_evidence=evidence,
        failure_candidate_code=failed_code,
        route_plan_defects=True,
        defer_object_gate=True,
    )
    return (
        result,
        "\n\n".join(evidence) or "candidate did not compile",
        failed_code[-1]
        if failed_code
        else _phase1_layer_candidate_code(candidate),
    )


def _materialized_phase1_candidate(
    candidate: Phase1LayerCandidate, module_code: str
) -> Phase1LayerCandidate:
    """Rebuild a candidate from the exact post-patch module that Lean saw."""
    parsed = _parse_module(module_code)
    generated_imports = {
        f"import {module}" for module in candidate.import_modules
    }
    return Phase1LayerCandidate(
        labels=list(candidate.labels),
        parsed=ParsedModule(
            imports=[
                item for item in parsed.imports if item not in generated_imports
            ],
            preamble=list(parsed.preamble),
            decls=[
                DeclBlock(decl.kind, decl.name, decl.text)
                for decl in parsed.decls
            ],
        ),
        import_modules=list(candidate.import_modules),
        generation_tier=candidate.generation_tier,
        sessions=candidate.sessions,
        plan_fps=dict(candidate.plan_fps),
    )


def _compile_phase1_candidate_preserving_attributed_siblings(
    ctx: Ctx,
    candidate: Phase1LayerCandidate,
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    layer_no: int,
) -> tuple[
    list[Section],
    list[tuple[Phase1LayerCandidate, str, str]],
]:
    """Compile one candidate and retain code outside attributed failures.

    Diagnostic attribution previously scoped retry counters but ran only after
    the all-or-nothing freezer had discarded the generated section. Split the
    exact post-patch module at the same declaration/helper ownership boundary,
    recheck the unaffected subset through every deterministic and Lean gate,
    and return only the true failure owners to the existing router. If the
    diagnostics or helper ownership are ambiguous, preserve the old whole-unit
    route.
    """
    result, evidence, failed_code = _compile_semantic_phase1_candidate(
        ctx,
        candidate,
        sections,
        alloc,
        layer_no=layer_no,
    )
    if result is not None:
        return result, []

    materialized = _materialized_phase1_candidate(candidate, failed_code)
    scoped = _compiler_generation_evidence_by_label(
        ctx, materialized.labels, failed_code, evidence
    )
    failed_labels = [
        label for label in materialized.labels if label in scoped
    ]
    preserved_labels = [
        label for label in materialized.labels if label not in scoped
    ]
    if not failed_labels or not preserved_labels:
        return [], [(materialized, evidence, failed_code)]

    failed_subset = _subset_phase1_candidate(ctx, materialized, failed_labels)
    preserved_subset = _subset_phase1_candidate(
        ctx, materialized, preserved_labels
    )
    if failed_subset is None or preserved_subset is None:
        return [], [(materialized, evidence, failed_code)]

    accepted, remaining = _compile_phase1_candidate_preserving_attributed_siblings(
        ctx,
        preserved_subset,
        sections,
        alloc,
        layer_no=layer_no,
    )
    owner_evidence = "\n\n".join(
        scoped[label] for label in failed_labels if scoped.get(label)
    ) or evidence
    owner_code = _phase1_layer_candidate_code(failed_subset)
    _record(
        ctx.telemetry,
        "phase1_compile_candidate_siblings_preserved",
        layer=layer_no,
        failed_labels=failed_labels,
        preserved_labels=preserved_labels,
        accepted_labels=[
            label for section in accepted for label in section.labels
        ],
        generation_tier=candidate.generation_tier,
    )
    return accepted, [(failed_subset, owner_evidence, owner_code), *remaining]


def _compile_semantic_phase1_candidates(
    ctx: Ctx,
    candidates: list[Phase1LayerCandidate],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    layer_no: int,
) -> list[Section]:
    """Typecheck contract candidates in parallel before final auditing."""
    if not candidates:
        return []
    worker_count = max(1, min(getattr(ctx, "workers", 1), len(candidates)))
    _log(
        f"==> {_contract_work_stage(ctx)} layer {layer_no}: compiling {len(candidates)} "
        f"validated-contract candidate group(s) with {worker_count} worker(s)"
    )
    results: list[list[Section] | None] = [None] * len(candidates)
    failures: list[tuple[int, RepairRequest]] = []
    old_defer = getattr(ctx, "defer_phase1_alignment", False)
    ctx.defer_phase1_alignment = True
    try:
        def compile_one(
            index: int, candidate: Phase1LayerCandidate
        ) -> tuple[
            int,
            list[Section],
            list[tuple[Phase1LayerCandidate, str, str]],
        ]:
            accepted, failed = (
                _compile_phase1_candidate_preserving_attributed_siblings(
                    ctx,
                    candidate,
                    sections,
                    alloc,
                    layer_no=layer_no,
                )
            )
            return index, accepted, failed

        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
            futures = [
                pool.submit(compile_one, index, candidate)
                for index, candidate in enumerate(candidates)
            ]
            for future in concurrent.futures.as_completed(futures):
                index, accepted, failed_outcomes = future.result()
                results[index] = accepted or None
                for failed_candidate, evidence, failed_code in failed_outcomes:
                    # Route each completed owner component while unrelated
                    # workers are still compiling. Candidate preservation has
                    # already rerun the normal gates on unaffected siblings.
                    failures.append(
                        (
                            index,
                            _route_phase1_compile_failure(
                                ctx,
                                failed_candidate,
                                evidence,
                                failed_code,
                                layer_no=layer_no,
                            ),
                        )
                    )
    finally:
        ctx.defer_phase1_alignment = old_defer

    compiled = [section for result in results if result for section in result]
    if failures:
        failures.sort(key=lambda item: item[0])
        requests = [request for _index, request in failures]
        _record(
            ctx.telemetry,
            "phase1_parallel_compile_failures",
            layer=layer_no,
            failure_count=len(requests),
            failing_groups=[request.section_labels for request in requests],
            accepted_labels=[
                label for section in compiled for label in section.labels
            ],
        )
        authorized = [
            request for request in requests if request.authorizes_blueprint_repair
        ]
        if authorized:
            raise _aggregate_authorized_repair_requests(
                authorized, frozen_sections=compiled
            )
        raise _aggregate_retry_requests(requests, frozen_sections=compiled)
    return compiled


def _compile_and_finalize_semantic_candidates(
    ctx: Ctx,
    candidates: list[Phase1LayerCandidate],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
    *,
    layer_no: int,
) -> list[Section]:
    """Typecheck, audit, object-build, and integrate accepted contracts."""
    try:
        compiled = _compile_semantic_phase1_candidates(
            ctx, candidates, sections, alloc, layer_no=layer_no
        )
    except RepairRequest as request:
        # Parallel compilation can succeed for independent siblings before one
        # candidate fails. They are preservable only after the same integrated
        # import and cache-backed semantic gate as a fully successful layer.
        partial = request.frozen_sections
        request.frozen_sections = []
        if partial:
            try:
                request.frozen_sections = _audit_phase1_layer_candidates(
                    ctx, layer_no, partial, sections, alloc
                )
            except RepairRequest as audit_request:
                if audit_request.authorizes_blueprint_repair:
                    raise
                raise _aggregate_retry_requests(
                    [request, audit_request],
                    frozen_sections=audit_request.frozen_sections,
                )
        raise
    if not compiled:
        return []
    return _audit_phase1_layer_candidates(
        ctx, layer_no, compiled, sections, alloc
    )


def _refine_statement_group(
    ctx: Ctx,
    sec: Section,
    labels: list[str],
    sections: list[Section],
) -> None:
    """Refine selected declarations without exposing failed candidates.

    Every deterministic/model/Lean gate runs against a disposable attempt file.
    The canonical skeleton is replaced atomically only after all gates pass.
    """
    existing_code = sec.path.read_text(encoding="utf-8")
    parsed = _canonicalize_model_lean(
        ctx, sec.labels, existing_code, strict_duplicates=False
    ).parsed
    index = {
        decl.name: position
        for position, decl in enumerate(parsed.decls)
        if decl.name
    }
    # Heal state written by older versions of the Phase-1 loop. Self-imports
    # can never be valid and duplicate names can only make Lean reject a module.
    self_import = f"import {sec.module}"
    parsed.imports = [item for item in parsed.imports if item != self_import]
    seen_existing: set[str] = set()
    healed_decls: list[DeclBlock] = []
    for decl in parsed.decls:
        if decl.name and decl.name in seen_existing:
            continue
        if decl.name:
            seen_existing.add(decl.name)
        healed_decls.append(decl)
    parsed.decls = healed_decls
    missing = [label for label in labels if _lean_name(label) not in index]
    if missing:
        raise RepairRequest(
            "Initial declaration pass omitted required generated names: "
            + ", ".join(missing),
            missing,
            section_labels=labels,
        )
    import_modules = [module for module in sec.import_modules if module != sec.module]
    # The file may also contain provisional theorem declarations from lower
    # layers. Their terminal ``sorry`` is legal until their own Phase-1 turn.
    target_kinds = _phase1_target_kinds(ctx, sec.labels)
    label_by_name = {_lean_name(label): label for label in sec.labels}
    sessions: dict[str, str] = {}
    # Rollback uses the deterministically healed baseline, allowing --continue
    # to recover files poisoned by the pre-transaction implementation.
    original_code, _original_ranges = _compose_module(
        parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
    )
    attempt_dir = SCRATCH_DIR / ctx.name / "phase1-attempts"
    attempt_dir.mkdir(parents=True, exist_ok=True)
    attempt_path = attempt_dir / sec.path.name

    _log(
        f"==> {_contract_work_stage(ctx)}: generating exact statements for {len(labels)} "
        "provisional declaration(s)"
    )
    parsed = _generate_phase1_statement_group(
        ctx,
        sec,
        labels,
        sections,
        import_modules,
        parsed,
        force_first_escalated=bool(
            len(labels) == 1
            and _retry_next_tier(ctx, labels[0], "phase1_statement")
            == "escalation"
        ),
    )

    def current_code() -> str:
        code, _ranges = _compose_module(
            parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
        )
        return code

    def write_attempt() -> tuple[str, list[tuple[int, int]]]:
        code, ranges = _compose_module(
            parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
        )
        attempt_path.write_text(code, encoding="utf-8")
        return code, ranges

    module_code = current_code()
    findings = [
        finding
        for finding in _skeleton_code_findings(
            module_code,
            target_kinds,
            label_by_name,
            _planned_helper_owner_by_name(ctx, sec.labels),
        )
        if finding.label is None or finding.label in set(labels)
    ]
    findings += _skeleton_deterministic_findings(module_code, ctx, labels)
    if findings:
        patched, note = _targeted_patch_skeleton_decls(
            ctx,
            labels,
            sections,
            import_modules,
            parsed,
            module_code,
            findings,
            timeout=ctx.base_timeout,
            sessions=sessions,
        )
        if patched is None:
            raise RepairRequest(
                "Phase 1 could not correct provisional statement contracts: "
                + note
                + "\n"
                + _format_skeleton_findings(findings),
                _patchable_skeleton_labels(findings, labels) or labels,
                section_labels=labels,
                authorizes_blueprint_repair=False,
            )
        parsed = patched
        module_code = current_code()
        findings = [
            finding
            for finding in _skeleton_code_findings(
                module_code,
                target_kinds,
                label_by_name,
                _planned_helper_owner_by_name(ctx, sec.labels),
            )
            if finding.label is None or finding.label in set(labels)
        ]
        findings += _skeleton_deterministic_findings(module_code, ctx, labels)
        if findings:
            attributable = _isolated_deterministic_failure_labels(findings, labels)
            if len(labels) > 1:
                route = _route_lean_generation_failure(
                    labels, attributable if attributable else None
                )
                raise RepairRequest(
                    "Phase 1 statement correction still failed deterministic gates:\n"
                    + _format_skeleton_findings(findings),
                    list(route.failed_labels),
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                    failure_route=route,
                )
            patched, note = _targeted_patch_skeleton_decls(
                ctx,
                labels,
                sections,
                import_modules,
                parsed,
                module_code,
                findings,
                timeout=ctx.hard_timeout,
                sessions=sessions,
                escalated=True,
            )
            if patched is None:
                raise RepairRequest(
                    "Phase 1 statement correction still failed deterministic gates: "
                    + note
                    + "\n"
                    + _format_skeleton_findings(findings),
                    _patchable_skeleton_labels(findings, labels) or labels,
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                )
            parsed = patched
            module_code = current_code()
            findings = [
                finding
                for finding in _skeleton_code_findings(
                    module_code,
                    target_kinds,
                    label_by_name,
                    _planned_helper_owner_by_name(ctx, sec.labels),
                )
                if finding.label is None or finding.label in set(labels)
            ]
            findings += _skeleton_deterministic_findings(
                module_code, ctx, labels
            )
            if findings:
                raise RepairRequest(
                    "Phase 1 statement correction remained invalid after escalation:\n"
                    + _format_skeleton_findings(findings),
                    _patchable_skeleton_labels(findings, labels) or labels,
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                )

    module_code, ranges = write_attempt()
    ok, output = _check_lean(attempt_path, ctx.lean_command)
    # A root statement can elaborate only after every declaration in the
    # shared provisional environment has a valid header. Repair malformed
    # lower scaffolding in small owned batches, retaining ``sorry`` bodies and
    # without marking those nodes refined. Then resume the original root.
    repaired_provisional: set[str] = set()
    while not ok:
        compile_findings = _lean_compile_findings(
            parsed,
            sec.labels,
            ranges,
            output,
            attempt_path.name,
            _planned_helper_owner_by_name(ctx, sec.labels),
        )
        owned = [
            label
            for label in sec.labels
            if any(finding.label == label for finding in compile_findings)
            and label not in repaired_provisional
        ]
        if not owned:
            break
        provisional_owned = [label for label in owned if label not in set(labels)]
        patch_labels = (
            provisional_owned or [label for label in owned if label in set(labels)]
        )[:TARGETED_DECL_PATCH_MAX_LABELS]
        patch_findings = [
            finding for finding in compile_findings if finding.label in set(patch_labels)
        ]
        singleton_patch = len(patch_labels) == 1
        patched, note = _targeted_patch_skeleton_decls(
            ctx,
            sec.labels,
            sections,
            import_modules,
            parsed,
            module_code,
            patch_findings,
            timeout=ctx.hard_timeout if singleton_patch else ctx.base_timeout,
            sessions=sessions,
            escalated=singleton_patch,
            provisional_only=not set(patch_labels) <= set(labels),
            escalate_timeout=singleton_patch,
        )
        if patched is None:
            break
        parsed = patched
        repaired_provisional.update(patch_labels)
        if provisional_owned:
            _record(
                ctx.telemetry,
                "phase1_provisional_scaffolding_repair",
                labels=patch_labels,
                root_labels=labels,
                count=len(patch_labels),
            )
        module_code, ranges = write_attempt()
        ok, output = _check_lean(attempt_path, ctx.lean_command)
    if not ok:
        compile_findings = _lean_compile_findings(
            parsed,
            sec.labels,
            ranges,
            output,
            attempt_path.name,
            _planned_helper_owner_by_name(ctx, sec.labels),
        )
        remaining = [
            label
            for label in sec.labels
            if any(finding.label == label for finding in compile_findings)
        ]
        route = _route_lean_generation_failure(
            labels,
            [label for label in remaining if label in set(labels)] or None,
        )
        raise RepairRequest(
            "Phase 1 provisional environment still does not compile after "
            "repairing declaration-owned scaffolding:\n" + output[-8000:],
            list(route.failed_labels),
            section_labels=labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
            evidence_by_label=_generation_evidence_from_findings(
                route.failed_labels, compile_findings
            ),
        )

    audit = _model_alignment_audit(ctx, labels, module_code, tag="phase1")
    if audit is not None:
        audit = _coerce_alignment_audit_result(audit)
        plan_request = _audit_plan_revision_request(
            ctx,
            audit,
            layer_no=-1,
            source="top_down_alignment",
        )
        if plan_request is not None:
            raise plan_request
        kind, reason, rejected, helpers = audit
        if kind in {"blueprint", "decomposition"}:
            raise RepairRequest(
                reason,
                sorted(rejected),
                decomposition_helpers=helpers if kind == "decomposition" else None,
                section_labels=labels,
            )
        route = _route_lean_generation_failure(labels, rejected)
        if len(labels) > 1:
            raise RepairRequest(
                reason,
                list(route.failed_labels),
                section_labels=labels,
                authorizes_blueprint_repair=False,
                failure_route=route,
            )
        audit_findings = [
            SkeletonFinding(reason, label=label, lean_name=_lean_name(label))
            for label in sorted(rejected)
        ]
        patched, note = _targeted_patch_skeleton_decls(
            ctx,
            labels,
            sections,
            import_modules,
            parsed,
            module_code,
            audit_findings,
            timeout=ctx.hard_timeout,
            sessions=sessions,
            escalated=True,
        )
        if patched is None:
            raise RepairRequest(
                "Phase 1 statement-alignment correction failed: " + note + "\n" + reason,
                sorted(rejected),
                section_labels=labels,
                authorizes_blueprint_repair=False,
            )
        parsed = patched
        module_code, _ranges = write_attempt()
        ok, output = _check_lean(attempt_path, ctx.lean_command)
        if not ok:
            retry_parsed, retry_code, retry_note = (
                _retry_statement_patch_compile_once(
                    ctx,
                    sec.labels,
                    sorted(rejected),
                    sections,
                    import_modules,
                    parsed,
                    module_code,
                    output,
                    attempt_path,
                    sessions=sessions,
                )
            )
            if retry_parsed is None:
                raise RepairRequest(
                    "Phase 1 alignment correction does not compile:\n"
                    + output[-8000:]
                    + "\nOne compiler-feedback correction failed: "
                    + retry_note,
                    sorted(rejected),
                    section_labels=labels,
                    authorizes_blueprint_repair=False,
                )
            parsed = retry_parsed
            module_code = retry_code
        reaudit = _model_alignment_audit(
            ctx, labels, module_code, tag="phase1-post-correction"
        )
        if reaudit is not None:
            reaudit = _coerce_alignment_audit_result(reaudit)
            plan_request = _audit_plan_revision_request(
                ctx,
                reaudit,
                layer_no=-1,
                source="top_down_alignment_post_correction",
            )
            if plan_request is not None:
                raise plan_request
            kind, reason, rejected, helpers = reaudit
            raise RepairRequest(
                reason,
                sorted(rejected),
                decomposition_helpers=helpers if kind == "decomposition" else None,
                section_labels=labels,
                authorizes_blueprint_repair=(kind in {"blueprint", "decomposition"}),
            )

    # All candidate gates passed. Atomically publish the source before building
    # its importable object; an interrupted earlier gate can never corrupt it.
    commit_path = sec.path.with_suffix(".phase1-commit.tmp")
    commit_path.write_text(module_code, encoding="utf-8")
    os.replace(commit_path, sec.path)
    object_attempt = _compile_section_olean(sec, ctx.lean_command, sections)
    if not object_attempt.ok:
        rollback_path = sec.path.with_suffix(".phase1-rollback.tmp")
        rollback_path.write_text(original_code, encoding="utf-8")
        os.replace(rollback_path, sec.path)
        _compile_section_olean(sec, ctx.lean_command, sections)
        route = _route_lean_generation_failure(labels)
        raise RepairRequest(
            "Phase 1 could not compile the refined module object:\n"
            + object_attempt.output[-8000:],
            list(route.failed_labels),
            section_labels=labels,
            authorizes_blueprint_repair=False,
            failure_route=route,
        )
    attempt_path.unlink(missing_ok=True)
    if sec.refined_labels is None:
        sec.refined_labels = set(sec.labels)
    else:
        sec.refined_labels.update(labels)
    _note_frozen_section(ctx, labels)
    _log(
        f"  {_contract_work_stage(ctx)} froze {len(labels)} top-down statement contract(s): "
        + ", ".join(labels[:6])
        + ("..." if len(labels) > 6 else "")
    )
    _record(
        ctx.telemetry,
        "phase1_statement_refined",
        section=sec.number,
        labels=labels,
        count=len(labels),
    )


def _phase1_candidate_code(candidates: list[Section]) -> str:
    """Collect target declarations for one layer-wide semantic audit."""
    declarations: list[str] = []
    for section in candidates:
        parsed, _index = _module_decl_texts(section)
        declarations.extend(decl.text for decl in parsed.decls)
    return "\n\n".join(declarations)


def _patch_phase1_candidate_section(
    ctx: Ctx,
    section: Section,
    rejected: set[str],
    reason: str,
) -> bool:
    """Patch only audit-rejected declarations in one compiled candidate."""
    local_rejected = [label for label in section.labels if label in rejected]
    if not local_rejected:
        return True
    original = section.path.read_text(encoding="utf-8")
    parsed = _parse_module(original)
    findings = [
        SkeletonFinding(reason, label=label, lean_name=_lean_name(label))
        for label in local_rejected
    ]
    patched, _note = _targeted_patch_skeleton_decls(
        ctx,
        section.labels,
        [],
        section.import_modules,
        parsed,
        original,
        findings,
        timeout=ctx.hard_timeout,
        sessions={},
        escalated=True,
    )
    if patched is None:
        return False
    target_kinds = _phase1_target_kinds(ctx, section.labels)
    for decl in patched.decls:
        if _may_defer_target_body(decl, target_kinds.get(decl.name or "")):
            decl.text = _normalize_terminal_sorry(decl.text)
    code, _ranges = _compose_module(
        patched.imports, patched.preamble, [decl.text for decl in patched.decls]
    )
    label_by_name = {_lean_name(label): label for label in section.labels}
    deterministic = _skeleton_code_findings(
        code,
        target_kinds,
        label_by_name,
        _planned_helper_owner_by_name(ctx, section.labels),
    )
    deterministic += _skeleton_deterministic_findings(code, ctx, section.labels)
    if deterministic:
        return False
    section.path.write_text(code, encoding="utf-8")
    ok, output = _check_lean(section.path, ctx.lean_command)
    if not ok:
        retry_parsed, retry_code, _retry_note = (
            _retry_statement_patch_compile_once(
                ctx,
                section.labels,
                local_rejected,
                [],
                section.import_modules,
                patched,
                code,
                output,
                section.path,
                sessions={},
            )
        )
        if retry_parsed is None:
            section.path.write_text(original, encoding="utf-8")
            return False
        patched = retry_parsed
        code = retry_code
    object_attempt = _compile_section_olean(section, ctx.lean_command)
    if not object_attempt.ok:
        section.path.write_text(original, encoding="utf-8")
        return False
    return True


def _expand_rejected_section_components(
    ctx: Ctx, candidates: list[Section], rejected: set[str]
) -> set[str]:
    """Keep every shared-helper component atomic after a critic rejection."""
    expanded = set(rejected)
    for section in candidates:
        if not (set(section.labels) & expanded) or not section.path.is_file():
            continue
        parsed = _parse_module(section.path.read_text(encoding="utf-8"))
        target_by_name = {_lean_name(label): label for label in section.labels}
        for component in _target_components_from_helpers(
            parsed,
            target_by_name,
            _planned_helper_owner_by_name(ctx, section.labels),
        ):
            if component & expanded:
                expanded.update(component)
    return expanded


def _route_phase1_representation_repairs(
    ctx: Ctx,
    audit: AlignmentAuditResult,
    decomposition_labels: set[str],
    *,
    layer_no: int,
    source: str,
) -> set[str]:
    """Route complete representation certificates through one shared boundary."""
    labels = audit.representation_repair_labels(
        "extension_certificate"
    ) & decomposition_labels
    if not labels:
        return set()
    _record(
        ctx.telemetry,
        "phase1_representation_repair_routed",
        layer=layer_no,
        source=source,
        labels=sorted(labels),
        kind="extension_certificate",
        route="transactional_blueprint_decomposition",
        repairs={
            label: audit.representation_repairs_by_label[label]
            for label in sorted(labels)
        },
        avoided_route="plan_revision_and_statement_retry",
    )
    _log(
        "  inherited/new-data scope mismatch requires an explicit "
        "blueprint extension certificate: " + ", ".join(sorted(labels))
    )
    return labels


def _audit_phase1_layer_candidates(
    ctx: Ctx,
    layer_no: int,
    candidates: list[Section],
    existing_sections: list[Section] | None = None,
    alloc: _SectionNumberAllocator | None = None,
) -> list[Section]:
    """Audit typechecked candidates, then object-build and integrate accepted ones.

    Semantic-first callers have already cached a verdict for each candidate.
    The cache key includes the target declaration and its owned helpers, so the
    audit call is free when compilation changed nothing and judges only
    contracts changed by a compiler-driven patch otherwise. Every accepted
    declaration still passes object generation and the integrated import gate
    before it is marked frozen.
    """
    if not candidates:
        return []
    labels = [label for section in candidates for label in section.labels]

    _log(
        f"==> {_contract_work_stage(ctx)} layer {layer_no}: checking {len(labels)} integrated "
        "declaration(s); unchanged semantic verdicts are reused"
    )
    audit = _model_alignment_audit(
        ctx, labels, _phase1_candidate_code(candidates), tag=f"layer-{layer_no}"
    )
    if audit is None:
        accepted = _finalize_phase1_accepted_sections(
            ctx, layer_no, candidates, existing_sections
        )
        _record(
            ctx.telemetry,
            "phase1_layer_frozen",
            layer=layer_no,
            labels=labels,
            sections=len(accepted),
        )
        _log(
            f"  {_contract_work_stage(ctx)} layer {layer_no} frozen "
            f"({len(labels)} declaration(s), {len(accepted)} section(s))"
        )
        return accepted

    audit = _coerce_alignment_audit_result(audit)
    kind, reason, rejected, helpers = audit
    confirmed_required_dependencies = _confirmed_phase1_dependency_observations(
        ctx, audit.required_dependencies
    )
    dependency_repair_labels = set(confirmed_required_dependencies)
    lean_rejected = audit.labels_for("lean-generation") - dependency_repair_labels
    decomposition_rejected = (
        audit.labels_for("decomposition") - dependency_repair_labels
    )
    blueprint_rejected = audit.labels_for("blueprint") - dependency_repair_labels
    certificate_repairs = _route_phase1_representation_repairs(
        ctx,
        audit,
        decomposition_rejected,
        layer_no=layer_no,
        source="integrated_alignment",
    )
    plan_revised = _revise_decomposition_plans_once(
        ctx,
        decomposition_rejected - certificate_repairs,
        audit.reason_for(sorted(decomposition_rejected - certificate_repairs)),
        layer_no=layer_no,
        source="integrated_alignment",
    )
    decomposition_rejected.difference_update(plan_revised)
    reported_plan_defects = _revise_audit_reported_plan_defects(
        ctx,
        audit,
        layer_no=layer_no,
        source="integrated_alignment",
        skip_labels=dependency_repair_labels,
    )
    if reported_plan_defects:
        plan_revised.update(reported_plan_defects)
        lean_rejected.difference_update(reported_plan_defects)
    candidate_plan_defects = _activate_audit_reported_candidate_plan_defects(
        ctx,
        audit,
        layer_no=layer_no,
        source="integrated_alignment",
        skip_labels=dependency_repair_labels,
    )
    if candidate_plan_defects:
        plan_revised.update(candidate_plan_defects)
        lean_rejected.difference_update(candidate_plan_defects)
    # A compiling candidate that exactly realizes every public surface in its
    # accepted plan cannot repair a semantic omission by being regenerated
    # under that unchanged plan. Correct the plan immediately from the audit
    # evidence instead of paying for an escalation candidate and the same
    # audit a second time. Conservative exact matching leaves all ambiguous
    # cases on the existing generation-retry lifecycle.
    realized_plan_defects = _plan_realized_semantic_rejections(
        ctx, lean_rejected, _phase1_candidate_code(candidates)
    )
    if realized_plan_defects:
        evidence_identities = {
            label: audit.failure_identity_for(label)
            for label in realized_plan_defects
            if audit.failure_identity_for(label)
        }
        revision_kwargs = (
            {"evidence_identities_by_label": evidence_identities}
            if evidence_identities
            else {}
        )
        immediately_revised = _revise_exhausted_phase1_contracts(
            ctx,
            realized_plan_defects,
            audit.reason_for(sorted(realized_plan_defects)),
            **revision_kwargs,
        )
        if immediately_revised:
            plan_revised.update(immediately_revised)
            lean_rejected.difference_update(immediately_revised)
            _record(
                ctx.telemetry,
                "phase1_plan_realized_semantic_rejection",
                layer=layer_no,
                labels=sorted(immediately_revised),
                route="immediate_plan_revision",
                additional_calls_vs_existing_exhaustion_route=0,
                replacement_call="phase1_design_plan_correction",
                avoided_route="unchanged_plan_generation_retry",
            )
            _log(
                "  compiling candidate exactly realized its rejected plan; "
                "revised the plan before regeneration: "
                + ", ".join(sorted(immediately_revised))
            )
    repair_rejected = decomposition_rejected | blueprint_rejected
    audit_required_dependencies = getattr(
        audit, "required_dependencies", {}
    )
    expanded_rejected = _expand_rejected_section_components(
        ctx, candidates, rejected
    )
    if expanded_rejected != rejected:
        _record(
            ctx.telemetry,
            "phase1_shared_helper_component_expanded",
            layer=layer_no,
            critic_rejected_labels=sorted(rejected),
            component_labels=sorted(expanded_rejected),
        )
        rejected = expanded_rejected
    request_labels = set(rejected)
    failure_route: FailureScopeDecision | None = None
    if lean_rejected:
        semantic_evidence_by_label = {
            label: audit.reason_for([label]) for label in lean_rejected
        }
        for section in candidates:
            section_rejected = lean_rejected & set(section.labels)
            if section_rejected:
                _store_generation_candidates(
                    ctx,
                    section_rejected,
                    section.path.read_text(encoding="utf-8"),
                    source=f"phase1_layer_{layer_no}_alignment",
                    all_labels=section.labels,
                    repair_stage="semantic_rejected",
                    required_dependencies=audit_required_dependencies,
                    lean_status="passed",
                    semantic_status="rejected",
                    semantic_evidence_by_label=semantic_evidence_by_label,
                    semantic_evidence_identity_by_label={
                        label: audit.failure_identity_for(label)
                        for label in section_rejected
                    },
                )
        tier_by_label = {
            label: (
                section.generation_tier
                if section.generation_tier in {"base", "escalation"}
                else _retry_next_tier(ctx, label, "phase1_statement")
            )
            for section in candidates
            for label in section.labels
            if label in lean_rejected
        }
        exhausted: set[str] = set()
        for tier in ("base", "escalation"):
            tier_labels = [
                label for label in labels
                if label in lean_rejected and tier_by_label.get(label, "base") == tier
            ]
            if tier_labels:
                for label in tier_labels:
                    exhausted.update(
                        _record_retry_failure(
                            ctx,
                            [label],
                            stage="phase1_statement",
                            attempted_tier=tier,
                            evidence=semantic_evidence_by_label[label],
                            source=f"phase1_layer_{layer_no}_alignment",
                            evidence_identity=audit.failure_identity_for(label),
                        )
                    )
        _store_generation_feedback(
            ctx,
            lean_rejected,
            reason,
            source="statement_alignment",
            evidence_by_label=semantic_evidence_by_label,
            evidence_identity_by_label={
                label: audit.failure_identity_for(label)
                for label in lean_rejected
            },
        )
        _quarantine_labels(ctx, lean_rejected, "statement_alignment")
        if exhausted:
            decomposition_after_revision, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    exhausted,
                    reason,
                    layer_no=layer_no,
                    source="integrated_alignment",
                    evidence_by_label={
                        label: audit.reason_for([label])
                        for label in exhausted
                    },
                    evidence_identities_by_label={
                        label: audit.failure_identity_for(label)
                        for label in exhausted
                        if audit.failure_identity_for(label)
                    },
                )
            )
            if decomposition_after_revision:
                decomposition_rejected.update(decomposition_after_revision)
                repair_rejected.update(decomposition_after_revision)
            if revised:
                kind = "plan-revised"
                request_labels = revised
                failure_route = FailureScopeDecision(
                    action="independent",
                    parts=tuple((label,) for label in sorted(revised)),
                    failed_labels=tuple(sorted(revised)),
                    accepted_labels=(),
                )
            if unresolved:
                kind = "generation-exhausted"
                request_labels = set(unresolved) | set(revised)
                failure_route = None
                _log(
                    f"  {_contract_work_stage(ctx)} layer {layer_no}: retry lifecycle exhausted for "
                    + ", ".join(sorted(unresolved))
                    + "; consuming bounded generation retry budget without editing "
                    "the blueprint"
                )
        else:
            ordered_rejected = tuple(label for label in labels if label in lean_rejected)
            failure_route = FailureScopeDecision(
                action="independent",
                parts=tuple((label,) for label in ordered_rejected),
                failed_labels=ordered_rejected,
                accepted_labels=tuple(label for label in labels if label not in rejected),
            )
            _log(
                f"  {_contract_work_stage(ctx)} layer {layer_no}: preserving {len(lean_rejected)} "
                "independent retry lifecycle(s); next attempts start at "
                "the escalation tier"
            )
        _record(
            ctx.telemetry,
            "lean_generation_failure_routed",
            stage="phase1_alignment",
            action=(failure_route.action if failure_route else "exhausted"),
            labels=labels,
            failing_labels=sorted(lean_rejected),
            accepted_labels=[label for label in labels if label not in rejected],
            part_sizes=(
                [len(part) for part in failure_route.parts]
                if failure_route
                else [1 for _label in lean_rejected]
            ),
            layer=layer_no,
            candidate_tiers=tier_by_label,
        )

    # A single audit may contain unrelated Lean-translation failures and
    # missing blueprint interfaces. Preserve the former's candidates and retry
    # state above, but immediately route only the independently authorized
    # blueprint/decomposition subset to the transactional blueprint repair.
    if repair_rejected:
        request_labels = set(repair_rejected)
        kind = "decomposition" if decomposition_rejected else "blueprint"
        reason = audit.reason_for(sorted(repair_rejected))
        helpers = audit.helpers_for(sorted(decomposition_rejected))
        if decomposition_rejected and not helpers:
            helpers = [
                "introduce explicit blueprint definitions or lemmas for the "
                "mathematical interfaces named by the repeated contract rejection"
            ]
        failure_route = None
        _record(
            ctx.telemetry,
            "phase1_mixed_alignment_routed",
            layer=layer_no,
            repair_labels=sorted(repair_rejected),
            decomposition_labels=sorted(decomposition_rejected),
            blueprint_labels=sorted(blueprint_rejected),
            deferred_lean_labels=sorted(lean_rejected),
        )
    elif lean_rejected:
        kind = "lean-generation" if kind == "mixed" else kind
        request_labels = set(request_labels) & set(lean_rejected)

    if plan_revised and not repair_rejected:
        revision_route = FailureScopeDecision(
            action="independent",
            parts=tuple((label,) for label in sorted(plan_revised)),
            failed_labels=tuple(sorted(plan_revised)),
            accepted_labels=(),
        )
        failure_route = (
            _combine_failure_routes([failure_route, revision_route])
            if failure_route is not None
            else revision_route
        )
        request_labels.update(plan_revised)
        if not lean_rejected:
            kind = "plan-revised"
            reason = audit.reason_for(sorted(plan_revised))

    accepted: list[Section] = []
    discarded_labels: set[str] = set()
    for section in candidates:
        section_rejected = rejected & set(section.labels)
        if section_rejected:
            retained_labels = [
                label for label in section.labels if label not in section_rejected
            ]
            retained: list[Section] | None = None
            if retained_labels and alloc is not None:
                parsed = _parse_module(section.path.read_text(encoding="utf-8"))
                decl_texts = _delivered_decl_texts(
                    parsed,
                    retained_labels,
                    {_lean_name(label) for label in section.labels},
                    _planned_helper_owner_by_name(ctx, section.labels),
                )
                if decl_texts:
                    # The layer critic already accepted these declarations.
                    # Rebuild them without the rejected siblings and rerun all
                    # deterministic and Lean gates, but do not pay for another
                    # semantic audit. If a retained declaration secretly used
                    # a rejected sibling or shared helper, Lean rejects the
                    # extraction and the normal regeneration fallback remains.
                    old_defer = getattr(ctx, "defer_phase1_alignment", False)
                    ctx.defer_phase1_alignment = True
                    try:
                        retained = _freeze_section_from_code(
                            ctx,
                            retained_labels,
                            list(existing_sections or []) + accepted,
                            alloc,
                            decl_texts,
                            list(parsed.imports),
                            list(parsed.preamble),
                            origin="accepted layer siblings",
                            defer_object_gate=True,
                        )
                    finally:
                        ctx.defer_phase1_alignment = old_defer
            _discard_section_artifacts(section.path)
            if retained:
                accepted.extend(retained)
                discarded_labels.update(section_rejected)
                _log(
                    f"  retained {len(retained_labels)} accepted declaration(s) "
                    f"beside {len(section_rejected)} rejected sibling(s)"
                )
                _record(
                    ctx.telemetry,
                    "phase1_partial_section_retained",
                    layer=layer_no,
                    retained_labels=retained_labels,
                    rejected_labels=sorted(section_rejected),
                    source_section=section.number,
                )
            else:
                discarded_labels.update(section.labels)
            continue
        accepted.append(section)
    _record(
        ctx.telemetry,
        "phase1_layer_rejected",
        layer=layer_no,
        labels=labels,
        rejected_labels=sorted(rejected),
        discarded_labels=sorted(discarded_labels),
        accepted_labels=[label for sec in accepted for label in sec.labels],
        classification=kind,
    )
    semantic_request = RepairRequest(
        reason,
        sorted(request_labels),
        decomposition_helpers=helpers if kind == "decomposition" else None,
        # Normalization is an editing operation, so its scope must match the
        # exact contracts authorized for repair. In a mixed-tier rejection,
        # other rejected siblings retain their independent escalation state.
        section_labels=sorted(request_labels),
        context_labels=sorted(discarded_labels or rejected),
        frozen_sections=accepted,
        authorizes_blueprint_repair=kind in {
            "blueprint",
            "decomposition",
        },
        failure_route=(
            failure_route
            if kind in {"lean-generation", "plan-revised"}
            else None
        ),
        required_dependencies={
            label: dependencies
            for label, dependencies in audit_required_dependencies.items()
            if label not in plan_revised
        },
        model_repair_labels=sorted(
            decomposition_rejected
            | (blueprint_rejected - set(audit_required_dependencies))
        ),
        evidence_by_label={
            label: audit.reason_for([label]) for label in request_labels
        },
        evidence_identities_by_label={
            label: audit.failure_identity_for(label)
            for label in request_labels
            if audit.failure_identity_for(label)
        },
    )
    try:
        semantic_request.frozen_sections = _finalize_phase1_accepted_sections(
            ctx,
            layer_no,
            accepted,
            existing_sections,
        )
    except RepairRequest as object_request:
        if _requires_blueprint_transaction(
            semantic_request.authorizes_blueprint_repair,
            semantic_request.required_dependencies,
        ):
            # The authorized semantic repair owns this outer transaction. The
            # object failure has already persisted its exact candidate and
            # evidence for the next unaffected-contract retry.
            semantic_request.frozen_sections = list(
                object_request.frozen_sections
            )
            raise semantic_request
        raise _aggregate_retry_requests(
            [semantic_request, object_request],
            frozen_sections=object_request.frozen_sections,
        )
    raise semantic_request


def _semantic_first_failure_request(
    ctx: Ctx,
    layer_no: int,
    candidates: list[Phase1LayerCandidate],
    audit: AlignmentAuditResult,
    frozen: list[Section],
) -> RepairRequest:
    """Route a semantic-first rejection while retaining independently accepted work."""
    audit = _coerce_alignment_audit_result(audit)
    kind, reason, rejected, helpers = audit
    confirmed_required_dependencies = _confirmed_phase1_dependency_observations(
        ctx, audit.required_dependencies
    )
    dependency_repair_labels = set(confirmed_required_dependencies)
    lean_rejected = audit.labels_for("lean-generation") - dependency_repair_labels
    decomposition_rejected = (
        audit.labels_for("decomposition") - dependency_repair_labels
    )
    blueprint_rejected = audit.labels_for("blueprint") - dependency_repair_labels
    certificate_repairs = _route_phase1_representation_repairs(
        ctx,
        audit,
        decomposition_rejected,
        layer_no=layer_no,
        source="semantic_first_alignment",
    )
    plan_revised = _revise_decomposition_plans_once(
        ctx,
        decomposition_rejected - certificate_repairs,
        audit.reason_for(sorted(decomposition_rejected - certificate_repairs)),
        layer_no=layer_no,
        source="semantic_first_alignment",
    )
    decomposition_rejected.difference_update(plan_revised)
    reported_plan_defects = _revise_audit_reported_plan_defects(
        ctx,
        audit,
        layer_no=layer_no,
        source="semantic_first_alignment",
        skip_labels=dependency_repair_labels,
    )
    if reported_plan_defects:
        plan_revised.update(reported_plan_defects)
        lean_rejected.difference_update(reported_plan_defects)
    candidate_plan_defects = _activate_audit_reported_candidate_plan_defects(
        ctx,
        audit,
        layer_no=layer_no,
        source="semantic_first_alignment",
        skip_labels=dependency_repair_labels,
    )
    if candidate_plan_defects:
        plan_revised.update(candidate_plan_defects)
        lean_rejected.difference_update(candidate_plan_defects)
    repair_rejected = decomposition_rejected | blueprint_rejected
    audit_required_dependencies = getattr(
        audit, "required_dependencies", {}
    )
    request_labels = set(rejected)
    failure_route: FailureScopeDecision | None = None
    if lean_rejected:
        semantic_evidence_by_label = {
            label: audit.reason_for([label]) for label in lean_rejected
        }
        tier_by_label = {
            label: candidate.generation_tier
            for candidate in candidates
            for label in candidate.labels
            if label in lean_rejected
        }
        exhausted: set[str] = set()
        for tier in ("base", "escalation"):
            tier_labels = [
                label
                for label in sorted(lean_rejected)
                if tier_by_label.get(label, "base") == tier
            ]
            if tier_labels:
                for label in tier_labels:
                    exhausted.update(
                        _record_retry_failure(
                            ctx,
                            [label],
                            stage="phase1_statement",
                            attempted_tier=tier,
                            evidence=semantic_evidence_by_label[label],
                            source=f"phase1_layer_{layer_no}_semantic_first",
                            evidence_identity=audit.failure_identity_for(label),
                        )
                    )
        for candidate in candidates:
            local = lean_rejected & set(candidate.labels)
            if local:
                _store_generation_candidates(
                    ctx,
                    local,
                    _phase1_layer_candidate_code(candidate),
                    source=f"phase1_layer_{layer_no}_semantic_first",
                    all_labels=candidate.labels,
                    repair_stage="semantic_rejected",
                    required_dependencies=audit_required_dependencies,
                    semantic_status="rejected",
                    semantic_evidence_by_label=semantic_evidence_by_label,
                    semantic_evidence_identity_by_label={
                        label: audit.failure_identity_for(label)
                        for label in local
                    },
                )
        _store_generation_feedback(
            ctx,
            lean_rejected,
            reason,
            source="semantic_first_statement_alignment",
            evidence_by_label=semantic_evidence_by_label,
            evidence_identity_by_label={
                label: audit.failure_identity_for(label)
                for label in lean_rejected
            },
        )
        _quarantine_labels(ctx, lean_rejected, "statement_alignment")
        if exhausted:
            decomposition_after_revision, revised, unresolved = (
                _route_exhausted_phase1_semantics(
                    ctx,
                    exhausted,
                    reason,
                    layer_no=layer_no,
                    source="semantic_first_alignment",
                    evidence_by_label={
                        label: audit.reason_for([label])
                        for label in exhausted
                    },
                    evidence_identities_by_label={
                        label: audit.failure_identity_for(label)
                        for label in exhausted
                        if audit.failure_identity_for(label)
                    },
                )
            )
            if decomposition_after_revision:
                decomposition_rejected.update(decomposition_after_revision)
                repair_rejected.update(decomposition_after_revision)
            if revised:
                kind = "plan-revised"
                request_labels = revised
                failure_route = FailureScopeDecision(
                    action="independent",
                    parts=tuple((label,) for label in sorted(revised)),
                    failed_labels=tuple(sorted(revised)),
                    accepted_labels=(),
                )
            if unresolved:
                kind = "generation-exhausted"
                request_labels = set(unresolved) | set(revised)
                failure_route = None
                _log(
                    f"  {_contract_work_stage(ctx)} layer {layer_no}: retry lifecycle exhausted for "
                    + ", ".join(sorted(unresolved))
                    + "; consuming bounded generation retry budget without editing "
                    "the blueprint"
                )
        else:
            ordered = tuple(
                label
                for candidate in candidates
                for label in candidate.labels
                if label in lean_rejected
            )
            failure_route = FailureScopeDecision(
                action="independent",
                parts=tuple((label,) for label in ordered),
                failed_labels=ordered,
                accepted_labels=(),
            )
    if repair_rejected:
        request_labels = set(repair_rejected)
        kind = "decomposition" if decomposition_rejected else "blueprint"
        reason = audit.reason_for(sorted(repair_rejected))
        helpers = audit.helpers_for(sorted(decomposition_rejected))
        if decomposition_rejected and not helpers:
            helpers = [
                "introduce explicit blueprint definitions or lemmas for the "
                "mathematical interfaces named by the repeated contract rejection"
            ]
        failure_route = None
        _record(
            ctx.telemetry,
            "phase1_mixed_alignment_routed",
            layer=layer_no,
            repair_labels=sorted(repair_rejected),
            decomposition_labels=sorted(decomposition_rejected),
            blueprint_labels=sorted(blueprint_rejected),
            deferred_lean_labels=sorted(lean_rejected),
            source="semantic_first_alignment",
        )
    elif lean_rejected:
        kind = "lean-generation" if kind == "mixed" else kind
        request_labels = set(request_labels) & set(lean_rejected)
    if plan_revised and not repair_rejected:
        revision_route = FailureScopeDecision(
            action="independent",
            parts=tuple((label,) for label in sorted(plan_revised)),
            failed_labels=tuple(sorted(plan_revised)),
            accepted_labels=(),
        )
        failure_route = (
            _combine_failure_routes([failure_route, revision_route])
            if failure_route is not None
            else revision_route
        )
        request_labels.update(plan_revised)
        if not lean_rejected:
            kind = "plan-revised"
            reason = audit.reason_for(sorted(plan_revised))
    _record(
        ctx.telemetry,
        "phase1_semantic_first_rejected",
        layer=layer_no,
        labels=[label for candidate in candidates for label in candidate.labels],
        rejected_labels=sorted(rejected),
        accepted_labels=[label for section in frozen for label in section.labels],
        classification=kind,
    )
    return RepairRequest(
        reason,
        sorted(request_labels),
        decomposition_helpers=helpers if kind == "decomposition" else None,
        section_labels=sorted(request_labels),
        context_labels=sorted(rejected),
        frozen_sections=frozen,
        authorizes_blueprint_repair=kind in {
            "blueprint",
            "decomposition",
        },
        failure_route=(
            failure_route
            if kind in {"lean-generation", "plan-revised"}
            else None
        ),
        required_dependencies={
            label: dependencies
            for label, dependencies in audit_required_dependencies.items()
            if label not in plan_revised
        },
        model_repair_labels=sorted(
            decomposition_rejected
            | (blueprint_rejected - set(audit_required_dependencies))
        ),
        evidence_by_label={
            label: audit.reason_for([label]) for label in request_labels
        },
        evidence_identities_by_label={
            label: audit.failure_identity_for(label)
            for label in request_labels
            if audit.failure_identity_for(label)
        },
    )


def _revise_exhausted_phase1_contracts(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    policy: str = "post_semantic_rejection",
    evidence_identities_by_label: Mapping[str, Mapping[str, Any]] | None = None,
) -> set[str]:
    """Revise plan contracts that survived generation but failed semantics.

    Once both generation tiers have emitted a compiling statement and the
    publication critic still rejects it, regenerating under the identical plan
    cannot help. Apply the critic evidence to the untrusted plan once, then
    update candidate plan provenance and reset retry provenance tied to the old
    plan. The compiling candidate remains the correction seed; the blueprint
    remains untouched and every revision still passes the normal deterministic,
    Lean, and semantic gates.
    """
    entries = getattr(ctx, "design_plan_entries", {}) or {}
    eligible = sorted(
        label
        for label in set(labels)
        if label in entries
        and (entries.get(label) or {}).get("origin") != "phase1_candidate"
        and int((entries.get(label) or {}).get("schema_version") or 0)
        == DESIGN_PLAN_SCHEMA_VERSION
    )
    if not eligible:
        return set()
    previous_revision_counts = {
        label: int((entries.get(label) or {}).get("semantic_revision_count") or 0)
        for label in eligible
    }
    # Capture the rejected compiling declaration before plan correction crosses
    # the epoch boundary and removes it. It may be reattached afterwards only
    # as an explicit semantic-correction seed, never as reusable accepted work.
    with _STATE_LOCK:
        candidates = copy.deepcopy(getattr(ctx, "generation_candidates", {}))
    retained_seeds: list[tuple[list[str], str, str, dict[str, set[str]]]] = []
    seen_seed_hashes: set[str] = set()
    reset_candidate_labels: set[str] = set(eligible)
    for label in eligible:
        candidate = candidates.get(label)
        if not isinstance(candidate, dict):
            continue
        component = [
            item
            for item in candidate.get("component_labels") or [label]
            if item in ctx.nodes
        ]
        code = str(candidate.get("code") or "").strip()
        seed_hash = _candidate_hash(code)
        if not code or seed_hash in seen_seed_hashes:
            continue
        seen_seed_hashes.add(seed_hash)
        reset_candidate_labels.update(component)
        seed_code, _ = _compose_module(
            [str(item) for item in candidate.get("imports") or []],
            [str(item) for item in candidate.get("preamble") or []],
            [code],
        )
        retained_seeds.append(
            (
                component,
                seed_code,
                str(candidate.get("generation_tier") or "base"),
                {
                    item: {
                        str(dep)
                        for dep in (candidates.get(item) or {}).get(
                            "required_dependencies"
                        )
                        or []
                    }
                    for item in component
                },
            )
        )

    correction_kwargs = (
        {"evidence_identities_by_label": evidence_identities_by_label}
        if evidence_identities_by_label
        else {}
    )
    if not _correct_phase1_design_plan(
        ctx,
        eligible,
        evidence,
        escalated=True,
        transition_generation_epoch=False,
        **correction_kwargs,
    ):
        return set()

    for label in eligible:
        entries[label]["semantic_revision_count"] = (
            previous_revision_counts[label] + 1
        )

    _transition_phase1_generation_epoch(
        ctx,
        reset_candidate_labels,
        reason="semantic_rejection_plan_revised",
    )
    retained: list[str] = []
    for component, code, tier, required in retained_seeds:
        retained.extend(
            _store_generation_candidates(
                ctx,
                component,
                code,
                source="interface_plan_revised",
                all_labels=component,
                generation_tier=tier,
                repair_stage="semantic_rejected",
                required_dependencies=required,
                semantic_status="rejected",
                semantic_evidence=evidence,
            )
        )
    _record(
        ctx.telemetry,
        "phase1_exhausted_contract_revised",
        labels=eligible,
        evidence=evidence[-4000:],
        policy=policy,
        retained_candidate_labels=retained,
    )
    _log(
        f"  revised rejected {_contract_work_stage(ctx)} contract plan for: "
        + ", ".join(eligible)
        + "; retrying only those nodes under the new contract"
    )
    return set(eligible)


def _revise_decomposition_plans_once(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    layer_no: int,
    source: str,
) -> set[str]:
    """Correct an untried interface plan before editing the blueprint.

    A semantic critic can correctly observe that a generated declaration lacks
    a mathematical interface while incorrectly concluding that the blueprint
    itself must be decomposed. When the shared plan has not yet consumed its
    one evidence-driven revision, repair that cheaper untrusted artifact first.
    A second decomposition verdict under the revised plan follows the existing
    transactional blueprint-decomposition path.
    """
    entries = getattr(ctx, "design_plan_entries", {}) or {}
    eligible = {
        label
        for label in labels
        if label in entries
        and (entries.get(label) or {}).get("origin") != "phase1_candidate"
        and int((entries.get(label) or {}).get("schema_version") or 0)
        == DESIGN_PLAN_SCHEMA_VERSION
        and int((entries.get(label) or {}).get("semantic_revision_count") or 0)
        < 1
    }
    if not eligible:
        return set()
    revised = _revise_exhausted_phase1_contracts(ctx, eligible, evidence)
    if revised:
        _record(
            ctx.telemetry,
            "phase1_decomposition_deferred_for_plan_revision",
            layer=layer_no,
            source=source,
            labels=sorted(revised),
            evidence=evidence[-4000:],
        )
        _log(
            "  decomposition verdict first corrected the untried interface "
            "plan for: " + ", ".join(sorted(revised))
        )
    return revised


def _semantic_exhaustion_policy(ctx: Ctx, label: str) -> str:
    """Classify the next bounded action without mutating refinement state.

    This pure policy is deliberately separate from the router so historical
    traces can validate a proposed lifecycle before it changes live behavior.
    """
    if _uses_blueprint_direct_generation(ctx, label):
        return "decomposition"
    entry = (getattr(ctx, "design_plan_entries", {}) or {}).get(label) or {}
    # Fresh Phase-1 contracts are derived from the exact Lean candidate and
    # have already received an evidence-driven candidate correction before
    # this exhaustion point.  There is no independent typed plan to repair.
    if entry.get("origin") == "phase1_candidate":
        return "blueprint-direct"
    if int(entry.get("semantic_revision_count") or 0) >= 1:
        return "blueprint-direct"
    return "plan-revision"


def _route_exhausted_phase1_semantics(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    layer_no: int,
    source: str,
    failure_kind: str = "semantic",
    evidence_by_label: Mapping[str, str] | None = None,
    evidence_identities_by_label: Mapping[str, Mapping[str, Any]] | None = None,
) -> tuple[set[str], set[str], set[str]]:
    """Route Phase-1 retry exhaustion identically for every failure source.

    The first exhausted lifecycle revises the node's saved interface plan from
    exact compiler or critic evidence. A second exhaustion disables that plan
    for the same statement fingerprint and tries blueprint-direct generation.
    Only exhaustion of that direct lifecycle routes the node to decomposition.

    Returns ``(decomposition, revised, unresolved)`` label sets.
    """
    exhausted = set(labels)
    scoped_evidence = (
        {
            label: str(value).strip()[-12000:]
            for label, value in evidence_by_label.items()
            if label in exhausted and str(value).strip()
        }
        if evidence_by_label is not None
        else _explicit_generation_evidence_by_label(exhausted, evidence)
    )
    scoped_identities = {
        label: identity
        for label, identity in (evidence_identities_by_label or {}).items()
        if label in exhausted and identity
    }
    if failure_kind == "compile":
        for label, label_evidence in scoped_evidence.items():
            scoped_identities.setdefault(
                label,
                {
                    "failure_class": "lean_compile",
                    "error_shape": _lean_error_shape(label_evidence),
                },
            )
    actions = {
        label: _semantic_exhaustion_policy(ctx, label)
        for label in exhausted
    }
    decomposition = {
        label for label, action in actions.items() if action == "decomposition"
    }
    if decomposition:
        exhausted.difference_update(decomposition)
        failure_description = {
            "compile": "compiler failure",
            "deterministic": "deterministic rejection",
        }.get(failure_kind, "semantic rejection")
        _log(
            f"  {failure_description} survived the blueprint-direct generation "
            "lifecycle; routing to blueprint decomposition: "
            + ", ".join(sorted(decomposition))
        )
        _record(
            ctx.telemetry,
            f"phase1_{failure_kind}_exhaustion_decomposition",
            layer=layer_no,
            source=source,
            labels=sorted(decomposition),
            statement_fps={
                label: ctx.stmt_fps.get(label, "")
                for label in sorted(decomposition)
            },
            evidence=evidence[-4000:],
        )

    direct_requested = {
        label
        for label, action in actions.items()
        if action == "blueprint-direct"
    }
    candidate_direct = {
        label
        for label in direct_requested
        if (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            == "phase1_candidate"
        )
    }
    legacy_direct = direct_requested - candidate_direct
    direct = set()
    if candidate_direct:
        direct.update(
            _activate_blueprint_direct_generation(
                ctx,
                candidate_direct,
                evidence,
                source=f"candidate_{failure_kind}_exhaustion",
                evidence_by_label={
                    label: scoped_evidence[label]
                    for label in candidate_direct
                    if label in scoped_evidence
                },
            )
        )
    if legacy_direct:
        direct_source = (
            "post_semantic_rejection_after_plan_revision"
            if failure_kind == "semantic"
            else "post_compile_failure_after_plan_revision"
        )
        direct.update(
            _activate_blueprint_direct_generation(
                ctx,
                legacy_direct,
                evidence,
                source=direct_source,
                evidence_by_label={
                    label: scoped_evidence[label]
                    for label in legacy_direct
                    if label in scoped_evidence
                },
            )
        )
    exhausted.difference_update(direct)
    revision_kwargs = (
        {"evidence_identities_by_label": scoped_identities}
        if scoped_identities
        else {}
    )
    revised = direct | _revise_exhausted_phase1_contracts(
        ctx,
        exhausted,
        evidence,
        **revision_kwargs,
    )
    unresolved = exhausted - revised
    return decomposition, revised, unresolved


def _route_phase1_precompile_deterministic_failure(
    ctx: Ctx,
    request: RepairRequest,
    *,
    layer_no: int,
) -> list[RepairRequest]:
    """Advance deterministic generation failures through the shared lifecycle.

    This runs in the coordinator after every generation worker has settled.
    Plan-closure failures retain their dedicated correction path; all other
    deterministic rejections use the same bounded base/escalation/strategy
    lifecycle as compiler and semantic failures.
    """
    attempted_tier = request.retry_attempted_tier
    if request.plan_revision_required or not attempted_tier:
        return [request]

    exhausted: set[str] = set()
    for label in request.labels:
        evidence = request.evidence_by_label.get(label, request.evidence)
        exhausted.update(
            _record_retry_failure(
                ctx,
                [label],
                stage="phase1_statement",
                attempted_tier=attempted_tier,
                evidence=evidence,
                source=f"phase1_layer_{layer_no}_deterministic",
                evidence_identity=request.evidence_identities_by_label.get(label),
            )
        )

    if not exhausted:
        _record(
            ctx.telemetry,
            "phase1_deterministic_failure_routed",
            layer=layer_no,
            labels=request.labels,
            classification="lean_generation",
            attempted_tier=attempted_tier,
        )
        return [request]

    decomposition, strategy_changed, unresolved = (
        _route_exhausted_phase1_semantics(
            ctx,
            exhausted,
            request.evidence,
            layer_no=layer_no,
            source="precompile_deterministic",
            failure_kind="deterministic",
            evidence_by_label=request.evidence_by_label,
            evidence_identities_by_label=request.evidence_identities_by_label,
        )
    )
    routed: list[RepairRequest] = []

    if decomposition:
        labels = sorted(decomposition)
        routed.append(
            RepairRequest(
                "Repeated statement generation could not produce deterministic-"
                "valid Lean interfaces for these blueprint contracts. Decompose "
                "only the listed contracts into explicit blueprint helper "
                "definitions or lemmas, then regenerate their interfaces.\n\n"
                + request.evidence[-12000:],
                labels,
                decomposition_helpers=[
                    "split the failing public contract into explicit blueprint-"
                    "owned helper definitions or lemmas whose Lean interfaces "
                    "can be generated and validated independently"
                ],
                section_labels=labels,
                authorizes_blueprint_repair=True,
                evidence_by_label={
                    label: request.evidence_by_label[label]
                    for label in labels
                    if label in request.evidence_by_label
                },
                evidence_identities_by_label={
                    label: request.evidence_identities_by_label[label]
                    for label in labels
                    if label in request.evidence_identities_by_label
                },
            )
        )

    if strategy_changed:
        labels = sorted(strategy_changed)
        routed.append(
            RepairRequest(
                "The deterministic statement-generation retry lifecycle was "
                "exhausted, so the interface-generation strategy changed before "
                "another candidate is attempted.\n\n"
                + request.evidence[-12000:],
                labels,
                section_labels=labels,
                authorizes_blueprint_repair=False,
                failure_route=_route_lean_generation_failure(labels),
                plan_revision_required=True,
                evidence_by_label={
                    label: request.evidence_by_label[label]
                    for label in labels
                    if label in request.evidence_by_label
                },
                evidence_identities_by_label={
                    label: request.evidence_identities_by_label[label]
                    for label in labels
                    if label in request.evidence_identities_by_label
                },
            )
        )

    ordinary = [
        label
        for label in request.labels
        if label not in decomposition and label not in strategy_changed
    ]
    if ordinary:
        route = _route_lean_generation_failure(ordinary)
        routed.append(
            RepairRequest(
                request.evidence,
                list(route.failed_labels),
                section_labels=ordinary,
                authorizes_blueprint_repair=False,
                failure_route=route,
                evidence_by_label={
                    label: request.evidence_by_label[label]
                    for label in route.failed_labels
                    if label in request.evidence_by_label
                },
                evidence_identities_by_label={
                    label: request.evidence_identities_by_label[label]
                    for label in route.failed_labels
                    if label in request.evidence_identities_by_label
                },
            )
        )

    _record(
        ctx.telemetry,
        "phase1_deterministic_failure_routed",
        layer=layer_no,
        labels=request.labels,
        classification=(
            "decomposition"
            if decomposition
            else "strategy_changed"
            if strategy_changed
            else "lean_generation"
        ),
        attempted_tier=attempted_tier,
        exhausted_labels=sorted(exhausted),
        decomposition_labels=sorted(decomposition),
        strategy_changed_labels=sorted(strategy_changed),
        unresolved_labels=sorted(unresolved),
    )
    return routed or [request]


def _run_validated_contract_phase1_layer(
    ctx: Ctx,
    layer_no: int,
    groups: list[list[str]],
    sections: list[Section],
    alloc: _SectionNumberAllocator,
) -> list[Section]:
    """Generate from shared plan entries, compile, then audit final statements.

    The plan is untrusted guidance, so this transaction spends no critic call
    on it. Compiler correction remains local to each candidate; the integrated,
    compiling declarations receive the mandatory publication audit exactly
    once (or a cache hit when byte-identical).
    """
    worker_count = max(1, min(getattr(ctx, "workers", 1), len(groups)))
    _log(
        f"==> {_contract_work_stage(ctx)} layer {layer_no}: generating {len(groups)} uncompiled "
        f"candidate group(s) with {worker_count} worker(s)"
    )
    generated: list[Phase1LayerCandidate | None] = [None] * len(groups)
    compiled_results: list[list[Section] | None] = [None] * len(groups)
    generation_failures: list[tuple[int, RepairRequest]] = []
    compile_failures: list[tuple[int, RepairRequest]] = []
    layer_started = time.monotonic()
    old_defer = getattr(ctx, "defer_phase1_alignment", False)
    ctx.defer_phase1_alignment = True
    try:
        def generate_and_compile(
            index: int, group: list[str]
        ) -> tuple[
            int,
            Phase1LayerCandidate | None,
            list[Section] | None,
            RepairRequest | None,
            str,
        ]:
            try:
                candidate = _generate_uncompiled_phase1_candidate(
                    ctx, group, sections
                )
            except RepairRequest as request:
                return index, None, None, request, "generation"

            _record(
                ctx.telemetry,
                "phase1_streamed_compile_started",
                layer=layer_no,
                labels=candidate.labels,
                elapsed_since_layer_start_s=round(
                    time.monotonic() - layer_started, 3
                ),
            )
            result, evidence, failed_code = (
                _compile_semantic_phase1_candidate(
                    ctx,
                    candidate,
                    sections,
                    alloc,
                    layer_no=layer_no,
                )
            )
            if result is None:
                request = _route_phase1_compile_failure(
                    ctx,
                    candidate,
                    evidence,
                    failed_code,
                    layer_no=layer_no,
                )
                return index, candidate, None, request, "compile"
            return index, candidate, result, None, ""

        with concurrent.futures.ThreadPoolExecutor(max_workers=worker_count) as pool:
            futures = [
                pool.submit(generate_and_compile, index, group)
                for index, group in enumerate(groups)
            ]
            for future in concurrent.futures.as_completed(futures):
                index, candidate, result, request, failure_stage = future.result()
                generated[index] = candidate
                compiled_results[index] = result
                if request is not None:
                    if failure_stage == "generation":
                        generation_failures.append((index, request))
                    else:
                        compile_failures.append((index, request))
    finally:
        ctx.defer_phase1_alignment = old_defer
    candidates = [candidate for candidate in generated if candidate is not None]
    compiled = [
        section
        for result in compiled_results
        if result
        for section in result
    ]
    if generation_failures or compile_failures:
        # A plan-closure finding cannot be repaired honestly by compiler
        # patching. Correct only the owning plan entries before ordinary retry.
        plan_requests = [
            request
            for _index, request in generation_failures
            if request.plan_revision_required
        ]
        plan_labels = sorted(
            {
                label
                for request in plan_requests
                for label in request.labels
            }
        )
        if plan_labels:
            plan_evidence = "\n\n".join(
                request.evidence[-6000:] for request in plan_requests
            )
            corrected = _correct_phase1_design_plan(
                ctx, plan_labels, plan_evidence, escalated=False
            )
            _record(
                ctx.telemetry,
                "phase1_outline_plan_closure_correction",
                labels=plan_labels,
                corrected=bool(corrected),
                reason="deterministic_contract_closure",
            )
            if corrected:
                _log(
                    f"  corrected mechanically unclosed {_contract_work_stage(ctx)} outline plan: "
                    + ", ".join(plan_labels)
                )
        routed_failures: list[tuple[int, RepairRequest]] = []
        for index, request in generation_failures:
            for routed in _route_phase1_precompile_deterministic_failure(
                ctx, request, layer_no=layer_no
            ):
                routed_failures.append((index, routed))
        failures = routed_failures + compile_failures
        compile_failed_indexes = {
            index for index, _request in compile_failures
        }
        for index, candidate in enumerate(generated):
            if candidate is None or index in compile_failed_indexes:
                continue
            _store_generation_candidates(
                ctx,
                candidate.labels,
                _phase1_layer_candidate_code(candidate),
                source=f"phase1_layer_{layer_no}_incomplete_generation",
                all_labels=candidate.labels,
                reusable_uncompiled=True,
                generation_tier=candidate.generation_tier,
                expected_plan_fps=candidate.plan_fps,
            )
        failures.sort(key=lambda item: item[0])
        # A failed generation group must not hold deterministically valid
        # siblings behind a frontier-wide barrier. Advance those siblings
        # through the ordinary compile/integration/alignment transaction now;
        # only their accepted contracts are attached to the retry request.
        accepted: list[Section] = []
        downstream_request: RepairRequest | None = None
        if compiled:
            try:
                accepted = _audit_phase1_layer_candidates(
                    ctx, layer_no, compiled, sections, alloc
                )
            except RepairRequest as request:
                accepted = list(request.frozen_sections)
                request.frozen_sections = []
                downstream_request = request

        # Prefer evidence that authorizes an actual blueprint edit. Every
        # non-selected generation/semantic failure has already persisted its
        # candidate, exact evidence, and retry lifecycle for the next frontier.
        requests = [request for _index, request in failures]
        if downstream_request is not None:
            requests.append(downstream_request)
        authorized = [
            request for request in requests if request.authorizes_blueprint_repair
        ]
        if authorized:
            selected = _aggregate_authorized_repair_requests(
                authorized,
                frozen_sections=accepted,
            )
            _record(
                ctx.telemetry,
                "phase1_authorized_repairs_aggregated",
                layer=layer_no,
                request_count=len(authorized),
                labels=selected.labels,
                model_repair_labels=selected.model_repair_labels,
                required_dependencies={
                    label: sorted(dependencies)
                    for label, dependencies in selected.required_dependencies.items()
                },
            )
        else:
            selected = _aggregate_retry_requests(
                requests, frozen_sections=accepted
            )
        _record(
            ctx.telemetry,
            "phase1_partial_frontier_advanced",
            layer=layer_no,
            generated_failure_labels=sorted(
                {
                    label
                    for _index, request in routed_failures
                    for label in request.labels
                }
            ),
            compile_failure_labels=sorted(
                {
                    label
                    for _index, request in compile_failures
                    for label in request.labels
                }
            ),
            additional_failure_labels=(
                sorted(downstream_request.labels)
                if downstream_request is not None
                else []
            ),
            frozen_labels=[
                label for section in accepted for label in section.labels
            ],
        )
        raise selected

    labels = [label for candidate in candidates for label in candidate.labels]
    _record(
        ctx.telemetry,
        "phase1_validated_contract_transaction",
        layer=layer_no,
        labels=labels,
        groups=[candidate.labels for candidate in candidates],
        stage="streamed_generate_typecheck_then_batched_audit_and_object_integration",
    )
    return _audit_phase1_layer_candidates(
        ctx, layer_no, compiled, sections, alloc
    )


def _run_phase1(
    ctx: Ctx,
    sections: list[Section],
    pending: set[str],
    refinement_order: str,
) -> list[Section]:
    """Freeze the one-time initial statement skeleton during Phase 1 only."""
    if bool(getattr(ctx, "phase2_started", False)):
        raise RuntimeError(
            "Phase 1 statement generation cannot run after Phase 2 starts; "
            "use the Phase 2 whole-node transaction"
        )
    if not pending:
        return sections
    stage = _contract_work_stage(ctx)

    # Source markers and the configured open-claim policy are authoritative.
    # Resolve them before paying for advisory planning or Lean generation.
    source_readiness_request = _phase1_source_readiness_request(ctx, pending)
    if source_readiness_request is not None:
        raise source_readiness_request

    # The global pass coordinates semantics and vocabulary only. Exact typed
    # contracts are created atomically with each Phase-1 Lean candidate below;
    # this avoids a separate typed planning phase and its correction loop.
    _ensure_phase1_semantic_plan(ctx, pending)
    advisory_readiness_request = _phase1_advisory_readiness_request(ctx, pending)
    if advisory_readiness_request is not None:
        raise advisory_readiness_request
    # Resumed state from the legacy typed planner remains valid and keeps its
    # historical closure behavior. Fresh compact-plan runs have no typed
    # entries yet; their closure starts when each candidate realizes one.
    legacy_plan_labels = {
        label
        for label in pending
        if label in getattr(ctx, "design_plan_entries", {})
        and (
            (getattr(ctx, "design_plan_entries", {}).get(label) or {}).get(
                "origin"
            )
            != "phase1_candidate"
        )
    }
    closure_findings: dict[str, list[str]] = (
        _validate_design_plan_contract_closure(ctx, legacy_plan_labels)
        if legacy_plan_labels
        else {}
    )
    _save_ctx_state(ctx, sections)
    plan_order = _design_plan_order(ctx, pending)

    if refinement_order == "bottom-up":
        alloc = _SectionNumberAllocator(
            max((section.number for section in sections), default=0) + 1
        )
        remaining = set(pending)
        frontier_no = 0
        deferred_requests: list[RepairRequest] = []
        suspended: set[str] = set()
        while remaining:
            frozen = _frozen_labels(sections)
            targets = _bottom_up_ready_frontier(
                ctx.nodes, remaining - suspended, frozen
            )
            if not targets:
                if deferred_requests:
                    _record(
                        ctx.telemetry,
                        "phase1_independent_branch_drain_completed",
                        deferred_request_count=len(deferred_requests),
                        deferred_labels=sorted(
                            {
                                label
                                for request in deferred_requests
                                for label in request.labels
                            }
                        ),
                        additionally_frozen=sorted(
                            set(pending) - remaining
                        ),
                    )
                    raise _combine_deferred_phase1_requests(
                        deferred_requests
                    )
                blocked_by = {
                    label: sorted(
                        dep
                        for dep in ctx.nodes[label].uses
                        if dep in remaining and not ctx.nodes[dep].mathlibok
                    )
                    for label in sorted(remaining)
                }
                _record(
                    ctx.telemetry,
                    "phase1_ready_frontier_stalled",
                    owner_phase=(
                        "phase2"
                        if bool(getattr(ctx, "phase2_started", False))
                        else "phase1"
                    ),
                    pending_labels=sorted(remaining),
                    frozen_labels=sorted(frozen),
                    blocked_by=blocked_by,
                )
                raise RepairRequest(
                    f"{stage} has pending declarations but no "
                    "dependency-ready frontier. Validation should have rejected "
                    "a dependency cycle; blocked dependencies: "
                    + json.dumps(blocked_by, sort_keys=True),
                    sorted(remaining),
                    section_labels=sorted(remaining),
                    authorizes_blueprint_repair=False,
                )
            closure_findings = _phase1_frontier_plan_gateway(
                ctx,
                targets,
                plan_order,
                closure_findings,
            )
            targets = _coalesce_candidate_components(ctx, targets)
            _log(
                f"==> {stage}: refining bottom-up ready frontier {frontier_no} "
                f"({len(targets)} node(s))"
            )
            groups: list[list[str]] = []
            index = 0
            while index < len(targets):
                component = set(
                    _candidate_component_labels(ctx, targets[index], set(targets))
                )
                forced = [
                    label for label in targets[index:] if label in component
                ]
                with _STATE_LOCK:
                    reusable_entry = copy.deepcopy(
                        getattr(ctx, "generation_candidates", {}).get(
                            targets[index]
                        )
                    )
                if len(forced) > 1 or (
                    isinstance(reusable_entry, dict)
                    and _candidate_is_reusable_uncompiled(reusable_entry)
                ):
                    group = forced
                else:
                    size = ctx.effective_section_size or ctx.section_size
                    group = _next_phase1_group(
                        targets,
                        index,
                        size,
                        ctx.quarantined_labels,
                        getattr(ctx, "local_group_partitions", {}),
                    )
                groups.append(group)
                index += len(group)

            groups = _partition_phase1_groups_by_dependency_context(
                ctx, groups, sections
            )
            groups = _coalesce_phase1_semantic_correction_waves(
                ctx, groups, sections
            )
            worker_count = max(1, min(getattr(ctx, "workers", 1), len(groups)))
            _record(
                ctx.telemetry,
                "phase1_layer_started",
                owner_phase=(
                    "phase2"
                    if bool(getattr(ctx, "phase2_started", False))
                    else "phase1"
                ),
                layer=frontier_no,
                scheduling="dynamic_dependency_ready_frontier",
                labels=targets,
                groups=groups,
                workers=worker_count,
                transaction_order="validated-contract_compile_final-audit",
            )
            try:
                accepted = _run_validated_contract_phase1_layer(
                    ctx, frontier_no, groups, sections, alloc
                )
            except RepairRequest as request:
                if request.frozen_sections:
                    sections.extend(request.frozen_sections)
                    remaining.difference_update(
                        label
                        for section in request.frozen_sections
                        for label in (
                            section.labels
                            if section.refined_labels is None
                            else section.refined_labels
                        )
                    )
                    request.frozen_sections = []
                    _save_ctx_state(ctx, sections)
                frozen = _frozen_labels(sections)
                failed_roots = {
                    label
                    for label in (request.context_labels or request.labels)
                    if label in ctx.nodes
                }
                if not failed_roots:
                    failed_roots = set(targets)
                blocked = (
                    _dependency_descendants(ctx.nodes, failed_roots)
                    | failed_roots
                ) & remaining
                independent_ready = _bottom_up_ready_frontier(
                    ctx.nodes,
                    remaining - blocked - suspended,
                    frozen,
                )
                if independent_ready:
                    deferred_requests.append(request)
                    suspended.update(blocked)
                    _record(
                        ctx.telemetry,
                        "phase1_independent_branch_drain_started",
                        layer=frontier_no,
                        failed_labels=sorted(failed_roots),
                        suspended_labels=sorted(blocked),
                        next_ready_labels=independent_ready,
                        blueprint_edit_deferred=True,
                    )
                    _log(
                        f"  {stage} failure is local to {len(blocked)} pending "
                        "node(s); advancing independent ready work before the "
                        "serialized repair"
                    )
                    frontier_no += 1
                    continue
                if deferred_requests:
                    deferred_requests.append(request)
                    raise _combine_deferred_phase1_requests(
                        deferred_requests
                    )
                raise
            sections.extend(accepted)
            accepted_labels = {
                label
                for section in accepted
                for label in (
                    section.labels
                    if section.refined_labels is None
                    else section.refined_labels
                )
            }
            if not accepted_labels:
                raise RepairRequest(
                    f"{stage} transaction returned without freezing "
                    "any dependency-ready declaration.",
                    targets,
                    section_labels=targets,
                    authorizes_blueprint_repair=False,
                )
            remaining.difference_update(accepted_labels)
            _save_ctx_state(ctx, sections)
            frontier_no += 1
        return sections

    layers = _top_down_statement_layers(ctx.nodes)

    owner = {label: sec for sec in sections for label in sec.labels}
    for layer_no, layer in enumerate(layers):
        targets = [label for label in layer if label in pending]
        if not targets:
            continue
        closure_findings = _phase1_frontier_plan_gateway(
            ctx,
            targets,
            plan_order,
            closure_findings,
        )
        _log(
            f"==> {stage}: refining top-down statement layer {layer_no} "
            f"({len(targets)} node(s))"
        )
        by_section: dict[int, list[str]] = {}
        for label in targets:
            sec = owner.get(label)
            if sec is None or sec.deferred:
                raise RepairRequest(
                    f"Initial declaration for {label} is unavailable during {stage}",
                    [label],
                    section_labels=[label],
                )
            by_section.setdefault(sec.number, []).append(label)
        for number in sorted(by_section):
            sec = next(item for item in sections if item.number == number)
            group = by_section[number]
            isolated = [
                label for label in group if label in ctx.quarantined_labels
            ]
            parts = _parts_around_labels(group, isolated) if isolated else [group]
            parts = _partition_phase1_groups_by_dependency_context(
                ctx, parts, sections
            )
            def refine_part(part: list[str]) -> None:
                starting_tier = (
                    _retry_next_tier(ctx, part[0], "phase1_statement")
                    if len(part) == 1
                    else "base"
                )
                try:
                    _refine_statement_group(ctx, sec, part, sections)
                    _save_ctx_state(ctx, sections)
                except RepairRequest as request:
                    route = request.failure_route
                    if not request.authorizes_blueprint_repair:
                        failed_labels = (
                            list(route.failed_labels) if route is not None else request.labels
                        )
                        attempted_tier = (
                            starting_tier
                            if len(part) == 1
                            else "base"
                        )
                        exhausted: set[str] = set()
                        for failed_label in failed_labels:
                            exhausted.update(
                                _record_retry_failure(
                                    ctx,
                                    [failed_label],
                                    stage="phase1_statement",
                                    attempted_tier=attempted_tier,
                                    evidence=request.evidence_by_label.get(
                                        failed_label, request.evidence
                                    ),
                                    source="phase1_top_down",
                                    evidence_identity=(
                                        request.evidence_identities_by_label.get(
                                            failed_label
                                        )
                                    ),
                                )
                            )
                        _store_generation_feedback(
                            ctx,
                            failed_labels,
                            request.evidence,
                            source="phase1_top_down_retry",
                            evidence_by_label=request.evidence_by_label,
                            evidence_identity_by_label=(
                                request.evidence_identities_by_label
                            ),
                        )
                        if exhausted and len(part) == 1:
                            # Exhausting translation attempts is not evidence
                            # that the blueprint contract is mathematically
                            # wrong. Keep the draft immutable and consume the
                            # configured outer generation budget instead.
                            request.failure_route = None
                            raise
                    if route is None or route.action == "singleton":
                        raise
                    _record(
                        ctx.telemetry,
                        "lean_generation_failure_routed",
                        stage="phase1_top_down",
                        action=route.action,
                        labels=part,
                        failing_labels=list(route.failed_labels),
                        accepted_labels=list(route.accepted_labels),
                        part_sizes=[len(item) for item in route.parts],
                        layer=layer_no,
                    )
                    _log(
                        f"  top-down {stage} failure routed as "
                        + route.action
                        + " across "
                        + " + ".join(str(len(item)) for item in route.parts)
                        + " node(s)"
                    )
                    for routed_part in route.parts:
                        refine_part(list(routed_part))

            for part in parts:
                refine_part(part)
    return sections


def _phase1_recompile_environment(ctx: Ctx, sections: list[Section]) -> set[str]:
    """Reuse clean contract objects, rebuild dirty ones, then check all imports.

    Every section is compiled when it freezes. Recompiling every unchanged
    module here made the final integration gate linear in all prior compiler
    work. Persisted fingerprints retain the same safety: source, toolchain,
    manifest, command, and imported generated interfaces must all match. One
    final aggregate import check proves the reused objects coexist.
    """
    # An integration failure can clear every accepted label from a section
    # while retaining the file as retry input.  Such a section is not part of
    # the frozen environment and must not be compiled or imported here.  Doing
    # so repeatedly checks stale imports, clears zero additional labels, and
    # leaves the outer loop with exactly the same state forever.
    active = [
        item
        for item in sections
        if not item.deferred
        and (item.refined_labels is None or bool(item.refined_labels))
    ]
    by_module = {sec.module: sec for sec in active}
    ordered: list[Section] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(sec: Section) -> None:
        if sec.module in visited:
            return
        if sec.module in visiting:
            # Blueprint validation should prevent a dependency cycle. Keep the
            # check total and let Lean report the malformed import graph.
            return
        visiting.add(sec.module)
        for module in sec.import_modules:
            dependency = by_module.get(module)
            if dependency is not None:
                visit(dependency)
        visiting.remove(sec.module)
        visited.add(sec.module)
        ordered.append(sec)

    for section in sorted(active, key=lambda item: item.number):
        visit(section)

    started = time.monotonic()
    checked = len(ordered)
    reused = 0
    rebuilt = 0
    failed: set[str] = set()
    stage = _contract_work_stage(ctx)
    _log(f"==> {stage} integration gate: checking {checked} module fingerprint(s)")
    for index, sec in enumerate(ordered, 1):
        expected = _section_compile_fingerprint(sec, ctx.lean_command, ordered)
        if sec.compile_fingerprint == expected and _section_objects_exist(sec):
            reused += 1
            if index == checked or index % 10 == 0:
                _log(
                    f"  integration {index}/{checked}: {reused} reused, "
                    f"{rebuilt} rebuilt"
                )
            continue
        rebuilt += 1
        attempt = _compile_section_olean(sec, ctx.lean_command, ordered)
        if attempt.ok:
            if index == checked or index % 10 == 0:
                _log(
                    f"  integration {index}/{checked}: {reused} reused, "
                    f"{rebuilt} rebuilt"
                )
            continue
        refined = set(sec.labels) if sec.refined_labels is None else set(sec.refined_labels)
        failed.update(refined)
        sec.refined_labels = (
            set(sec.labels) - refined if sec.refined_labels is None else sec.refined_labels - refined
        )
        _log(
            f"  {stage} integration recheck returned {len(refined)} statement "
            f"contract(s) to refinement from {sec.file_name}"
        )
        _record(
            ctx.telemetry,
            "phase1_integration_recheck",
            section=sec.number,
            labels=sorted(refined),
            status="compile_failed",
            output_tail=attempt.output[-4000:],
        )
    aggregate_ok = False
    aggregate_output = ""
    if not failed:
        gate_path = _phase1_integration_gate_path(ctx)
        gate_path.parent.mkdir(parents=True, exist_ok=True)
        gate_path.write_text(
            "\n".join(f"import {sec.module}" for sec in ordered) + "\n",
            encoding="utf-8",
        )
        aggregate_ok, aggregate_output = _check_lean(
            gate_path, ctx.lean_command
        )
        if not aggregate_ok:
            failed.update(
                label
                for sec in ordered
                for label in (
                    sec.labels
                    if sec.refined_labels is None
                    else sec.refined_labels
                )
            )
            _log(
                f"  aggregate {stage} import check failed; returning the "
                "integrated contracts to deterministic refinement"
            )
    duration = time.monotonic() - started
    _log(
        f"  integration gate {'passed' if not failed and aggregate_ok else 'failed'}: "
        f"{reused} reused, {rebuilt} rebuilt, {duration:.1f}s"
    )
    _record(
        ctx.telemetry,
        "phase1_integration_gate",
        owner_phase=(
            "phase2"
            if bool(getattr(ctx, "phase2_started", False))
            else "phase1"
        ),
        checked_modules=checked,
        reused_modules=reused,
        rebuilt_modules=rebuilt,
        aggregate_ok=aggregate_ok,
        failed_labels=sorted(failed),
        duration_s=duration,
        output_tail=aggregate_output[-4000:] if not aggregate_ok else "",
    )
    return failed
