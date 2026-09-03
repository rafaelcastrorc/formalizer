"""Final assembly, verified-label accounting, and the pipeline progress card.

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
# Final assembly


def _assemble_final(ctx: Ctx, sections: list[Section]) -> str:
    imports: list[str] = []
    bodies: list[str] = []
    for sec in sorted(sections, key=lambda s: s.number):
        parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        for item in parsed.imports:
            if item.startswith("import AutoBlueprint"):
                continue
            if item not in imports:
                imports.append(item)
        body = "\n".join(parsed.preamble + [""] if parsed.preamble else [])
        body += "\n\n".join(d.text for d in parsed.decls)
        bodies.append(body)
    return _compose_lean_file(imports, bodies)


def _record_proof_graph_telemetry(
    telemetry: TelemetryRun,
    nodes: dict[str, Node],
    *,
    proof_order: str,
    reason: str,
    focus_labels: set[str] | None = None,
) -> None:
    """Record the current proof graph and node-level scheduling features."""
    root_first_layers = _top_down_proof_layers(nodes)
    scheduled_layers = (
        root_first_layers
        if proof_order == "top-down"
        else list(reversed(root_first_layers))
    )
    proof_depth = {
        label: depth
        for depth, labels in enumerate(root_first_layers)
        for label in labels
    }
    traversal_depth = {
        label: depth
        for depth, labels in enumerate(scheduled_layers)
        for label in labels
    }
    theorem_labels = set(proof_depth)
    immediate_theorem_deps = {
        label: sorted(_immediate_theorem_dependencies(nodes, label, theorem_labels))
        for label in theorem_labels
    }
    theorem_consumers: dict[str, list[str]] = {label: [] for label in theorem_labels}
    for consumer, dependencies in immediate_theorem_deps.items():
        for dependency in dependencies:
            theorem_consumers.setdefault(dependency, []).append(consumer)
    telemetry.record(
        "proof_schedule_graph",
        proof_order=proof_order,
        reason=reason,
        layers=scheduled_layers,
        roots=root_first_layers[0] if root_first_layers else [],
        immediate_theorem_dependencies=immediate_theorem_deps,
    )
    node_blocks = _node_tex_blocks(nodes)
    targets = nodes if focus_labels is None else {
        label: node for label, node in nodes.items() if label in focus_labels
    }
    roots = set(root_first_layers[0]) if root_first_layers else set()
    for label, node in targets.items():
        telemetry.record(
            "node_features",
            **node_structural_features(
                label, node.kind, node_blocks.get(label, ""), len(node.uses)
            ),
            proof_depth=proof_depth.get(label),
            traversal_depth=traversal_depth.get(label),
            is_proof_root=label in roots,
            immediate_theorem_dependencies=immediate_theorem_deps.get(label, []),
            immediate_theorem_dependency_count=len(immediate_theorem_deps.get(label, [])),
            theorem_consumers=sorted(theorem_consumers.get(label, [])),
            theorem_consumer_count=len(theorem_consumers.get(label, [])),
        )


def _verified_node_labels(ctx: Ctx, sections: list[Section]) -> set[str]:
    """Nodes whose current contract is already discharged in Lean/Mathlib."""
    frozen = _frozen_labels(sections)
    proved = _proved_labels(sections)
    return {
        label
        for label, node in ctx.nodes.items()
        if not _records_conjecture(ctx, label)
        and (
            node.mathlibok
        or label in proved
        or (label in frozen and not _is_theorem_like_kind(node.kind))
        )
    }


def _recorded_conjecture_labels(ctx: Ctx, sections: list[Section]) -> set[str]:
    """Open claims faithfully encoded as propositions, but not proved."""
    frozen = _frozen_labels(sections)
    recorded: set[str] = set()
    for sec in sections:
        if sec.deferred:
            continue
        try:
            parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        except OSError:
            continue
        by_name = {decl.name: decl for decl in parsed.decls if decl.name}
        for label in set(sec.labels) & frozen:
            if not _records_conjecture(ctx, label):
                continue
            decl = by_name.get(_lean_name(label))
            if (
                decl is not None
                and decl.kind in {"def", "abbrev"}
                and not _has_terminal_sorry(decl.text)
                and re.search(r":\s*Prop\s*:=", decl.text)
            ):
                recorded.add(label)
    return recorded


def _phase2_body_progress(
    ctx: Ctx, sections: list[Section]
) -> tuple[set[str], set[str]]:
    """Return ``(implemented, required)`` body labels among frozen contracts.

    Phase 1 freezes structures, inductives, classes, theorem statements, and
    typed definitions. Only declaration kinds with replaceable bodies belong
    to Phase 2; interface-only declarations are already complete in Phase 1.
    """
    frozen = _frozen_labels(sections)
    required: set[str] = set()
    implemented: set[str] = set()
    body_kinds = {"theorem", "lemma", "def", "abbrev", "instance"}
    for sec in sections:
        if sec.deferred:
            continue
        try:
            parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        except OSError:
            continue
        by_name = {decl.name: decl for decl in parsed.decls if decl.name}
        for label in set(sec.labels) & frozen:
            if label not in ctx.nodes or ctx.nodes[label].mathlibok:
                continue
            if _records_conjecture(ctx, label):
                continue
            decl = by_name.get(_lean_name(label))
            if decl is None or decl.kind not in body_kinds:
                continue
            required.add(label)
            if not _has_terminal_sorry(decl.text):
                implemented.add(label)
    return implemented, required


def _contract_work_stage(ctx: Ctx) -> str:
    """User-visible owner of declaration work in the current state."""
    return (
        "Phase 2 whole-node repair"
        if bool(getattr(ctx, "phase2_started", False))
        else "Phase 1"
    )


def _run_pending_declaration_work(
    ctx: Ctx,
    sections: list[Section],
    pending: set[str],
) -> list[Section]:
    """Enforce the one-way Phase 1/Phase 2 declaration boundary."""
    if bool(getattr(ctx, "phase2_started", False)):
        return _run_phase2_whole_node_repairs(ctx, sections, pending)
    return _run_phase1(ctx, sections, pending, PHASE1_STATEMENT_ORDER)


def _begin_phase2(ctx: Ctx, sections: list[Section]) -> bool:
    """Cross the one-way workflow boundary after the initial skeleton freezes.

    Returns ``True`` only for the transition itself. Later blueprint repairs
    regenerate complete statement-and-body declarations inside Phase 2.
    """
    if bool(getattr(ctx, "phase2_started", False)):
        return False
    required = {
        label for label, node in ctx.nodes.items() if not node.mathlibok
    }
    if not required <= _frozen_labels(sections):
        return False
    ctx.phase1_baseline_labels = set(required)
    ctx.phase2_started = True
    _record(
        ctx.telemetry,
        "phase2_started",
        phase1_baseline_labels=sorted(required),
        phase1_baseline_count=len(required),
    )
    _log(
        f"==> Phase 1 complete: initial skeleton frozen for "
        f"{len(required)} contract(s); entering Phase 2"
    )
    return True


def _print_pipeline_progress(
    ctx: Ctx, sections: list[Section], repair_trials: int, max_trials: int
) -> None:
    current_required = {
        label for label, node in ctx.nodes.items() if not node.mathlibok
    }
    phase2_started = bool(getattr(ctx, "phase2_started", False))
    baseline_labels = set(getattr(ctx, "phase1_baseline_labels", set()))
    if phase2_started and baseline_labels:
        # This card describes completion of the one-time initial skeleton, not
        # the transient state of Phase-2 contract patches.
        phase1_required = baseline_labels
        phase1_frozen = set(phase1_required)
    else:
        phase1_required = current_required
        phase1_frozen = _frozen_labels(sections) & phase1_required
    phase2_implemented, phase2_required = _phase2_body_progress(ctx, sections)
    verified = _verified_node_labels(ctx, sections)
    recorded = _recorded_conjecture_labels(ctx, sections)
    completed = verified | recorded
    print(
        f"==> Progress: Phase 1 contracts {len(phase1_frozen)}/{len(phase1_required)} frozen; "
        f"Phase 2 Lean implementations {len(phase2_implemented)}/{len(phase2_required)} complete; "
        f"overall {len(completed)}/{len(ctx.nodes)} complete "
        f"({len(verified)} verified, {len(recorded)} open conjectures recorded); "
        f"repair/retries {repair_trials}/{max_trials}",
        flush=True,
    )
    _record(
        ctx.telemetry,
        "pipeline_progress",
        phase1_frozen_labels=sorted(phase1_frozen),
        phase1_frozen_count=len(phase1_frozen),
        phase1_required_count=len(phase1_required),
        phase2_implemented_labels=sorted(phase2_implemented),
        phase2_implemented_count=len(phase2_implemented),
        phase2_required_count=len(phase2_required),
        verified_labels=sorted(verified),
        verified_count=len(verified),
        recorded_conjecture_labels=sorted(recorded),
        recorded_conjecture_count=len(recorded),
        completed_labels=sorted(completed),
        completed_count=len(completed),
        total_nodes=len(ctx.nodes),
        repair_trials_used=repair_trials,
        repair_trials_max=max_trials,
        workflow_phase="phase2" if phase2_started else "phase1",
        phase2_whole_node_pending_labels=sorted(
            current_required - _frozen_labels(sections)
            if phase2_started
            else set()
        ),
    )
