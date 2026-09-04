"""Transactional blueprint repair, boundary audit, dependency edges, section normalization.

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
# Blueprint repair (evidence-driven, batched)


def _invalidate_after_repair(
    ctx: Ctx,
    sections: list[Section],
    changed: set[str],
    lean_command: list[str],
    *,
    previous_nodes: dict[str, Node] | None = None,
) -> tuple[list[Section], set[str]]:
    """Invalidate changed contracts and defer unchanged descendants.

    Changed declarations are removed immediately. Descendants whose own full
    blueprint contract fingerprint did not change are retained as untrusted
    cache candidates: their ``.olean`` is removed and they stop counting as
    frozen until ``_reactivate_deferred_sections`` rebinds imports and Lean
    recompiles them against the repaired interfaces.
    """
    descendants = _dependency_descendants(ctx.nodes, changed) | changed
    if previous_nodes is not None:
        descendants |= _dependency_descendants(previous_nodes, changed)
    invalidated = set(changed)
    kept: list[Section] = []
    for sec in sections:
        if not sec.path.is_file():
            invalidated |= set(sec.labels)
            continue
        hit = set(sec.labels) & changed
        affected = set(sec.labels) & descendants
        if not affected:
            sec.deferred = False
            kept.append(sec)
            continue
        if sec.provisional_environment:
            parsed, _index = _module_decl_texts(sec)
            # This is permanent name scaffolding. A blueprint repair makes
            # affected contracts provisional again; it does not erase the
            # declarations and restart the initial model pass. Remove only
            # nodes deleted from the blueprint. New helper names are added
            # deterministically by the owning contract-patch operation on the
            # next loop iteration; after Phase 2 begins this does not reopen
            # Phase 1.
            surviving = [label for label in sec.labels if label in ctx.nodes]
            surviving_names = {_lean_name(label) for label in surviving}
            parsed.decls = [
                decl for decl in parsed.decls if decl.name in surviving_names
            ]
            invalidated |= set(sec.labels) & descendants
            sec.labels = surviving
            if sec.refined_labels is None:
                sec.refined_labels = set()
            else:
                sec.refined_labels &= set(surviving) - descendants
            sec.deferred = False
            _write_section(sec, parsed)
            _discard_section_objects(sec.path)
            kept.append(sec)
            continue
        if hit:
            parsed, _index = _module_decl_texts(sec)
            owned_names = {_lean_name(label) for label in sec.labels}
            # Unowned local helpers may encode the changed contract. Without a
            # reliable label-level owner, retaining them would be unsafe; drop
            # this directly edited section and regenerate it normally. Broad
            # downstream sections can still be deferred and salvaged.
            if any(
                decl.name is None or decl.name not in owned_names
                for decl in parsed.decls
            ):
                invalidated |= set(sec.labels)
                _discard_section_artifacts(sec.path)
                continue
            retained = [label for label in sec.labels if label not in affected]
            invalidated |= affected
            if not retained:
                _discard_section_artifacts(sec.path)
                continue
            retained_names = {_lean_name(label) for label in retained}
            parsed.decls = [
                decl for decl in parsed.decls if decl.name in retained_names
            ]
            sec.labels = retained
            if sec.refined_labels is not None:
                sec.refined_labels &= set(retained)
            _write_section(sec, parsed)
            ok, _output = _check_lean(sec.path, lean_command)
            if ok and _compile_section_olean(sec, lean_command, kept).ok:
                sec.deferred = False
                kept.append(sec)
            else:
                # A retained declaration that still mentions the edited
                # contract exposes a missing dependency edge or an unowned
                # local coupling. Lean, rather than file order, decides that
                # it cannot be reused.
                invalidated |= set(retained)
                _discard_section_artifacts(sec.path)
            continue
        sec.deferred = True
        invalidated |= set(sec.labels)
        _discard_section_objects(sec.path)
        kept.append(sec)
    return kept, invalidated


def _generated_skeleton_import(item: str, name: str) -> bool:
    base = _module_safe_name(name)
    return item.startswith(f"import AutoBlueprint.Generated.{base}.Skeleton")


def _reactivate_deferred_sections(
    ctx: Ctx,
    sections: list[Section],
    *,
    drop_unready: bool = False,
) -> tuple[list[Section], set[str], set[str]]:
    """Rebind and recompile unchanged descendants after a repair.

    Returns ``(sections, reactivated_labels, dropped_labels)``. No model or
    semantic critic is called: the node's full contract fingerprint is already
    unchanged, and Lean recompilation checks it against the final regenerated
    dependency interfaces.
    """
    reactivated: set[str] = set()
    dropped: set[str] = set()
    active = [sec for sec in sections if not sec.deferred]
    waiting = [sec for sec in sections if sec.deferred]
    progress = True
    while waiting and progress:
        progress = False
        owner = {label: sec for sec in active for label in sec.labels}
        for sec in list(waiting):
            own = set(sec.labels)
            external_deps = {
                dep
                for label in sec.labels
                for dep in ctx.nodes.get(
                    label, Node(label, "", Path("."), 0)
                ).uses
                if dep in ctx.nodes
                and not ctx.nodes[dep].mathlibok
                and dep not in own
            }
            if any(dep not in owner for dep in external_deps):
                continue
            try:
                parsed, index = _module_decl_texts(sec)
            except OSError:
                dropped.update(sec.labels)
                waiting.remove(sec)
                progress = True
                continue
            if any(_lean_name(label) not in index for label in sec.labels):
                dropped.update(sec.labels)
                waiting.remove(sec)
                progress = True
                _discard_section_artifacts(sec.path)
                _record(
                    ctx.telemetry,
                    "deferred_section_recheck",
                    section=sec.number,
                    labels=sec.labels,
                    status="missing_declarations",
                    compile_output_tail="",
                )
                continue
            generated_imports = _sections_for_deps(ctx, sec.labels, active)
            parsed.imports = [f"import {module}" for module in generated_imports] + [
                item
                for item in parsed.imports
                if not _generated_skeleton_import(item, ctx.name)
            ]
            sec.import_modules = generated_imports
            _write_section(sec, parsed)
            ok, output = _check_lean(sec.path, ctx.lean_command)
            object_ok = ok and _compile_section_olean(
                sec, ctx.lean_command, active
            ).ok
            if object_ok:
                sec.deferred = False
                active.append(sec)
                waiting.remove(sec)
                reactivated.update(sec.labels)
                progress = True
                _log(
                    f"  reactivated deferred {sec.file_name} "
                    f"({len(sec.labels)} unchanged contract(s))"
                )
                _record(
                    ctx.telemetry,
                    "deferred_section_recheck",
                    section=sec.number,
                    labels=sec.labels,
                    status="reactivated",
                    compile_output_tail="",
                )
            else:
                dropped.update(sec.labels)
                waiting.remove(sec)
                progress = True
                _discard_section_artifacts(sec.path)
                _log(
                    f"  deferred {sec.file_name} no longer compiles; "
                    f"returning {len(sec.labels)} node(s) to "
                    f"{_contract_work_stage(ctx)}"
                )
                _record(
                    ctx.telemetry,
                    "deferred_section_recheck",
                    section=sec.number,
                    labels=sec.labels,
                    status="compile_failed",
                    compile_output_tail=output[-4000:],
                )
    if waiting and drop_unready:
        for sec in waiting:
            dropped.update(sec.labels)
            _discard_section_artifacts(sec.path)
            _record(
                ctx.telemetry,
                "deferred_section_recheck",
                section=sec.number,
                labels=sec.labels,
                status="dependencies_unavailable",
                compile_output_tail="",
            )
        waiting = []
    retained = active + waiting
    retained.sort(key=lambda sec: sec.number)
    return retained, reactivated, dropped


def _paper_excerpt_for(ctx: Ctx, labels: list[str], *, budget: int = 20000) -> str:
    """Deterministic paper slice for repair prompts: the head of the paper
    (title/abstract) plus the paragraphs sharing the rarest terms with the
    target nodes' TeX. Repair calls previously carried the full paper."""
    paper = ctx.paper_text or ""
    if len(paper) <= budget:
        return paper
    target_text = " ".join(ctx.tex_blocks.get(label, "") for label in labels)
    target_tokens = set(_WORD_TOKEN_RE.findall(target_text.lower()))
    paragraphs = [para for para in re.split(r"\n\s*\n", paper) if para.strip()]
    freq: dict[str, int] = {}
    para_tokens: list[set[str]] = []
    for para in paragraphs:
        tokens = set(_WORD_TOKEN_RE.findall(para.lower())) & target_tokens
        para_tokens.append(tokens)
        for token in tokens:
            freq[token] = freq.get(token, 0) + 1
    scored = sorted(
        (
            (sum(1.0 / freq[token] for token in tokens), index)
            for index, tokens in enumerate(para_tokens)
        ),
        reverse=True,
    )
    head = paper[:_PAPER_EXCERPT_HEAD]
    used = len(head)
    chosen: set[int] = set()
    for score, index in scored:
        if score <= 0.0:
            break
        size = len(paragraphs[index]) + 2
        if used + size > budget:
            continue
        chosen.add(index)
        used += size
    body = "\n\n".join(paragraphs[index] for index in sorted(chosen))
    if not body:
        return head
    return f"{head}\n\n[... paper excerpted; paragraphs relevant to the failing nodes ...]\n\n{body}"


def _repair_node_context(
    ctx: Ctx,
    labels: list[str],
    *,
    dep_budget: int = 14000,
    consumer_budget: int = 6000,
) -> str:
    """Failing nodes in full, dependency-closure statements, and immediate
    consumer statements — the slice a repair actually needs, instead of the
    entire blueprint."""
    target_set = {label for label in labels if label in ctx.nodes}
    blocks: list[str] = []
    for label in sorted(target_set):
        node = ctx.nodes[label]
        blocks.append(
            f"## FAILING NODE {label} ({node.kind}; uses "
            f"[{', '.join(sorted(node.uses)) or 'none'}])\n"
            f"```tex\n{ctx.tex_blocks.get(label, '')[:5000]}\n```"
        )
    dep_blocks: list[str] = []
    used = 0
    for label in sorted(_dependency_closure(ctx.nodes, sorted(target_set)) - target_set):
        piece = (
            f"### dependency {label} ({ctx.nodes[label].kind})\n"
            f"```tex\n{ctx.stmt_blocks.get(label, '')[:1500]}\n```"
        )
        if used + len(piece) > dep_budget:
            dep_blocks.append(
                f"### (further dependencies omitted for space, starting at {label})"
            )
            break
        dep_blocks.append(piece)
        used += len(piece)
    consumer_blocks: list[str] = []
    used = 0
    consumers = sorted(
        label
        for label, node in ctx.nodes.items()
        if node.uses & target_set and label not in target_set
    )[:8]
    for label in consumers:
        piece = (
            f"### immediate consumer {label} ({ctx.nodes[label].kind})\n"
            f"```tex\n{ctx.stmt_blocks.get(label, '')[:1200]}\n```"
        )
        if used + len(piece) > consumer_budget:
            break
        consumer_blocks.append(piece)
        used += len(piece)
    parts = ["\n\n".join(blocks) or "(failing nodes no longer present in the blueprint)"]
    parts.append(
        "Dependency closure of the failing nodes (statements only):\n"
        + ("\n\n".join(dep_blocks) or "- none")
    )
    parts.append(
        "Immediate consumers of the failing nodes (statements only; their "
        "statements must keep compiling unchanged):\n"
        + ("\n\n".join(consumer_blocks) or "- none")
    )
    return "\n\n".join(parts)


def _phase2_component_repair_rules(ctx: Ctx, labels: list[str]) -> str:
    """Require one Phase-2 edit to expose its complete helper component.

    Phase 1 repairs still optimize statement contracts. Once Phase 2 starts,
    however, a repair follows failed proof work and must not defer the next
    obvious sub-obligation to another expensive Lean-generation cycle.
    """
    if not bool(getattr(ctx, "phase2_started", False)):
        return ""
    roots = ", ".join(labels) or "(none)"
    return f"""
Phase 2 dependency-closed repair requirement:
- The original failing root(s) are: {roots}.
- Repair each root's COMPLETE blueprint proof strategy in this transaction.
- If helpers are needed, add the entire finite dependency-closed helper
  component now, not just the first helper. Every new helper must have a
  mathematically sufficient blueprint proof using existing dependencies or
  other helpers included in this same edit.
- Do not add a helper that merely renames, restates, or postpones an unresolved
  obligation. Trace each new helper down to already established blueprint
  nodes before finishing the edit.
- Keep the original root claim unchanged unless the evidence proves its public
  statement is mathematically wrong. The purpose is to complete its proof
  structure, not weaken it.
"""


def _scoped_blueprint_repair_prompt(
    ctx: Ctx,
    labels: list[str],
    evidence: str,
    trial: int,
    *,
    escalation_note: str = "",
    model_timeout_s: int | None = None,
) -> str:
    escalation_block = f"\nIMPORTANT: {escalation_note}\n" if escalation_note else ""
    budget_block = (
        f"\nThis repair call has a wall-clock budget of about {model_timeout_s} seconds.\n"
        if model_timeout_s
        else ""
    )
    shape = {
        "replacements": {
            label: (
                "complete replacement TeX for this existing node and its "
                "following proof; new helper nodes may appear immediately before it"
            )
            for label in labels
        },
        "notes": "short explanation of the mathematical repair",
    }
    return f"""TASK: RETURN-SCOPED-BLUEPRINT-REPAIR

Trial {trial} failed when Lean checked a disposable implementation generated
from the current blueprint.

You are the blueprint author. Fix the blueprint, not the Lean implementation.
{escalation_block}
{budget_block}

Return exactly one JSON object with this shape:
```json
{json.dumps(shape, indent=2)}
```

The response is data, not a workspace-editing task. Do not inspect or edit
files, run commands, or return the full blueprint. Python will apply these
replacements to the unpublished draft and run every validator itself.

Rules:
{_REPAIR_SCOPE_RULES}
{_phase2_component_repair_rules(ctx, labels)}
- Return every requested target key exactly once, even when its replacement is
  unchanged. Do not return any other pre-existing node as a replacement.
- Each value must contain the target's complete theorem-like environment and
  its following `proof` environment, when present. Definition-like targets
  must contain their complete environment.
- A value may contain brand-new helper nodes immediately before its target.
  Every helper needs a globally unique `\\label{{...}}`, a concrete statement,
  a complete blueprint proof, and explicit `\\uses{{...}}` edges. A helper may
  appear in only one replacement value.
- Preserve all pre-existing non-target labels byte-for-byte by omitting them.
  Python rejects a replacement that contains any such label.
- Do not make the theorem weaker just to satisfy Lean.
- If Lean failed because the blueprint skipped an argument, add the missing
  lemma/proposition/definition as a blueprint node.
- If the statement audit says the generated Lean used abstract tags, erased
  semantics, dropped parameters, or proved only a vacuous/too-weak behavior,
  strengthen the blueprint itself with concrete mathematical content.
- Definitions for new problem nodes must specify real input/output relations,
  promises, thresholds, approximation factors, and yes/no conditions. They
  cannot merely introduce a family tag.
- Construction lemmas must state the actual constructed object and behavior
  equalities/inequalities, not just existence, continuity, or a placeholder
  predicate.
- If a proof needs an unstated dependency, add or correct `\\uses{{...}}`.
- If a statement is mathematically wrong compared with the paper, correct the
  statement in the blueprint.
- When readiness evidence cites `\\notready`, do not merely delete the marker.
  First supply the missing mathematical content. A theorem-like replacement
  must include its complete blueprint proof; a definition-like replacement
  must explicitly define the interface needed by its consumers. Remove
  `\\notready` only in that completed replacement.
- Do not include `\\begin{{document}}`, `\\end{{document}}`, Markdown fences,
  commentary outside the JSON object, or a complete `content.tex` file.

{_HARNESS_CONVENTIONS_NOTE}

{_repair_node_context(ctx, labels)}

Relevant paper context (deterministic excerpt):
<paper>
{_paper_excerpt_for(ctx, labels)}
</paper>

Lean critic output:
```text
{evidence[-12000:]}
```
"""


def _insert_statement_dependencies(
    text: str, label: str, dependencies: Iterable[str]
) -> tuple[str, set[str]]:
    """Add direct ``\\uses`` edges to one node without changing its prose.

    This is intentionally a narrow TeX transformation. The caller validates
    the complete draft and rolls it back unless every requested edge is parsed
    as a statement dependency.
    """
    requested = set(dict.fromkeys(str(dep).strip() for dep in dependencies))
    requested.discard("")
    marker = rf"\label{{{label}}}"
    label_pos = text.find(marker)
    if label_pos < 0 or not requested:
        return text, set()
    begin = text.rfind(r"\begin{", 0, label_pos)
    end = text.find(r"\end{", label_pos)
    if begin < 0 or end < 0:
        return text, set()
    block = text[begin:end]
    uses_match = re.search(r"\\uses\s*\{([^{}]*)\}", block)
    if uses_match is not None:
        existing = {
            item.strip()
            for item in uses_match.group(1).split(",")
            if item.strip()
        }
        added = requested - existing
        if not added:
            return text, set()
        replacement = r"\uses{" + ", ".join(sorted(existing | added)) + "}"
        absolute_start = begin + uses_match.start()
        absolute_end = begin + uses_match.end()
        return text[:absolute_start] + replacement + text[absolute_end:], added

    line_start = text.rfind("\n", 0, label_pos) + 1
    indent = re.match(r"[ \t]*", text[line_start:label_pos]).group(0)
    marker_end = label_pos + len(marker)
    insertion = "\n" + indent + r"\uses{" + ", ".join(sorted(requested)) + "}"
    return text[:marker_end] + insertion + text[marker_end:], requested


def _dependency_path(
    nodes: dict[str, Node], start: str, target: str
) -> list[str] | None:
    """Return one existing dependency path from ``start`` to ``target``."""
    if start == target:
        return [start]
    queue: list[tuple[str, list[str]]] = [(start, [start])]
    seen = {start}
    index = 0
    while index < len(queue):
        current, path = queue[index]
        index += 1
        node = nodes.get(current)
        if node is None:
            continue
        for dependency in sorted(node.uses):
            if dependency == target:
                return [*path, dependency]
            if dependency in nodes and dependency not in seen:
                seen.add(dependency)
                queue.append((dependency, [*path, dependency]))
    return None


def _cyclic_dependency_repair_findings(
    nodes: dict[str, Node], required_dependencies: dict[str, set[str]]
) -> dict[str, dict[str, str]]:
    """Describe proposed edges that would close a dependency cycle."""
    findings: dict[str, dict[str, str]] = {}
    for label, dependencies in required_dependencies.items():
        if label not in nodes:
            continue
        for dependency in dependencies:
            if dependency not in nodes:
                continue
            path = _dependency_path(nodes, dependency, label)
            if path is None:
                continue
            findings.setdefault(label, {})[dependency] = (
                f"reject `{label} -> {dependency}`: existing dependency path "
                + " -> ".join(path)
                + f" would close the cycle back to {dependency}"
            )
    return findings


def _mark_repair_boundary_pending(
    ctx: Ctx,
    changed: Iterable[str],
    previous_nodes: dict[str, Node],
    *,
    previous_statement_blocks: Mapping[str, str],
    previous_statement_fps: Mapping[str, str],
    repair_roots: Iterable[str] = (),
    failure_evidence: str = "",
) -> set[str]:
    """Persist blueprint mutations that need an early component audit.

    Full contract fingerprints also change for proof-prose edits. Those edits
    do not need this extra pre-generation call during Phase 1. During Phase 2,
    the same edit is part of a failed proof repair, so retain the original root
    and evidence and verify that the complete helper component resolves it
    before paying for another Lean generation cycle.
    """
    changed_set = {label for label in changed if label in ctx.nodes}
    roots = {
        label for label in repair_roots if label in ctx.nodes
    }
    # ``Node`` stores only a file path and source position. Re-extracting TeX
    # from ``previous_nodes`` after a model edit therefore reads the *new* file
    # and can make an existing-node statement repair look unchanged. Callers
    # must pass the immutable text/fingerprints captured before the edit.
    before_statements = dict(previous_statement_blocks)
    before_fps = dict(previous_statement_fps)
    statement_changed = {
        label
        for label in changed_set
        if before_fps.get(label) != ctx.stmt_fps.get(label)
    }
    phase2_component = bool(getattr(ctx, "phase2_started", False)) and bool(roots)
    labels = (
        changed_set | roots
        if phase2_component
        else statement_changed
    )
    if not labels:
        return set()
    ordered = sorted(
        labels,
        key=lambda label: (ctx.nodes[label].file, ctx.nodes[label].line, label),
    )
    ctx.repair_boundary_pending = {
        "mode": "audit",
        "labels": ordered,
        "statement_fps": {label: ctx.stmt_fps[label] for label in ordered},
        "previous_statements": {
            label: before_statements.get(label, "") for label in ordered
        },
        "evidence": failure_evidence[-12000:],
        "repair_roots": sorted(roots),
        "component_changed_labels": sorted(changed_set),
        "component_added_labels": sorted(set(ctx.nodes) - set(previous_nodes)),
        "require_component_closure": phase2_component,
        "repair_labels": [],
        "required_dependencies": {},
        "decomposition_helpers": [],
    }
    _record(
        ctx.telemetry,
        "post_repair_boundary_queued",
        labels=ordered,
        count=len(ordered),
        repair_roots=sorted(roots),
        component_changed_labels=sorted(changed_set),
        require_component_closure=phase2_component,
    )
    return set(ordered)


def _post_repair_boundary_prompt(ctx: Ctx, labels: list[str]) -> str:
    """Build the one scoped blueprint-only audit used after a repair."""
    pending = ctx.repair_boundary_pending
    previous = pending.get("previous_statements") or {}
    roots = [
        label
        for label in pending.get("repair_roots") or []
        if label in ctx.nodes
    ]
    changed = [
        label
        for label in pending.get("component_changed_labels") or labels
        if label in ctx.nodes
    ]
    closure_required = bool(pending.get("require_component_closure"))
    provider_candidates = (
        _phase2_provider_contract_candidates(ctx, roots)
        if closure_required
        else set()
    )
    changed_blocks = []
    for label in labels:
        node = ctx.nodes[label]
        changed_blocks.append(
            f"## {label} ({node.kind})\n"
            f"Previous public statement:\n```tex\n{str(previous.get(label) or '(new node)')[:6000]}\n```\n"
            f"Repaired public statement:\n```tex\n{ctx.stmt_blocks.get(label, '')[:6000]}\n```\n"
            f"Complete current blueprint node (statement and proof):\n"
            f"```tex\n{ctx.tex_blocks.get(label, '')[:10000]}\n```\n"
            f"Current statement dependencies: "
            f"{', '.join(sorted(_statement_uses(node))) or '(none)'}"
        )
    target_set = set(labels)
    nearby = target_set | {
        dependency
        for label in labels
        for dependency in ctx.nodes[label].uses
        if dependency in ctx.nodes
    }
    nearby |= {
        label
        for label, node in ctx.nodes.items()
        if node.uses & target_set
    }
    boundary = "\n".join(
        f"- {label} ({ctx.nodes[label].kind}): statement uses "
        f"{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or '(none)'}"
        for label in sorted(nearby)
    )
    paper = _paper_excerpt_for(ctx, labels, budget=12000)
    component_requirement = ""
    if closure_required:
        component_requirement = f"""
This is a Phase 2 proof-repair boundary. The original failing root(s) are:
{chr(10).join(f'- {label}' for label in roots) or '- (missing)'}

The repair changed this component:
{chr(10).join(f'- {label}' for label in changed) or '- (none)'}

Original Lean/audit evidence that authorized the repair:
```text
{str(pending.get('evidence') or '')[-12000:]}
```

Accept only if the complete blueprint proofs now form a dependency-closed
strategy that addresses that evidence. In particular, every newly introduced
helper must itself be justified from existing nodes or other helpers included
in this same component. Reject a helper that merely postpones another obvious
sub-obligation. When more helpers are required, report all foreseeable missing
helper statements together rather than only the first one.
"""
    return f"""TASK: AUDIT-MODEL-BLUEPRINT-REPAIR-BOUNDARY

A model just edited the public statements below. Before spending Lean
generation and compilation calls, check only whether the repaired component is
self-consistent and has the statement-scoped dependencies required to state
what it now claims.

This is NOT a Lean-code audit. For Phase 2 component repairs, audit only whether
the blueprint proof structure closes the original failure; do not reject
stylistic proof changes, request Lean implementation details, or demand that
proof-only lemmas occur in public statements. The blueprint remains the source
of truth.
{component_requirement}

Return exactly one JSON object:
{{
  "accepted": true,
  "issues": [
    {{
      "node": "existing blueprint label",
      "severity": "reject",
      "classification": "missing_statement_dependency | blueprint_contract_defect | provider_contract_defect | needs_decomposition",
      "reason": "specific mathematical defect in the repaired statement",
      "required_dependencies": ["existing label needed by the public statement"],
      "missing_helpers": ["helper statement needed to express the claim"]
    }}
  ]
}}

Rules:
- Accept when the repaired statement is complete as written.
- Before accepting a correspondence, equivalence, transport, or existence
  claim that depends on a particular map, isomorphism, coordinate system, or
  witness, require the repaired blueprint to identify that witness (directly
  or through an existing statement dependency) and state the equations or
  behavior needed by the claim and its downstream consumers. Phrases such as
  "under a suitable isomorphism" are not complete when the witness, its
  domain/codomain, or its required action remains unnamed.
- Do not apply the preceding rule to an ordinary existential theorem whose
  mathematical content is complete without fixing one distinguished witness.
  It applies only when the claim or later declarations depend on a particular
  witness or on specific properties of its action.
- Use `missing_statement_dependency` only when an existing blueprint node is
  semantically required by the repaired PUBLIC statement and its direct
  statement `\\uses` edge is absent.
- Do not request a dependency merely because its theorem is useful in a proof.
- Use `blueprint_contract_defect` only for concrete missing or contradictory
  mathematical content introduced or left unresolved by the repair.
- Use `provider_contract_defect` only when the changed node correctly relies on
  an EXISTING dependency whose unchanged public contract lacks specific
  mathematical content required by the blueprint proof. Name that dependency,
  not the changed consumer. Eligible provider labels are listed below. This
  classification requests a separate provider-owned transaction; it must not
  be used for a Lean implementation error or a merely useful proof lemma.
- Use `needs_decomposition` only when the repaired public claim still bundles
  genuinely separate obligations that require explicit blueprint helper nodes,
  or when a Phase 2 helper component does not yet close the original repaired
  root's blueprint proof.
- Never suggest weakening, deleting, or replacing a claim with a placeholder.
- Every issue except `provider_contract_defect` must name one of the changed
  labels. A `provider_contract_defect` must name one of the eligible unchanged
  providers below. Every required dependency must be an existing label from
  the label inventory.

Eligible unchanged provider contracts from the original repair root's existing
blueprint dependency closure:
{chr(10).join(f'- {label}' for label in sorted(provider_candidates)) or '- (none)'}

Changed statements:
{chr(10).join(changed_blocks)}

Immediate dependency/consumer boundary:
{boundary}

Existing label inventory:
{chr(10).join(f'- {label} ({node.kind})' for label, node in sorted(ctx.nodes.items()))}

Relevant paper excerpt:
<paper>
{paper}
</paper>
"""


def _phase2_provider_contract_candidates(ctx: Ctx, roots: Iterable[str]) -> set[str]:
    """Existing dependencies that may own a Phase-2 boundary defect.

    Provider ownership is intentionally narrower than graph proximity: only a
    dependency already reachable from an original repair root can be named.
    Consumers, siblings, invented labels, and newly proposed graph edges never
    gain edit authority through this route.
    """
    root_set = {str(label) for label in roots if str(label) in ctx.nodes}
    return {
        dependency
        for root in root_set
        for dependency in _transitive_dependencies(ctx.nodes, root)
        if dependency in ctx.nodes
        and dependency not in root_set
        and not ctx.nodes[dependency].mathlibok
    }


def _audit_post_repair_boundary(
    ctx: Ctx, labels: list[str]
) -> RepairBoundaryAuditOutcome:
    """Audit one repaired component once; failures fall back to later gates."""
    repair_roots = list(
        ctx.repair_boundary_pending.get("repair_roots") or []
    )
    component_changed = list(
        ctx.repair_boundary_pending.get("component_changed_labels") or []
    )
    component_closure = bool(
        ctx.repair_boundary_pending.get("require_component_closure")
    )
    provider_candidates = (
        _phase2_provider_contract_candidates(ctx, repair_roots)
        if component_closure
        else set()
    )
    prompt = _post_repair_boundary_prompt(ctx, labels)
    result = _call_model(
        ctx,
        prompt,
        purpose="post_repair_blueprint_audit",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=labels,
        tag="repair-boundary",
    )
    if result.status != "ok":
        _record(
            ctx.telemetry,
            "post_repair_boundary_audit",
            labels=labels,
            status="unavailable",
            reason=result.error,
            repair_roots=repair_roots,
            component_changed_labels=component_changed,
            require_component_closure=component_closure,
        )
        return RepairBoundaryAuditOutcome("unavailable", result.error)
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        _record(
            ctx.telemetry,
            "post_repair_boundary_audit",
            labels=labels,
            status="unavailable",
            reason=str(exc),
            repair_roots=repair_roots,
            component_changed_labels=component_changed,
            require_component_closure=component_closure,
        )
        return RepairBoundaryAuditOutcome("unavailable", str(exc))

    issues = [item for item in payload.get("issues") or [] if isinstance(item, dict)]
    rejected_issues = [
        item
        for item in issues
        if str(item.get("severity") or "reject").lower() == "reject"
    ]
    if bool(payload.get("accepted")) and not rejected_issues:
        _record(
            ctx.telemetry,
            "post_repair_boundary_audit",
            labels=labels,
            status="accepted",
            issue_count=0,
            repair_roots=repair_roots,
            component_changed_labels=component_changed,
            require_component_closure=component_closure,
        )
        return RepairBoundaryAuditOutcome("accepted")

    label_set = set(labels)
    required: dict[str, set[str]] = {}
    repair_labels: set[str] = set()
    provider_repair_labels: set[str] = set()
    helpers: list[str] = []
    formatted: list[str] = []
    for issue in rejected_issues:
        label = str(issue.get("node") or "")
        classification = str(issue.get("classification") or "")
        provider_issue = (
            classification == "provider_contract_defect"
            and label in provider_candidates
            and label not in label_set
        )
        if label not in label_set and not provider_issue:
            continue
        reason = str(issue.get("reason") or "unspecified repair defect").strip()
        formatted.append(f"{label} [{classification or 'unclassified'}]: {reason}")
        if provider_issue:
            provider_repair_labels.add(label)
            continue
        dependencies = {
            str(dep).strip()
            for dep in issue.get("required_dependencies") or []
            if str(dep).strip() in ctx.nodes and str(dep).strip() != label
        }
        if dependencies:
            required.setdefault(label, set()).update(dependencies)
        if classification != "missing_statement_dependency" or not dependencies:
            repair_labels.add(label)
        if classification == "needs_decomposition":
            helpers.extend(
                str(item).strip()
                for item in issue.get("missing_helpers") or []
                if str(item).strip()
            )
    if not formatted:
        repair_labels = set(labels)
        formatted = [
            "The repair-boundary critic rejected the component without usable "
            "per-node routing evidence. Recheck the changed public statements."
        ]
    boundary_evidence = (
        "Post-repair blueprint boundary audit rejected:\n- "
        + "\n- ".join(formatted)
    )
    original_evidence = str(
        ctx.repair_boundary_pending.get("evidence") or ""
    ).strip()
    evidence = (
        original_evidence + "\n\n" + boundary_evidence
        if original_evidence
        else boundary_evidence
    )[-20000:]
    _record(
        ctx.telemetry,
        "post_repair_boundary_audit",
        labels=labels,
        status="repair_required",
        repair_labels=sorted(repair_labels),
        required_dependencies={
            label: sorted(dependencies)
            for label, dependencies in required.items()
        },
        decomposition_helpers=list(dict.fromkeys(helpers)),
        provider_repair_labels=sorted(provider_repair_labels),
        issue_count=len(formatted),
        repair_roots=repair_roots,
        component_changed_labels=component_changed,
        require_component_closure=component_closure,
    )
    return RepairBoundaryAuditOutcome(
        "repair",
        evidence,
        tuple(sorted(repair_labels)),
        required,
        tuple(dict.fromkeys(helpers)),
        tuple(sorted(provider_repair_labels)),
    )


def _pending_repair_boundary_request(ctx: Ctx) -> RepairRequest | None:
    """Resume or perform the persisted post-repair boundary transaction."""
    pending = ctx.repair_boundary_pending
    if not pending:
        return None

    mode = str(pending.get("mode") or "audit")
    if mode == "repair":
        provider_repair_labels = [
            label
            for label in pending.get("provider_repair_labels") or []
            if label in ctx.nodes
            and bool((pending.get("provider_statement_fps") or {}).get(label))
            and (pending.get("provider_statement_fps") or {}).get(label)
            == ctx.stmt_fps.get(label)
        ]
        if provider_repair_labels:
            request = RepairRequest(
                str(
                    pending.get("evidence")
                    or "A dependency provider contract is insufficient."
                ),
                provider_repair_labels,
                section_labels=provider_repair_labels,
                context_labels=list(
                    dict.fromkeys(
                        [
                            *provider_repair_labels,
                            *[str(label) for label in pending.get("repair_roots") or []],
                        ]
                    )
                ),
                authorizes_blueprint_repair=True,
                model_repair_labels=provider_repair_labels,
                evidence_by_label={
                    label: str(pending.get("evidence") or "")[-12000:]
                    for label in provider_repair_labels
                },
                provider_contract_labels=provider_repair_labels,
                reschedule_labels=[
                    str(label) for label in pending.get("repair_roots") or []
                ],
            )
            return request

        stored_required = {
            label: {
                dependency
                for dependency in dependencies
                if label in ctx.nodes and dependency in ctx.nodes
            }
            for label, dependencies in (
                pending.get("required_dependencies") or {}
            ).items()
        }
        required_dependencies = {
            label: dependencies - set(_statement_uses(ctx.nodes[label]))
            for label, dependencies in stored_required.items()
            if label in ctx.nodes
        }
        required_dependencies = {
            label: dependencies
            for label, dependencies in required_dependencies.items()
            if dependencies
        }

        # An explicitly empty list means the boundary audit authorized only a
        # deterministic dependency edit.  Preserve that distinction; using
        # ``or labels`` here would silently authorize a model blueprint repair.
        if "repair_labels" in pending:
            candidate_model_labels = list(pending.get("repair_labels") or [])
        else:
            # Backward compatibility for state written before repair scopes
            # were stored separately from dependency-only actions.
            candidate_model_labels = (
                [] if stored_required else list(pending.get("labels") or [])
            )
        model_repair_labels = [
            label
            for label in candidate_model_labels
            if label in ctx.nodes
            and (
                (pending.get("statement_fps") or {}).get(label)
                == ctx.stmt_fps.get(label)
                # A certified edge may have been written immediately before
                # interruption, changing the target fingerprint while an
                # independent model repair for that same target is still
                # pending.  The now-present requested edge accounts for that
                # transaction-owned mutation; do not lose the other action.
                or bool(
                    stored_required.get(label, set())
                    & set(_statement_uses(ctx.nodes[label]))
                )
            )
        ]
        request_labels = list(
            dict.fromkeys([*model_repair_labels, *required_dependencies])
        )
        if not request_labels:
            # Every certified edge is already present and no independent model
            # repair remains.  This also makes continuation idempotent if the
            # process stopped after editing TeX but before clearing state.
            ctx.repair_boundary_pending = {}
            _record(
                ctx.telemetry,
                "post_repair_boundary_completed",
                status="dependency_actions_satisfied",
                labels=sorted(stored_required),
            )
            return None
        return RepairRequest(
            str(pending.get("evidence") or "Post-repair boundary audit rejected."),
            request_labels,
            decomposition_helpers=list(pending.get("decomposition_helpers") or []),
            authorizes_blueprint_repair=bool(model_repair_labels),
            required_dependencies=required_dependencies,
            model_repair_labels=model_repair_labels,
        )

    labels = [
        label
        for label in pending.get("labels") or []
        if label in ctx.nodes
        and (pending.get("statement_fps") or {}).get(label) == ctx.stmt_fps.get(label)
    ]
    if not labels:
        ctx.repair_boundary_pending = {}
        return None

    _log(
        "==> Auditing repaired blueprint component before Lean generation: "
        + ", ".join(labels[:8])
    )
    outcome = _audit_post_repair_boundary(ctx, labels)
    if outcome.status in {"accepted", "unavailable"}:
        ctx.repair_boundary_pending = {}
        if outcome.status == "unavailable":
            _log(
                "  repair-boundary audit unavailable; continuing to the existing "
                "mandatory Lean statement-alignment gate"
            )
        else:
            _log("  repaired blueprint component passed its scoped boundary audit")
        return None
    ctx.repair_boundary_pending = {
        **pending,
        "mode": "repair",
        "evidence": outcome.evidence,
        "repair_labels": list(outcome.repair_labels),
        "provider_repair_labels": list(outcome.provider_repair_labels),
        "provider_statement_fps": {
            label: ctx.stmt_fps.get(label)
            for label in outcome.provider_repair_labels
        },
        "required_dependencies": {
            label: set(dependencies)
            for label, dependencies in outcome.required_dependencies.items()
        },
        "decomposition_helpers": list(outcome.decomposition_helpers),
    }
    return _pending_repair_boundary_request(ctx)


def _apply_required_dependency_edges(
    ctx: Ctx, required_dependencies: dict[str, set[str]]
) -> set[str]:
    """Transactionally add critic-and-Lean-confirmed statement graph edges."""
    normalized = {
        label: {
            dep
            for dep in dependencies
            if label in ctx.nodes and dep in ctx.nodes
        }
        for label, dependencies in required_dependencies.items()
    }
    normalized = {label: deps for label, deps in normalized.items() if deps}
    cycle_findings = _cyclic_dependency_repair_findings(ctx.nodes, normalized)
    ctx.last_dependency_edge_rejections = cycle_findings
    if cycle_findings:
        rejected_dependency_observations = {
            label: set(rejected)
            for label, rejected in cycle_findings.items()
        }
        for label, rejected in cycle_findings.items():
            normalized[label].difference_update(rejected)
        normalized = {label: deps for label, deps in normalized.items() if deps}
        messages = [
            message
            for rejected in cycle_findings.values()
            for message in rejected.values()
        ]
        _log(
            "==> Rejected cyclic blueprint dependency repair(s):\n  - "
            + "\n  - ".join(messages)
        )
        _record(
            ctx.telemetry,
            "blueprint_dependency_edge_repair",
            labels=sorted(cycle_findings),
            status="cycle_rejected",
            rejected_dependencies={
                label: dict(rejected)
                for label, rejected in cycle_findings.items()
            },
        )
        _clear_phase1_dependency_observations(
            ctx, rejected_dependency_observations
        )
    if not normalized:
        return set()

    paths = {ctx.nodes[label].file for label in normalized}
    before = {path: path.read_text(encoding="utf-8") for path in paths}
    added_by_label: dict[str, set[str]] = {}
    try:
        for label, dependencies in normalized.items():
            path = ctx.nodes[label].file
            current = path.read_text(encoding="utf-8")
            updated, added = _insert_statement_dependencies(
                current, label, dependencies
            )
            if added:
                path.write_text(updated, encoding="utf-8")
                added_by_label[label] = added

        validation = _validate_draft(ctx)
        if not validation.ok:
            raise ValueError("dependency-edge edit made the blueprint invalid")
        for label, dependencies in added_by_label.items():
            parsed = validation.nodes.get(label)
            if parsed is None or not dependencies <= set(parsed.statement_uses):
                raise ValueError(
                    f"validator did not parse required dependency edges for {label}"
                )
        ctx.refresh_nodes(validation.nodes)
    except (OSError, ValueError):
        for path, text in before.items():
            path.write_text(text, encoding="utf-8")
        restored = _validate_draft(ctx)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        _record(
            ctx.telemetry,
            "blueprint_dependency_edge_repair",
            labels=sorted(normalized),
            status="rolled_back",
            required_dependencies={
                label: sorted(dependencies)
                for label, dependencies in normalized.items()
            },
        )
        return set()

    changed = set(added_by_label)
    _clear_phase1_dependency_observations(ctx, normalized)
    _record(
        ctx.telemetry,
        "blueprint_dependency_edge_repair",
        labels=sorted(changed),
        status="applied",
        required_dependencies={
            label: sorted(dependencies)
            for label, dependencies in added_by_label.items()
        },
    )
    if changed:
        _log(
            "==> Deterministic blueprint dependency repair: "
            + "; ".join(
                f"{label} -> {', '.join(sorted(added_by_label[label]))}"
                for label in sorted(changed)
            )
        )
    return changed


@dataclass(frozen=True)
class _ScopedBlueprintRepairProposal:
    labels: tuple[str, ...]
    response_text: str
    duration_s: float
    repaired_json_backslashes: int


def _run_scoped_blueprint_repair_proposal(
    ctx: Ctx,
    labels: list[str],
    evidence: str,
    *,
    trial: int,
    escalation_note: str,
) -> _ScopedBlueprintRepairProposal:
    """Run and parse one read-only proposal without mutating the draft."""
    prompt = _scoped_blueprint_repair_prompt(
        ctx,
        labels,
        evidence,
        trial,
        escalation_note=escalation_note,
        model_timeout_s=ctx.hard_timeout,
    )
    prompt_artifact = _store_text(
        ctx.telemetry, "prompt_blueprint_repair", prompt
    )
    runner = _make_runner(
        ctx.escalation_runner_spec,
        timeout=ctx.hard_timeout,
        readonly=True,
        effort=ctx.escalation_effort,
        with_skill=True,
    )
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        duration = time.monotonic() - started
        status = _runner_failure_status(exc)
        _record(
            ctx.telemetry,
            "model_call",
            purpose="blueprint_repair",
            labels=labels,
            status=status,
            duration_s=duration,
            timeout_s=ctx.hard_timeout,
            backend=runner.backend_name,
            model=runner.model,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
            transport_error=status == "transport_exhausted",
            partitioned=True,
        )
        raise
    duration = time.monotonic() - started
    response_artifact = _store_text(
        ctx.telemetry, "response_blueprint_repair", result.text
    )
    _record(
        ctx.telemetry,
        "model_call",
        purpose="blueprint_repair",
        labels=labels,
        status="success",
        duration_s=duration,
        timeout_s=ctx.hard_timeout,
        backend=runner.backend_name,
        model=runner.model,
        prompt=prompt_artifact.to_event(REPO_ROOT),
        response=response_artifact.to_event(REPO_ROOT),
        partitioned=True,
    )
    payload, repaired_backslashes = _extract_json_object_with_key(
        result.text, "replacements"
    )
    replacements = payload.get("replacements")
    if not isinstance(replacements, Mapping):
        raise ValueError("repair JSON did not include a replacements object")
    returned = {str(label).strip() for label in replacements}
    expected = set(labels)
    if returned != expected:
        missing = sorted(expected - returned)
        unexpected = sorted(returned - expected)
        details = []
        if missing:
            details.append("missing target(s): " + ", ".join(missing))
        if unexpected:
            details.append("unauthorized target(s): " + ", ".join(unexpected))
        raise ValueError(
            "scoped repair target mismatch (" + "; ".join(details) + ")"
        )
    return _ScopedBlueprintRepairProposal(
        labels=tuple(labels),
        response_text=result.text,
        duration_s=duration,
        repaired_json_backslashes=repaired_backslashes,
    )


def _normalized_parallel_repair_components(
    labels: list[str], components: Iterable[Mapping[str, Any]]
) -> list[dict[str, Any]]:
    """Return disjoint component scopes only when they cover the transaction."""
    expected = set(labels)
    normalized: list[dict[str, Any]] = []
    seen: set[str] = set()
    for component in components:
        component_labels = list(
            dict.fromkeys(
                str(label)
                for label in component.get("labels") or []
                if str(label) in expected
            )
        )
        if not component_labels or seen.intersection(component_labels):
            return []
        seen.update(component_labels)
        normalized.append(
            {
                "labels": component_labels,
                "evidence": str(component.get("evidence") or "")[-24000:],
            }
        )
    if seen != expected or len(normalized) < 2:
        return []
    return normalized


def _repair_blueprint_components(
    ctx: Ctx,
    evidence: str,
    labels: list[str],
    *,
    trial: int,
    max_trials: int,
    escalation_note: str,
    repair_runner_agent: bool,
    decomposition_roots: Iterable[str] = (),
    repair_components: Iterable[Mapping[str, Any]] = (),
) -> set[str]:
    """Propose independent repairs concurrently, then commit once atomically."""
    components = _normalized_parallel_repair_components(labels, repair_components)
    if not components:
        return _repair_blueprint(
            ctx,
            evidence,
            labels,
            trial=trial,
            max_trials=max_trials,
            escalation_note=escalation_note,
            repair_runner_agent=repair_runner_agent,
            decomposition_roots=decomposition_roots,
        )

    worker_count = max(1, min(ctx.workers, len(components)))
    _log(
        f"==> Blueprint repair {trial}/{max_trials}: proposing "
        f"{len(components)} independent component(s) with {worker_count} worker(s)"
    )
    _record(
        ctx.telemetry,
        "blueprint_repair_partition_started",
        labels=labels,
        components=[component["labels"] for component in components],
        workers=worker_count,
        atomic_commit=True,
    )
    started = time.monotonic()
    proposals: list[_ScopedBlueprintRepairProposal] = []
    try:
        with concurrent.futures.ThreadPoolExecutor(
            max_workers=worker_count
        ) as pool:
            futures = [
                pool.submit(
                    _run_scoped_blueprint_repair_proposal,
                    ctx,
                    component["labels"],
                    component["evidence"] or evidence,
                    trial=trial,
                    escalation_note=escalation_note,
                )
                for component in components
            ]
            for future in concurrent.futures.as_completed(futures):
                proposals.append(future.result())
    except (RunnerError, ValueError) as exc:
        _record(
            ctx.telemetry,
            "blueprint_repair_partition_result",
            labels=labels,
            status="proposal_failed",
            duration_s=time.monotonic() - started,
            reason=str(exc),
            atomic_commit=True,
        )
        if isinstance(exc, RunnerError) and (
            is_environment_error(exc) or is_transient_error(exc)
        ):
            raise
        _log(f"  partitioned blueprint repair produced no draft edit: {exc}")
        return set()

    replacements: dict[str, str] = {}
    notes: list[str] = []
    repaired_backslashes = 0
    for proposal in proposals:
        payload, repaired = _extract_json_object_with_key(
            proposal.response_text, "replacements"
        )
        raw = payload.get("replacements")
        if not isinstance(raw, Mapping):
            return set()
        overlap = set(replacements).intersection(str(label) for label in raw)
        if overlap:
            _record(
                ctx.telemetry,
                "blueprint_repair_partition_result",
                labels=labels,
                status="overlap_rejected",
                overlapping_labels=sorted(overlap),
                atomic_commit=True,
            )
            return set()
        replacements.update({str(label): str(value) for label, value in raw.items()})
        note = str(payload.get("notes") or "").strip()
        if note:
            notes.append(note)
        repaired_backslashes += repaired

    merged_response = json.dumps(
        {"replacements": replacements, "notes": "\n".join(notes)}
    )
    _record(
        ctx.telemetry,
        "blueprint_repair_partition_result",
        labels=labels,
        status="proposals_merged",
        duration_s=time.monotonic() - started,
        component_durations_s={
            ",".join(proposal.labels): proposal.duration_s
            for proposal in proposals
        },
        repaired_json_backslashes=repaired_backslashes,
        atomic_commit=True,
    )
    return _repair_blueprint(
        ctx,
        evidence,
        labels,
        trial=trial,
        max_trials=max_trials,
        escalation_note=escalation_note,
        repair_runner_agent=repair_runner_agent,
        decomposition_roots=decomposition_roots,
        prepared_response=merged_response,
    )


def _repair_blueprint(
    ctx: Ctx,
    evidence: str,
    labels: list[str],
    *,
    trial: int,
    max_trials: int,
    escalation_note: str,
    repair_runner_agent: bool,
    decomposition_roots: Iterable[str] = (),
    prepared_response: str | None = None,
) -> set[str]:
    """Run one transactional blueprint-repair attempt.

    Every provider returns scoped replacement data and runs read-only. Python
    applies that data to the immutable pre-call source, so neither an agent nor
    an API response can rewrite unrelated blueprint nodes. The caller treats an
    empty result as a consumed no-op repair and continues until the configured
    repair budget is exhausted. ``repair_runner_agent`` remains in the call
    signature for compatibility with the existing coordinator, but no longer
    changes the repair protocol.
    """
    content_path = ctx.content_path
    before_content = content_path.read_text(encoding="utf-8")
    before_nodes = dict(ctx.nodes)
    before_blocks = dict(ctx.tex_blocks)
    before_fps = dict(ctx.contract_fps)
    ctx.last_blueprint_repair_rejection = ""
    _log(f"==> Blueprint repair {trial}/{max_trials} for: " + ", ".join(labels[:8]))
    prompt = _scoped_blueprint_repair_prompt(
        ctx,
        labels,
        evidence,
        trial,
        escalation_note=escalation_note,
        model_timeout_s=ctx.hard_timeout,
    )
    prompt_artifact = _store_text(ctx.telemetry, "prompt_blueprint_repair", prompt)
    runner = None
    try:
        if prepared_response is None:
            runner = _make_runner(
                ctx.escalation_runner_spec,
                timeout=ctx.hard_timeout,
                readonly=True,
                effort=ctx.escalation_effort,
                with_skill=True,
            )
    except RunnerError as exc:
        _record(
            ctx.telemetry,
            "model_call",
            purpose="blueprint_repair",
            labels=labels,
            status="error",
            duration_s=0.0,
            timeout_s=ctx.hard_timeout,
            backend=ctx.escalation_runner_spec.partition(":")[0],
            model=ctx.escalation_runner_spec.partition(":")[2],
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
            transport_error=is_transient_error(exc),
        )
        _record(
            ctx.telemetry,
            "blueprint_repair_result",
            labels=labels,
            status="runner_error",
            changed_labels=[],
            changed_count=0,
            reason=str(exc),
        )
        if is_environment_error(exc) or is_transient_error(exc):
            raise
        return set()
    started = time.monotonic()
    try:
        if prepared_response is None:
            assert runner is not None
            result_text = runner.run(
                prompt, cwd=REPO_ROOT, retries=0
            ).text
        else:
            result_text = prepared_response
    except RunnerError as exc:
        duration = time.monotonic() - started
        status = _runner_failure_status(exc)
        _record(
            ctx.telemetry,
            "model_call",
            purpose="blueprint_repair",
            labels=labels,
            status=status,
            duration_s=duration,
            timeout_s=ctx.hard_timeout,
            backend=runner.backend_name if runner is not None else "",
            model=runner.model if runner is not None else "",
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
            transport_error=status == "transport_exhausted",
        )
        # Restore defensively even though every repair runner is read-only.
        content_path.write_text(before_content, encoding="utf-8")
        restored = _validate_draft(ctx)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        if is_environment_error(exc) or status == "transport_exhausted":
            raise
        if status == "timeout" and len(labels) > 1 and not is_environment_error(exc):
            mid = len(labels) // 2
            _log(
                "  blueprint repair timed out; splitting target into "
                + f"{mid} + {len(labels) - mid} label(s)"
            )
            left = _repair_blueprint(
                ctx,
                evidence,
                labels[:mid],
                trial=trial,
                max_trials=max_trials,
                escalation_note=escalation_note,
                repair_runner_agent=repair_runner_agent,
                decomposition_roots=decomposition_roots,
            )
            right = _repair_blueprint(
                ctx,
                evidence,
                labels[mid:],
                trial=trial,
                max_trials=max_trials,
                escalation_note=escalation_note,
                repair_runner_agent=repair_runner_agent,
                decomposition_roots=decomposition_roots,
            )
            return left | right
        _record(
            ctx.telemetry,
            "blueprint_repair_result",
            labels=labels,
            status=status,
            changed_labels=[],
            changed_count=0,
            reason=str(exc),
        )
        return set()
    if prepared_response is None:
        assert runner is not None
        _record(
            ctx.telemetry,
            "model_call",
            purpose="blueprint_repair",
            labels=labels,
            status="success",
            duration_s=time.monotonic() - started,
            timeout_s=ctx.hard_timeout,
            backend=runner.backend_name,
            model=runner.model,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            response=_store_text(
                ctx.telemetry, "response_blueprint_repair", result_text
            ).to_event(REPO_ROOT),
        )
    try:
        scoped_metadata = _write_scoped_blueprint_repair_to(
            content_path,
            result_text,
            original_content=before_content,
            requested_labels=labels,
            existing_blocks=before_blocks,
            existing_labels=before_nodes,
        )
        _record(
            ctx.telemetry,
            "blueprint_repair_scoped_application",
            labels=labels,
            protocol="scoped_replacements_v1",
            runner_mode="agent" if repair_runner_agent else "api",
            replacement_labels=scoped_metadata["replacement_labels"],
            new_helper_labels=scoped_metadata["new_helper_labels"],
            repaired_json_backslashes=scoped_metadata[
                "repaired_json_backslashes"
            ],
        )
        validation = _validate_draft(ctx)
        if not validation.ok:
            print_result(validation)
            raise ValueError("blueprint repair produced an invalid blueprint")
        conjecture_policy = getattr(ctx, "conjecture_policy", "record")
        readiness_labels = [
            label
            for label in labels
            if label in before_nodes
            and not (
                conjecture_policy == "record"
                and _is_conjecture_node(label, before_nodes[label])
            )
            and (
                bool(getattr(before_nodes[label], "notready", False))
                or (
                    conjecture_policy == "attempt"
                    and _is_conjecture_node(label, before_nodes[label])
                    and not _blueprint_block_has_proof(
                        str(before_blocks.get(label, ""))
                    )
                )
            )
        ]
        readiness_findings = (
            _readiness_repair_postcondition_findings(
                before_nodes=before_nodes,
                after_nodes=validation.nodes,
                before_blocks=before_blocks,
                after_blocks=_node_tex_blocks(validation.nodes),
                labels=readiness_labels,
                conjecture_policy=conjecture_policy,
            )
            if readiness_labels
            else []
        )
        if readiness_findings:
            raise ValueError(
                "blueprint readiness repair did not resolve its source contract:\n- "
                + "\n- ".join(readiness_findings)
            )
        orientation_findings = _decomposition_orientation_findings(
            before_nodes, validation.nodes, decomposition_roots
        )
        if orientation_findings:
            orientation_edges = _decomposition_orientation_dependency_edges(
                before_nodes, validation.nodes, decomposition_roots
            )
            if orientation_edges:
                ctx.refresh_nodes(validation.nodes)
                edge_changed = _apply_required_dependency_edges(
                    ctx, orientation_edges
                )
                validation = _validate_draft(ctx)
                remaining_findings = (
                    _decomposition_orientation_findings(
                        before_nodes,
                        validation.nodes if validation.ok else {},
                        decomposition_roots,
                    )
                    if edge_changed and validation.ok
                    else orientation_findings
                )
                if edge_changed and validation.ok and not remaining_findings:
                    _record(
                        ctx.telemetry,
                        "blueprint_decomposition_orientation_edge_repair",
                        labels=labels,
                        status="applied",
                        required_dependencies={
                            label: sorted(dependencies)
                            for label, dependencies in orientation_edges.items()
                        },
                        changed_labels=sorted(edge_changed),
                    )
                    _log(
                        "  fixed decomposition helper direction by adding "
                        "statement dependency edge(s): "
                        + "; ".join(
                            f"{label} -> {', '.join(sorted(dependencies))}"
                            for label, dependencies in orientation_edges.items()
                        )
                    )
                else:
                    raise ValueError(
                        "blueprint decomposition put helper nodes in the wrong "
                        "graph direction:\n- " + "\n- ".join(remaining_findings)
                    )
            else:
                raise ValueError(
                    "blueprint decomposition put helper nodes in the wrong graph "
                    "direction:\n- " + "\n- ".join(orientation_findings)
                )
    except (OSError, ValueError) as exc:
        ctx.last_blueprint_repair_rejection = str(exc)
        content_path.write_text(before_content, encoding="utf-8")
        restored = _validate_draft(ctx)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        _record(
            ctx.telemetry,
            "blueprint_repair_result",
            labels=labels,
            status="invalid_rolled_back",
            changed_labels=[],
            changed_count=0,
            reason=str(exc),
        )
        _log(f"  invalid blueprint repair rolled back: {exc}")
        return set()
    ctx.refresh_nodes(validation.nodes)
    changed = {
        label
        for label, fp in ctx.contract_fps.items()
        if before_fps.get(label) != fp
    }
    changed |= {label for label in before_fps if label not in ctx.contract_fps}
    changed |= {label for label in ctx.contract_fps if label not in before_fps}
    _record(
        ctx.telemetry,
        "blueprint_repair_result",
        labels=labels,
        status="applied" if changed else "noop",
        changed_labels=sorted(changed),
        changed_count=len(changed),
    )
    return changed


def _stuck_state_for(
    states: list[SectionStuckState], section_labels: list[str]
) -> SectionStuckState:
    """Return retry state for one exact editable repair scope.

    Partially overlapping failure sets are not interchangeable: merging them
    can authorize normalization of siblings that have not exhausted their own
    retry lifecycle. Related nodes may still be supplied as read-only prompt
    context, but edit authority remains tied to this exact label set.
    """
    current = set(section_labels)
    for state in states:
        if state.labels == current:
            return state
    state = SectionStuckState(labels=current)
    states.append(state)
    return state


def _section_normalization_prompt(
    ctx: Ctx,
    blueprint_source: str,
    section_labels: list[str],
    context_labels: list[str],
    evidence: str,
    *,
    model_timeout_s: int,
    api_mode: bool,
) -> str:
    draft_content = ctx.content_path.relative_to(REPO_ROOT)
    draft_dir = ctx.blueprint_dir.relative_to(REPO_ROOT)
    blocks = _node_tex_blocks(ctx.nodes)
    section_nodes = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; uses "
        f"{', '.join(sorted(ctx.nodes[label].uses)) or 'none'})\n"
        f"```tex\n{blocks.get(label, '')[:5000]}\n```"
        for label in section_labels
        if label in ctx.nodes
    )
    context_only = [
        label for label in context_labels
        if label not in set(section_labels) and label in ctx.nodes
    ]
    context_nodes = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; read-only context)\n"
        f"```tex\n{blocks.get(label, '')[:3000]}\n```"
        for label in context_only
    )
    context_block = (
        "\nRelated rejected nodes supplied as read-only context; do not edit "
        "them:\n" + context_nodes + "\n"
        if context_nodes
        else ""
    )
    excerpt = _paper_excerpt_for(ctx, section_labels)
    paper_block = (
        f"\nRelevant paper context (deterministic excerpt):\n<paper>\n{excerpt}\n</paper>\n"
        if excerpt
        else ""
    )
    if api_mode:
        source_block = f"""
Current blueprint source:
```tex
{blueprint_source}
```
"""
    else:
        source_block = f"""
The unpublished blueprint draft lives at `{draft_content}`;
read it from disk as needed (locate the section nodes via their `\\label{{...}}`
anchors) and edit it in place. The section nodes are already excerpted above —
do not re-read the whole file into context.
"""
    base = f"""TASK: NORMALIZE-STUCK-BLUEPRINT-SECTION

Phase 1 is repeatedly failing to freeze one dependency-ordered section. Do a
single constrained blueprint normalization pass for that section only.

Goal:
- Make the listed blueprint nodes easier to state one-to-one in Lean.
- Preserve the mathematical content.
- Keep the blueprint as the source of truth; do not write Lean code.

Hard constraints:
- Edit only `{draft_content}`. Do not edit the canonical blueprint.
- Do not weaken, delete, or replace claims with placeholders.
- Preserve existing labels unless a node must be split.
- If splitting is necessary, insert helper nodes immediately before the node
  that uses them and add explicit `\\uses{{...}}` edges.
- Do not touch unrelated downstream sections.
- Do not rewrite the whole blueprint.
- Keep changes small: target the listed section plus direct helper nodes only.
- After editing, run `python scripts/validate_blueprint.py {ctx.name} --blueprint-dir {draft_dir}`.
- This call has a wall-clock budget of about {model_timeout_s}s.

{_HARNESS_CONVENTIONS_NOTE}

The recurring evidence is:
```text
{evidence[-12000:]}
```

Section nodes to normalize:
{section_nodes}

{context_block}

{paper_block}
{source_block}
"""
    if not api_mode:
        return base
    return f"""{base}

API MODE: Return exactly one JSON object:
{{
  "content_tex": "full replacement for the unpublished draft {draft_content}",
  "notes": "short explanation of the small section-normalization changes"
}}

Do not include `\\begin{{document}}` or `\\end{{document}}`.
"""


def _normalize_stuck_section(
    ctx: Ctx,
    evidence: str,
    section_labels: list[str],
    *,
    context_labels: list[str] | None = None,
    trial: int,
    max_trials: int,
    repair_runner_agent: bool,
) -> set[str]:
    """One constrained normalization pass for a repeatedly failing section.

    Rolls back if the model invalidates the blueprint or edits too broadly.
    """
    content_path = ctx.content_path
    before_content = content_path.read_text(encoding="utf-8")
    blueprint_source = _read_draft_blueprint_source(ctx)
    before_fps = dict(ctx.contract_fps)
    _log(
        f"==> Section normalization {trial}/{max_trials} for: "
        + ", ".join(section_labels[:8])
    )
    prompt = _section_normalization_prompt(
        ctx,
        blueprint_source,
        section_labels,
        context_labels or section_labels,
        evidence,
        model_timeout_s=ctx.hard_timeout,
        api_mode=not repair_runner_agent,
    )
    prompt_artifact = _store_text(ctx.telemetry, "prompt_section_normalization", prompt)
    try:
        runner = _make_runner(
            ctx.escalation_runner_spec,
            timeout=ctx.hard_timeout,
            readonly=False,
            effort=ctx.escalation_effort,
            with_skill=True,
        )
    except RunnerError as exc:
        _record(
            ctx.telemetry,
            "section_normalization_result",
            labels=section_labels,
            status="runner_error",
            changed_labels=[],
            changed_count=0,
            reason=str(exc),
        )
        if is_environment_error(exc) or is_transient_error(exc):
            raise
        raise SectionNormalizationRejected(str(exc)) from exc
    started = time.monotonic()
    try:
        result = runner.run(prompt, cwd=REPO_ROOT, retries=0)
    except RunnerError as exc:
        _record(
            ctx.telemetry,
            "model_call",
            purpose="section_normalization",
            labels=section_labels,
            status=_runner_failure_status(exc),
            duration_s=time.monotonic() - started,
            timeout_s=ctx.hard_timeout,
            backend=runner.backend_name,
            model=runner.model,
            prompt=prompt_artifact.to_event(REPO_ROOT),
            error=str(exc),
            environment_error=is_environment_error(exc),
            transport_error=_runner_failure_status(exc) == "transport_exhausted",
        )
        content_path.write_text(before_content, encoding="utf-8")
        restored = _validate_draft(ctx)
        if restored.ok:
            ctx.refresh_nodes(restored.nodes)
        if is_environment_error(exc) or _runner_failure_status(exc) == "transport_exhausted":
            raise
        raise SectionNormalizationRejected(str(exc)) from exc
    _record(
        ctx.telemetry,
        "model_call",
        purpose="section_normalization",
        labels=section_labels,
        status="success",
        duration_s=time.monotonic() - started,
        timeout_s=ctx.hard_timeout,
        backend=runner.backend_name,
        model=runner.model,
        prompt=prompt_artifact.to_event(REPO_ROOT),
        response=_store_text(ctx.telemetry, "response_section_normalization", result.text).to_event(REPO_ROOT),
    )
    try:
        if not repair_runner_agent:
            _write_api_refinement_to(content_path, result.text)
        validation = _validate_draft(ctx)
        if not validation.ok:
            print_result(validation)
            raise ValueError("section normalization produced an invalid blueprint")
        ctx.refresh_nodes(validation.nodes)
        changed = {
            label
            for label, fp in ctx.contract_fps.items()
            if before_fps.get(label) != fp
        }
        changed |= {label for label in before_fps if label not in ctx.contract_fps}
        changed |= {label for label in ctx.contract_fps if label not in before_fps}
        if len(changed) > SECTION_NORMALIZATION_MAX_CHANGED:
            raise SectionNormalizationRejected(
                "section normalization changed too many node contracts "
                f"({len(changed)} > {SECTION_NORMALIZATION_MAX_CHANGED})"
            )
    except SectionNormalizationRejected as exc:
        content_path.write_text(before_content, encoding="utf-8")
        validation = _validate_draft(ctx)
        if validation.ok:
            ctx.refresh_nodes(validation.nodes)
        _record(
            ctx.telemetry,
            "section_normalization_result",
            labels=section_labels,
            status="rejected",
            reason=str(exc),
        )
        raise
    except Exception as exc:
        content_path.write_text(before_content, encoding="utf-8")
        validation = _validate_draft(ctx)
        if validation.ok:
            ctx.refresh_nodes(validation.nodes)
        raise SectionNormalizationRejected(str(exc)) from exc
    _record(
        ctx.telemetry,
        "section_normalization_result",
        labels=section_labels,
        status="applied",
        changed_labels=sorted(changed),
        changed_count=len(changed),
    )
    return changed
