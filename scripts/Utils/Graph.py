"""Blueprint fingerprints, dependency-graph ordering/frontiers, label bookkeeping, repair-scope gates.

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
# Blueprint statement extraction


def _statement_blocks(nodes: dict[str, Node]) -> dict[str, str]:
    """Per-node TeX with the trailing proof environment stripped.

    The statement block is the alignment contract for the frozen Lean
    statement. It is not the full cache contract: proof sketches also matter
    because accepted Lean is supposed to certify the blueprint proof.
    """
    blocks = _node_tex_blocks(nodes)
    return {
        label: re.sub(r"\\begin\{proof\}[\s\S]*\\end\{proof\}\s*$", "", block).strip()
        for label, block in blocks.items()
    }


def _statement_fingerprints(nodes: dict[str, Node]) -> dict[str, str]:
    return {
        label: hashlib.sha256(block.encode("utf-8")).hexdigest()
        for label, block in _statement_blocks(nodes).items()
    }


def _contract_fingerprints(nodes: dict[str, Node]) -> dict[str, str]:
    """Hash the full per-node TeX contract, including proof sketches.

    Fast-mode resume uses this broader fingerprint so a proof-prose repair does
    not silently keep Lean generated for the old proof obligation structure.
    """
    return {
        label: hashlib.sha256(block.encode("utf-8")).hexdigest()
        for label, block in _node_tex_blocks(nodes).items()
    }


def _topo_order(nodes: dict[str, Node]) -> list[str]:
    """Dependency-respecting node order, stable by blueprint source position."""
    position = {label: idx for idx, label in enumerate(_node_order(nodes))}
    indegree = {label: 0 for label in nodes}
    dependents: dict[str, list[str]] = {label: [] for label in nodes}
    for label, node in nodes.items():
        for dep in node.uses:
            if dep in nodes:
                indegree[label] += 1
                dependents[dep].append(label)
    ready = sorted((label for label, deg in indegree.items() if deg == 0), key=position.get)
    order: list[str] = []
    while ready:
        label = ready.pop(0)
        order.append(label)
        changed = False
        for dep in dependents[label]:
            indegree[dep] -= 1
            if indegree[dep] == 0:
                ready.append(dep)
                changed = True
        if changed:
            ready.sort(key=position.get)
    # Validation guarantees acyclicity; any leftover means a validator bug.
    order.extend(label for label in position if label not in set(order))
    return order


def _bottom_up_statement_layers(nodes: dict[str, Node]) -> list[list[str]]:
    """All generated nodes in dependency-first graph frontiers.

    A node is eligible only after every generated dependency in its ``uses``
    set has appeared in an earlier layer. Mathlib-settled dependencies are
    already available and therefore do not participate in the scheduler.
    """
    source_order = _node_order(nodes)
    position = {label: index for index, label in enumerate(source_order)}
    remaining = {
        label for label, node in nodes.items() if not node.mathlibok
    }
    layers: list[list[str]] = []
    while remaining:
        layer = sorted(
            (
                label
                for label in remaining
                if not ({dep for dep in nodes[label].uses if dep in remaining})
            ),
            key=position.get,
        )
        if not layer:
            # Validation guarantees acyclicity. Preserve total behavior if a
            # malformed graph somehow reaches the scheduler.
            layer = [min(remaining, key=position.get)]
        layers.append(layer)
        remaining.difference_update(layer)
    return layers


def _bottom_up_ready_frontier(
    nodes: dict[str, Node], pending: set[str], frozen: set[str]
) -> list[str]:
    """Return pending contracts whose generated dependencies are frozen.

    Unlike the static layer partition, this frontier is recomputed after every
    successful transaction. A difficult node therefore blocks only its own
    dependents; accepted siblings can immediately unlock work in other graph
    branches without weakening dependency-first refinement.
    """
    position = {label: index for index, label in enumerate(_node_order(nodes))}
    generated = {label for label, node in nodes.items() if not node.mathlibok}
    return sorted(
        (
            label
            for label in pending
            if {
                dep for dep in nodes[label].uses if dep in generated
            } <= frozen
        ),
        key=position.get,
    )


def _partition_sections(
    nodes: dict[str, Node], pending: set[str], section_size: int
) -> list[list[str]]:
    """Contiguous topo-order groups so every dependency lives in an earlier
    section, an already-frozen section, or Mathlib."""
    sections: list[list[str]] = []
    current: list[str] = []
    for label in _topo_order(nodes):
        if label not in pending or nodes[label].mathlibok:
            continue
        current.append(label)
        if len(current) >= section_size:
            sections.append(current)
            current = []
    if current:
        sections.append(current)
    return sections


def _immediate_theorem_dependencies(
    nodes: dict[str, Node], label: str, theorem_labels: set[str]
) -> set[str]:
    """The nearest theorem-like dependencies below ``label``.

    Definition nodes are transparent for proof scheduling: if a theorem uses a
    definition that in turn uses a lemma, that lemma is still the next proof
    frontier. This changes only proof order; the original ``uses`` graph remains
    the source of truth for imports, audits, and invalidation.
    """
    found: set[str] = set()
    seen: set[str] = set()
    stack = list(nodes[label].uses) if label in nodes else []
    while stack:
        dep = stack.pop()
        if dep in seen or dep not in nodes:
            continue
        seen.add(dep)
        if dep in theorem_labels:
            found.add(dep)
            continue
        stack.extend(nodes[dep].uses)
    return found


def _top_down_proof_layers(nodes: dict[str, Node]) -> list[list[str]]:
    """Return theorem-like nodes from public roots down to proof leaves.

    Roots are theorem-like nodes that no other theorem-like node depends on.
    Breadth-first layers then follow the nearest theorem dependencies. Stable
    source order keeps telemetry and resumes deterministic.
    """
    source_order = _node_order(nodes)
    position = {label: index for index, label in enumerate(source_order)}
    theorem_labels = {
        label
        for label, node in nodes.items()
        if not node.mathlibok and _is_theorem_like_kind(node.kind)
    }
    immediate = {
        label: _immediate_theorem_dependencies(nodes, label, theorem_labels)
        for label in theorem_labels
    }
    consumed = {dep for deps in immediate.values() for dep in deps}
    roots = sorted(theorem_labels - consumed, key=position.get)
    if not roots:
        roots = sorted(theorem_labels, key=position.get)

    depth: dict[str, int] = {}
    frontier = list(roots)
    current_depth = 0
    while frontier:
        next_frontier: set[str] = set()
        for label in frontier:
            previous = depth.get(label)
            # Keep the longest root-to-node depth. A theorem may be referenced
            # both directly by a root and through another theorem; assigning
            # the shortest depth would put consumer and dependency in the same
            # parallel frontier.
            if previous is not None and previous >= current_depth:
                continue
            depth[label] = current_depth
            next_frontier.update(immediate.get(label, set()))
        frontier = sorted(next_frontier, key=position.get)
        current_depth += 1

    # Defensive coverage for disconnected or malformed subgraphs. Validation
    # normally makes this unnecessary, but no theorem should disappear from a
    # scheduler because of an unexpected graph shape.
    for label in theorem_labels:
        depth.setdefault(label, current_depth)
    return [
        sorted((label for label, item_depth in depth.items() if item_depth == layer), key=position.get)
        for layer in range(max(depth.values(), default=-1) + 1)
    ]


def _next_top_down_frontier(
    nodes: dict[str, Node], unproved: set[str]
) -> tuple[int, list[str], list[str]]:
    """Return ``(layer, unresolved labels, all roots)`` for the next proof wave."""
    layers = _top_down_proof_layers(nodes)
    roots = layers[0] if layers else []
    for layer, labels in enumerate(layers):
        pending = [label for label in labels if label in unproved]
        if pending:
            return layer, pending, roots
    return -1, [], roots


def _bottom_up_proof_layers(nodes: dict[str, Node]) -> list[list[str]]:
    """Theorem-like nodes from proof leaves upward to public roots."""
    return list(reversed(_top_down_proof_layers(nodes)))


def _next_bottom_up_frontier(
    nodes: dict[str, Node], unproved: set[str]
) -> tuple[int, list[str], list[str]]:
    """Return the next dependency-first theorem frontier."""
    layers = _bottom_up_proof_layers(nodes)
    roots = layers[-1] if layers else []
    for layer, labels in enumerate(layers):
        pending = [label for label in labels if label in unproved]
        if pending:
            return layer, pending, roots
    return -1, [], roots


def _next_implementation_frontier(
    nodes: dict[str, Node], unresolved: set[str], refinement_order: str
) -> tuple[int, list[str], list[str]]:
    """Return the branch-local ready frontier for deferred implementations.

    Static graph layers are useful for ordering and diagnostics, but they are
    not synchronization barriers. In top-down mode a node is ready after every
    unresolved generated consumer has completed; in bottom-up mode it is ready
    after every unresolved generated dependency has completed. Consequently a
    difficult node blocks only its own graph branch while independent work can
    occupy the remaining workers.
    """
    layers = (
        _top_down_statement_layers(nodes)
        if refinement_order == "top-down"
        else _bottom_up_statement_layers(nodes)
    )
    roots = layers[0] if layers else []
    generated = {
        label for label, node in nodes.items() if not node.mathlibok
    }
    pending = unresolved & generated
    if not pending:
        return -1, [], roots

    position = {label: index for index, label in enumerate(_node_order(nodes))}
    layer_by_label = {
        label: layer
        for layer, labels in enumerate(layers)
        for label in labels
    }
    if refinement_order == "top-down":
        unresolved_consumers: dict[str, set[str]] = {
            label: set() for label in pending
        }
        for consumer in pending:
            for dependency in nodes[consumer].uses:
                if dependency in pending:
                    unresolved_consumers[dependency].add(consumer)
        ready = [
            label
            for label in pending
            if not unresolved_consumers[label]
        ]
    else:
        ready = [
            label
            for label in pending
            if not ({dependency for dependency in nodes[label].uses} & pending)
        ]

    if ready:
        ready.sort(
            key=lambda label: (
                layer_by_label.get(label, len(layers)),
                position.get(label, len(position)),
            )
        )
        return min(layer_by_label.get(label, 0) for label in ready), ready, roots

    # Validation normally rejects dependency cycles. Preserve total scheduler
    # behavior if malformed state nevertheless reaches this point, and let the
    # existing compile/audit/repair path produce actionable evidence.
    for layer, labels in enumerate(layers):
        fallback = [label for label in labels if label in pending]
        if fallback:
            return layer, fallback, roots
    return -1, [], roots


def _top_down_statement_layers(nodes: dict[str, Node]) -> list[list[str]]:
    """All generated nodes from public theorem roots down to graph leaves.

    The initial declaration pass has already made every name available, so
    Phase 1 is free to refine contracts in the direction required by the
    method: public claims first, then the definitions and lemmas they constrain.
    Unconsumed public definitions start alongside theorem roots; any malformed
    leftover component is appended deterministically as a defensive fallback.
    """
    order = _node_order(nodes)
    position = {label: index for index, label in enumerate(order)}
    generated = {
        label for label, node in nodes.items() if not node.mathlibok
    }
    consumed = {
        dep
        for label in generated
        for dep in nodes[label].uses
        if dep in generated
    }
    theorem_roots = [
        label
        for label in order
        if label in generated
        and _is_theorem_like_kind(nodes[label].kind)
        and label not in consumed
    ]
    # Public generated definitions can be independent outputs rather than
    # dependencies of a theorem. They are roots of their own graph component
    # and should be refined in the same wave, not serialized one per synthetic
    # layer after all theorem work.
    other_roots = [
        label
        for label in order
        if label in generated
        and label not in consumed
        and label not in set(theorem_roots)
    ]
    roots = theorem_roots + other_roots

    depth: dict[str, int] = {}
    frontier = list(roots)
    current_depth = 0
    while frontier:
        next_frontier: set[str] = set()
        for label in frontier:
            previous = depth.get(label)
            if previous is not None and previous >= current_depth:
                continue
            depth[label] = current_depth
            next_frontier.update(
                dep for dep in nodes[label].uses if dep in generated
            )
        frontier = sorted(next_frontier, key=position.get)
        current_depth += 1

    # A blueprint may contain notation or supporting components that are not
    # reachable from a public theorem. They still need Phase-1 alignment. Put
    # them after the root-driven component while preserving a deterministic
    # consumer-before-dependency order.
    remaining = generated - set(depth)
    if remaining:
        topo = [label for label in _topo_order(nodes) if label in remaining]
        for label in reversed(topo):
            depth[label] = current_depth
            current_depth += 1

    return [
        sorted(
            (label for label, item_depth in depth.items() if item_depth == layer),
            key=position.get,
        )
        for layer in range(max(depth.values(), default=-1) + 1)
    ]


def _frozen_labels(sections: list[Section]) -> set[str]:
    return {
        label
        for sec in sections
        if not sec.deferred
        for label in (
            sec.labels if sec.refined_labels is None else sec.refined_labels
        )
    }


def _reserved_labels(sections: list[Section]) -> set[str]:
    """Contracts owned by active or deterministically deferred sections."""
    return {label for sec in sections for label in sec.labels}


def _proved_labels(sections: list[Section]) -> set[str]:
    proved: set[str] = set()
    for sec in sections:
        if sec.deferred:
            continue
        try:
            parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        except OSError:
            continue
        by_name = {decl.name: decl for decl in parsed.decls if decl.name}
        refined = set(sec.labels) if sec.refined_labels is None else sec.refined_labels
        for label in refined:
            decl = by_name.get(_lean_name(label))
            if decl is not None and not _has_terminal_sorry(decl.text):
                proved.add(label)
    return proved


def _sections_for_deps(ctx: Ctx, labels: list[str], sections: list[Section]) -> list[str]:
    """Skeleton modules a new section must import: owners of transitive deps."""
    owner = {
        label: sec.module
        for sec in sections
        if not sec.deferred
        for label in sec.labels
    }
    needed: set[str] = set()
    stack = list(labels)
    seen: set[str] = set()
    while stack:
        label = stack.pop()
        if label in seen:
            continue
        seen.add(label)
        for dep in ctx.nodes.get(label, Node(label, "", Path("."), 0)).uses:
            if dep in owner:
                needed.add(owner[dep])
            if dep in ctx.nodes:
                stack.append(dep)
    return sorted(needed)


def _dependency_contract_table(
    ctx: Ctx, labels: list[str], sections: list[Section]
) -> str:
    """Deterministically tell the model how every direct dependency is owned.

    In particular, ``\\mathlibok`` nodes use their settled ``\\lean{...}`` name;
    their generated label name must never be requested as a missing helper.
    """
    target_set = set(labels)
    owner = {
        label: sec.module
        for sec in sections
        if not sec.deferred
        for label in sec.labels
    }
    lines: list[str] = []
    for label in labels:
        statement_dependencies = _statement_uses(ctx.nodes[label])
        for dep in sorted(ctx.nodes[label].uses):
            node = ctx.nodes.get(dep)
            if node is None:
                continue
            if node.mathlibok:
                actual = node.lean_decl or "(missing \\lean mapping)"
                ownership = (
                    f"Mathlib-owned; use `{actual}` exactly; "
                    f"do NOT generate or request `{_lean_name(dep)}`"
                )
            elif dep in target_set:
                ownership = f"generated earlier in this same file as `{_lean_name(dep)}`"
            elif dep in owner:
                ownership = f"frozen in `{owner[dep]}` as `{_lean_name(dep)}`"
            else:
                ownership = f"generated dependency not frozen yet as `{_lean_name(dep)}`"
            scope = "statement interface" if dep in statement_dependencies else "proof only"
            lines.append(f"- {label} -> {dep} ({scope}): {ownership}")
    return "\n".join(dict.fromkeys(lines)) or "- no direct dependencies"


def _transitive_dependencies(nodes: dict[str, Node], label: str) -> set[str]:
    found: set[str] = set()
    stack = list(nodes.get(label, Node(label, "", Path("."), 0)).uses)
    while stack:
        dep = stack.pop()
        if dep in found:
            continue
        found.add(dep)
        if dep in nodes:
            stack.extend(nodes[dep].uses)
    return found


def _statement_uses(node: Node) -> set[str]:
    """Dependencies that belong in the node's public declaration.

    Older tests and persisted in-memory callers construct ``Node`` with only
    ``uses``.  Fall back to that union only when no scoped information exists.
    """
    statement = set(getattr(node, "statement_uses", set()))
    proof = set(getattr(node, "proof_uses", set()))
    if statement or proof:
        return statement
    return set(node.uses)


def _proof_uses(node: Node) -> set[str]:
    return set(getattr(node, "proof_uses", set()))


def _transitive_statement_dependencies(
    nodes: dict[str, Node], label: str
) -> set[str]:
    """Public-interface dependency closure, excluding proof-only edges."""
    found: set[str] = set()
    node = nodes.get(label)
    stack = list(_statement_uses(node)) if node is not None else []
    while stack:
        dep = stack.pop()
        if dep in found:
            continue
        found.add(dep)
        if dep in nodes:
            stack.extend(_statement_uses(nodes[dep]))
    return found


def _repair_graph_distances(
    before: dict[str, Node],
    after: dict[str, Node],
    targets: list[str],
    changed: set[str],
) -> dict[str, int | None]:
    """Distance of each changed contract from a requested repair target.

    The union of the old and new undirected dependency graphs handles helper
    insertion, edge reversal during normalization, and deleted labels. This is
    deterministic repair-scope evidence for telemetry; it does not overrule a
    valid repair or add a critic call.
    """
    adjacency: dict[str, set[str]] = {}
    for nodes in (before, after):
        for label, node in nodes.items():
            adjacency.setdefault(label, set())
            for dep in node.uses:
                if dep not in nodes:
                    continue
                adjacency.setdefault(dep, set())
                adjacency[label].add(dep)
                adjacency[dep].add(label)
    distance: dict[str, int] = {}
    queue = [label for label in targets if label in adjacency]
    for label in queue:
        distance[label] = 0
    index = 0
    while index < len(queue):
        label = queue[index]
        index += 1
        for neighbor in adjacency.get(label, set()):
            if neighbor in distance:
                continue
            distance[neighbor] = distance[label] + 1
            queue.append(neighbor)
    return {label: distance.get(label) for label in sorted(changed)}


def _upstream_contract_closure(nodes: dict[str, Node], labels: Iterable[str]) -> set[str]:
    """Labels whose contracts may legitimately change to repair ``labels``.

    A Phase 1 statement repair is allowed to change the failing labels and the
    dependency/helper side of those labels. It should not rewrite downstream
    consumers just because those consumers will later need to recompile against
    the repaired contract.
    """
    allowed: set[str] = set()
    stack = [label for label in labels if label in nodes]
    while stack:
        label = stack.pop()
        if label in allowed:
            continue
        allowed.add(label)
        stack.extend(dep for dep in nodes[label].uses if dep in nodes)
    return allowed


def _phase1_repair_scope_violations(
    before: dict[str, Node],
    after: dict[str, Node],
    targets: list[str],
    changed: set[str],
) -> set[str]:
    """Changed contracts outside a target's dependency/decomposition scope.

    Existing downstream consumers remain immutable during a Phase 1 repair.
    This general scope check permits connected additions so ordinary repairs
    can be validated transactionally. Confirmed decomposition receives the
    stricter ``_decomposition_orientation_findings`` check as well: every new
    helper must be an actual dependency of the rejected target.
    """
    allowed = _upstream_contract_closure(before, targets) | _upstream_contract_closure(
        after, targets
    )
    added = set(after) - set(before)
    connected = set(targets)
    pending = set(added)
    while pending:
        newly_connected = {
            label
            for label in pending
            if set(after[label].uses) & connected
        }
        if not newly_connected:
            break
        allowed.update(newly_connected)
        connected.update(newly_connected)
        pending -= newly_connected
    return {label for label in changed if label not in allowed}


def _phase2_existing_repair_scope_violations(
    before: dict[str, Node],
    targets: Iterable[str],
    changed: Iterable[str],
) -> set[str]:
    """Pre-existing contracts edited without direct Phase-2 evidence.

    A complete-node failure authorizes edits to its named target component,
    not to every dependency supplied as read-only context. Brand-new helper
    nodes are intentionally excluded here; the existing connectivity,
    decomposition-orientation, and post-repair boundary gates validate them.
    """
    allowed = set(targets)
    return {
        label
        for label in changed
        if label in before and label not in allowed
    }


def _decomposition_orientation_findings(
    before: dict[str, Node],
    after: dict[str, Node],
    roots: Iterable[str],
) -> list[str]:
    """Reject new decomposition helpers placed on the consumer side.

    A helper introduced to state or prove a rejected contract must be in that
    contract's dependency closure. Otherwise the original node cannot use it;
    adding the reverse edge later either leaves dead scaffolding or creates the
    cycle observed in the Simplex run.
    """
    root_set = {label for label in roots if label in after}
    added = set(after) - set(before)
    if not root_set or not added:
        return []
    root_closures = {
        root: _transitive_dependencies(after, root) for root in root_set
    }
    findings: list[str] = []
    for helper in sorted(added):
        owners = sorted(
            root for root, closure in root_closures.items() if helper in closure
        )
        if owners:
            continue
        reverse = sorted(
            root
            for root in root_set
            if root in _transitive_dependencies(after, helper)
        )
        if reverse:
            findings.append(
                f"new helper `{helper}` depends on repaired target(s) "
                f"{', '.join(reverse)} instead of being their dependency"
            )
        else:
            findings.append(
                f"new helper `{helper}` is not in the dependency closure of "
                f"any repaired target ({', '.join(sorted(root_set))})"
            )
    return findings


def _decomposition_orientation_dependency_edges(
    before: dict[str, Node],
    after: dict[str, Node],
    roots: Iterable[str],
) -> dict[str, set[str]]:
    """Return safe deterministic root->helper edges for orientation defects.

    This is deliberately narrower than ``_decomposition_orientation_findings``.
    If a decomposition repair introduces helper nodes for a single repaired
    root but forgets to add the public ``\\uses`` edge from that root, the graph
    direction can be fixed mechanically and then validated.  Multi-root repairs
    and reverse edges remain model/validator failures, because guessing the
    owner or closing a cycle would change the proof graph.
    """
    root_set = {label for label in roots if label in after}
    added = set(after) - set(before)
    if len(root_set) != 1 or not added:
        return {}
    root = next(iter(root_set))
    root_closure = _transitive_dependencies(after, root)
    dependencies: set[str] = set()
    for helper in sorted(added):
        if helper in root_closure:
            continue
        if root in _transitive_dependencies(after, helper):
            continue
        dependencies.add(helper)
    return {root: dependencies} if dependencies else {}


def _invalid_mathlib_refusal_mappings(ctx: Ctx, refusal: dict) -> dict[str, str]:
    """Return generated-name -> settled-name mappings misread by a refusal."""
    label = str(refusal.get("label") or "")
    if label not in ctx.nodes:
        return {}
    refusal_text = "\n".join(
        [str(refusal.get("reason") or "")]
        + [str(item) for item in refusal.get("missing_helpers") or []]
    )
    mappings: dict[str, str] = {}
    for dep in _transitive_dependencies(ctx.nodes, label):
        node = ctx.nodes.get(dep)
        if node is None or not node.mathlibok or not node.lean_decl:
            continue
        generated = _lean_name(dep)
        if dep in refusal_text or re.search(rf"\b{re.escape(generated)}\b", refusal_text):
            mappings[generated] = node.lean_decl
    return mappings


def _parts_around_labels(labels: list[str], isolated: list[str]) -> list[list[str]]:
    """Preserve dependency order while splitting named nodes into singletons."""
    isolated_set = set(isolated)
    parts: list[list[str]] = []
    current: list[str] = []
    for label in labels:
        if label in isolated_set:
            if current:
                parts.append(current)
                current = []
            parts.append([label])
        else:
            current.append(label)
    if current:
        parts.append(current)
    return parts


def _lean_failure_fingerprint(code: str, output: str) -> tuple[str, str]:
    """Stable identity for a generated file failing with the same Lean output."""
    normalized = re.sub(r"\x1b\[[0-9;]*m", "", output)
    return (
        hashlib.sha256(code.encode("utf-8")).hexdigest(),
        hashlib.sha256(normalized.strip().encode("utf-8")).hexdigest(),
    )


def _lean_error_shape(output: str) -> str:
    """Hash the stable compiler failure shape, ignoring generated locations.

    Exact code/error hashes remain useful for proving byte-for-byte stagnation,
    but model rewrites often move the same error to another line or rename a
    metavariable. This normalized shape catches that repeated work without
    treating different Lean diagnostics as equivalent.
    """
    normalized = re.sub(r"\x1b\[[0-9;]*m", "", output)
    normalized = re.sub(r"(?m)^.*?\.lean:\d+:\d+:\s*", "", normalized)
    normalized = re.sub(r"\?m[._]?[0-9]+", "?m", normalized)
    normalized = re.sub(r"(?:^|\s)\d+:\d+(?=\s|$)", " <loc>", normalized)
    normalized = re.sub(r"[ \t]+", " ", normalized)
    normalized = re.sub(r"\n{3,}", "\n\n", normalized).strip()
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()
