"""Prompt-context builders (digests, dependency interfaces) and shared prompt builders.

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


def _decl_interface_text(decl) -> str:
    """Return the useful frozen interface for one declaration.

    Theorem proofs and deferred def/abbrev bodies are omitted. Completed
    definition bodies remain visible because they carry definitional meaning.
    """
    text = decl.text.strip()
    if decl.kind in {"theorem", "lemma"} or (
        decl.kind in {"def", "abbrev"} and _has_terminal_sorry(text)
    ):
        deferred = _terminal_sorry_interface_text(text)
        if deferred is not None:
            return deferred
        stripped = _TERMINAL_PROOF_RE.sub("", text).rstrip()
        if stripped != text:
            return stripped
        head = text.split(":=", 1)[0].rstrip()
        return head
    if len(text) > _INTERFACE_DECL_CAP:
        return text[:_INTERFACE_DECL_CAP].rstrip() + "\n-- ... body truncated; the name and signature above are frozen"
    return text


def _frozen_interface_digest(
    sections: list[Section],
    modules: list[str],
    *,
    budget: int = 24000,
    priority_modules: set[str] | None = None,
) -> str:
    """Complete, module-grouped interface digest of the frozen declarations in
    ``modules``. Budgeting is module-granular: when over budget, the OLDEST
    modules are dropped whole and named explicitly — never a silent mid-
    declaration cut (a truncated structure is worse than an omitted one,
    because the model then re-reads files to fill the gap). Modules in
    ``priority_modules`` (owners of the targets' direct dependencies) are
    dropped only after every other module is gone."""
    blocks: list[tuple[str, str]] = []
    for sec in sections:
        if sec.deferred or sec.module not in modules:
            continue
        try:
            code = sec.path.read_text(encoding="utf-8")
        except OSError:
            continue
        parts = [_decl_interface_text(decl) for decl in _lean_declarations(code).values()]
        body = "\n\n".join(part for part in parts if part)
        if body:
            blocks.append((sec.module, f"-- ==== {sec.module} (frozen) ====\n{body}"))
    total = sum(len(text) + 2 for _, text in blocks)
    priority = priority_modules or set()
    omitted: list[str] = []
    while len(blocks) > 1 and total > budget:
        drop_index = next(
            (i for i, (module, _text) in enumerate(blocks) if module not in priority),
            0,
        )
        module, text = blocks.pop(drop_index)
        omitted.append(module)
        total -= len(text) + 2
    digest = "\n\n".join(text for _, text in blocks)
    if omitted:
        digest = (
            "-- NOTE: for space, interfaces of these older imported modules are omitted:\n"
            f"-- {', '.join(omitted)}\n"
            "-- Their declarations are still imported and frozen; any of their names used\n"
            "-- by the modules below can be referenced as-is.\n\n" + digest
        )
    return digest


def _minimal_dependency_interface(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    modules: list[str],
    *,
    local_code: str = "",
    budget: int | None = PHASE1_DEPENDENCY_CONTEXT_BUDGET,
) -> str:
    """Return the smallest complete generated interface needed by ``labels``.

    Start from direct non-Mathlib ``uses`` dependencies outside the target
    group. Include their exact frozen declarations, then include only generated
    declarations referenced by those interfaces. The final name-set comparison
    is the deterministic completeness gate: a model call is never launched
    with an advertised generated dependency silently absent from its context.

    ``budget`` is a soft batching target, not a correctness limit. The Phase-1
    scheduler partitions ordinary multi-node groups before prompt construction.
    An atomic component or singleton whose genuinely minimal interface is still
    larger must receive that complete interface; omitting it or terminating the
    autonomous run would both be incorrect.
    """
    target_set = set(labels)
    required = {
        dep
        for label in labels
        for dep in ctx.nodes.get(label, Node(label, "", Path("."), 0)).uses
        if dep in ctx.nodes and not ctx.nodes[dep].mathlibok and dep not in target_set
    }
    if not required:
        return ""

    local_names = set(_lean_declarations(local_code)) if local_code.strip() else set()
    sources: list[str] = []
    seen_paths: set[Path] = set()
    for sec in sections:
        if sec.module not in modules or sec.path in seen_paths or not sec.path.is_file():
            continue
        seen_paths.add(sec.path)
        sources.append(sec.path.read_text(encoding="utf-8"))
    # A section list can represent only the current scheduling frontier. Module
    # names still map deterministically to generated source paths, so recover
    # their interfaces without asking the model to inspect the repository.
    for module in modules:
        path = REPO_ROOT / (module.replace(".", "/") + ".lean")
        if path in seen_paths or not path.is_file():
            continue
        seen_paths.add(path)
        sources.append(path.read_text(encoding="utf-8"))

    declarations = {}
    for source in sources:
        declarations.update(_lean_declarations(source))
    label_by_name = {
        _lean_name(label): label
        for label, node in ctx.nodes.items()
        if not node.mathlibok
    }

    queue = list(sorted(required))
    included: dict[str, str] = {}
    missing: set[str] = set()
    while queue:
        label = queue.pop(0)
        if label in included or _lean_name(label) in local_names:
            continue
        lean_name = _lean_name(label)
        decl = declarations.get(lean_name)
        if decl is None:
            missing.add(label)
            continue
        text = _decl_interface_text(decl)
        included[label] = text
        for referenced_name, referenced_label in label_by_name.items():
            if (
                referenced_label not in target_set
                and referenced_label not in included
                and re.search(rf"(?<![A-Za-z0-9_']){re.escape(referenced_name)}(?![A-Za-z0-9_'])", text)
            ):
                queue.append(referenced_label)

    unresolved = sorted(
        label for label in required if label not in included and _lean_name(label) not in local_names
    )
    unresolved.extend(sorted(missing - set(unresolved)))
    if unresolved:
        raise ValueError(
            "generated dependency context is incomplete for "
            + ", ".join(labels)
            + ": missing "
            + ", ".join(dict.fromkeys(unresolved))
        )

    blocks: list[str] = []
    for label in sorted(included):
        block = f"-- {label}\n{included[label]}"
        blocks.append(block)
    return "\n\n".join(blocks)


def _phase1_dependency_interface_chars(
    ctx: Ctx, labels: list[str], sections: list[Section]
) -> int:
    """Measure the complete frozen dependency interface for one candidate group."""
    modules = _sections_for_deps(ctx, labels, sections)
    return len(
        _minimal_dependency_interface(
            ctx,
            labels,
            sections,
            modules,
            budget=None,
        )
    )


def _frozen_decl_for_label(sections: list[Section], label: str) -> str:
    lean_name = _lean_name(label)
    for sec in sections:
        if sec.deferred or label not in sec.labels or not sec.path.is_file():
            continue
        parsed = _parse_module(sec.path.read_text(encoding="utf-8"))
        for decl in parsed.decls:
            if decl.name == lean_name:
                return _decl_interface_text(decl)
    return ""


def _downstream_proof_context(
    ctx: Ctx, target_labels: list[str], sections: list[Section], *, budget: int = 10000
) -> str:
    """Explain how higher-level blueprint proofs consume the current frontier.

    Top-down proof search establishes public results first. When it later proves
    their dependencies, this compact read-only context carries the intended use
    of each dependency downward without introducing a Lean import cycle.
    """
    theorem_labels = {
        label
        for label, node in ctx.nodes.items()
        if not node.mathlibok and _is_theorem_like_kind(node.kind)
    }
    proved = _proved_labels(sections)
    consumers: set[str] = set()
    target_set = set(target_labels)
    for consumer in theorem_labels - target_set:
        if _immediate_theorem_dependencies(ctx.nodes, consumer, theorem_labels) & target_set:
            consumers.add(consumer)
    ordered = sorted(
        consumers,
        key=lambda label: (label not in proved, _node_order(ctx.nodes).index(label)),
    )[:8]
    blocks: list[str] = []
    for label in ordered:
        status = "proof already accepted" if label in proved else "higher-level frozen obligation"
        lean_decl = _frozen_decl_for_label(sections, label)
        blocks.append(
            f"### {label} ({status})\n"
            f"Blueprint contract:\n```tex\n{ctx.tex_blocks.get(label, '')[:2600]}\n```\n"
            f"Frozen Lean interface:\n```lean\n{lean_decl[:2200] or '-- unavailable'}\n```"
        )
    text = "\n\n".join(blocks)
    return text[:budget]


# ---------------------------------------------------------------------------
# Prompts


def _format_library_candidates(candidates: list) -> str:
    """Render a candidate subset in the same shape as the global search summary."""
    lines = [
        "- Candidate modules below were found by deterministic local search; "
        "treat module paths as already verified."
    ]
    for cand in candidates:
        rel = cand.file
        try:
            rel = cand.file.relative_to(REPO_ROOT)
        except ValueError:
            pass
        lines.append(
            f"- {cand.library}: `{cand.declaration}` in `{cand.module}` "
            f"({rel}:{cand.line}, matched `{cand.matched}`)"
        )
        if cand.snippet:
            lines.append("  ```lean")
            lines.extend(f"  {line}" for line in cand.snippet.splitlines())
            lines.append("  ```")
    return "\n".join(lines)


def _library_context_for(ctx: Ctx, labels: list[str], *, max_candidates: int = 12) -> str:
    """Slice the run-global library candidates down to the ones whose matched
    search term comes from the target nodes or their direct dependencies. The
    global list is derived from the whole blueprint; repeating all of it in
    every prompt is the single largest fixed prompt cost."""
    if not ctx.library_candidates:
        return ctx.library_context
    subset = set(labels)
    for label in labels:
        node = ctx.nodes.get(label)
        if node is not None:
            subset.update(dep for dep in node.uses if dep in ctx.nodes)
    subset_nodes = {label: ctx.nodes[label] for label in subset if label in ctx.nodes}
    subset_blocks = {label: ctx.tex_blocks.get(label, "") for label in subset_nodes}
    terms = {
        term.lower() for term in _search_terms_from_blueprint(subset_nodes, subset_blocks)
    }
    chosen = [
        cand for cand in ctx.library_candidates if cand.matched.lower() in terms
    ][:max_candidates]
    if not chosen:
        chosen = ctx.library_candidates[:8]
    return _format_library_candidates(chosen)


def _local_node_summary(ctx: Ctx, labels: list[str]) -> str:
    """Node-graph orientation limited to targets, direct deps, and direct
    consumers; the whole-graph summary scaled with blueprint size, not with
    the work in this call."""
    target_set = set(labels)
    nearby = set(labels)
    for label in labels:
        node = ctx.nodes.get(label)
        if node is not None:
            nearby.update(dep for dep in node.uses if dep in ctx.nodes)
    nearby.update(
        consumer
        for consumer, node in ctx.nodes.items()
        if node.uses & target_set
    )
    return _node_summary({label: ctx.nodes[label] for label in nearby if label in ctx.nodes})


def _conjecture_policy_prompt(ctx: Ctx, labels: Iterable[str]) -> str:
    conjectures = [
        label
        for label in labels
        if _is_conjecture_node(label, ctx.nodes.get(label))
    ]
    if not conjectures:
        return ""
    listed = ", ".join(conjectures)
    if getattr(ctx, "conjecture_policy", "record") == "record":
        return f"""
Conjecture policy (`record`) for: {listed}
- Preserve each conjecture's exact claim as a proposition-valued definition:
  `def <required_name> ... : Prop := <the exact proposition>`.
- Do not emit a theorem, proof, `sorry`, axiom, or placeholder for it. Recording
  the proposition is not claiming that the conjecture has been proved.
- When the blueprint says "it remains open whether P", the recorded proposition
  is P itself. The fact that P is open is pipeline metadata; do not encode that
  status as a tautological `P or not P`, a contradictory wrapper, an
  `OpenQuestion` wrapper, or a second blueprint statement.
- Only statement-scoped dependencies may appear in this public proposition;
  proof-only dependencies remain unavailable because no proof is attempted.
"""
    return f"""
Conjecture policy (`attempt`) for: {listed}
- Treat these as ordinary theorem-like nodes. Phase 1 freezes the exact theorem
  statement with `:= sorry`; Phase 2 may prove it only after the blueprint
  itself contains a proof for Lean to formalize.
"""


def _text_only_budget_rule(timeout_s: int) -> str:
    """Shared budget bullet for read-only generation calls.

    Every generation backend is text-only by construction (README: read-only
    model calls): the harness alone inspects the repository, searches
    libraries, and compiles. The former wording licensed spending half the
    budget "verifying library APIs or exploring" — an activity no backend can
    perform. Because readonly Claude Code removes the tools from the schema
    rather than denying calls, models answered that allowance with
    tool-invocation markup, bare shell commands, or investigation narration as
    plain text (62 of 404 stored Phase-1 statement responses), sometimes
    hallucinating the "results". This bullet states the real contract instead;
    the original timeout protections (leave time to emit, an imperfect reply
    beats none, never end without code) are retained.
    """
    return f"""- This call has a wall-clock budget of about {timeout_s}s and is text-only: no shell,
  file, search, or web tool is available, and tool-invocation text in a reply
  is rejected as commentary. Never try to inspect the repository, run
  commands, or search a library; the module paths, dependency interfaces, and
  API snippets supplied in this prompt are already verified, so reason
  directly from them. Always leave time to emit your complete Lean reply: an
  imperfect reply beats no reply, because the Lean compiler and the audits
  exist precisely to catch and correct mistakes, while a reply without the
  requested code wastes the entire call. Never end the budget without having
  produced the requested code."""


def _common_rules(ctx: Ctx, labels: list[str] | None = None) -> str:
    unavailable = ""
    if ctx.unavailable_imports:
        unavailable = (
            "\nUnavailable imports (no compiled .olean locally; NEVER import these):\n"
            + "\n".join(f"- {item}" for item in sorted(ctx.unavailable_imports))
        )
    library_block = (
        _library_context_for(ctx, labels) if labels else ctx.library_context
    )
    conjecture_rules = _conjecture_policy_prompt(ctx, labels or [])
    return f"""Hard constraints:
- The blueprint TeX below is the only mathematical source of truth. Formalize
  each node's statement EXACTLY as written: same objects, same hypotheses, same
  claims. Do not weaken, strengthen, or substitute an adjacent formulation.
- Give each blueprint node exactly the Lean name listed for it.
- Dependencies marked Mathlib-owned are the exception to generated label
  names: use their settled external declaration exactly as shown in the
  dependency contract table. Never generate or request the label-derived name
  for a Mathlib-owned node.
- No `sorry` outside the places these instructions explicitly allow, and never
  `admit`, `by ?`, `axiom`, `constant`, or `opaque`.
- No invented helpers that merely assert a paper result (`foo_from_paper`,
  author-year names, etc.). Every name must come from an imported library, this
  file, or an earlier accepted skeleton module.
- No top-level `variable`/`namespace`/`section`/`example` commands. Each
  declaration must be self-contained. Preamble may only contain `open` lines.
- Import only the specific modules you need; never blanket `import Mathlib` or
  `import AutoBlueprint`.
- If a node CANNOT be faithfully formalized as stated (it needs helper nodes
  the blueprint does not have), do NOT emit weakened Lean for it — but DO
  still return the Lean code block with every other target node you can
  formalize (omit only declarations that would need the refused node). After
  the code block, add one line:
  NEEDS-DECOMPOSITION: {{"label": "<node label>", "missing_helpers": ["<each needed helper statement>"], "reason": "<why>"}}
  If no target node can be formalized, reply with only that line.
{unavailable}

Local Lean library candidates (module paths verified by deterministic search):
{library_block or "- none found"}

Lean API idioms:
{LEAN_IDIOM_CHEATSHEET}
{conjecture_rules}"""


def _design_plan_rules(ctx: Ctx, labels: list[str]) -> str:
    """Rules for JSON interface planning, without generation-only output modes."""
    unavailable = ""
    if ctx.unavailable_imports:
        unavailable = (
            "\nUnavailable imports (do not reference declarations from these):\n"
            + "\n".join(f"- {item}" for item in sorted(ctx.unavailable_imports))
        )
    library_block = _library_context_for(ctx, labels)
    conjecture_rules = _conjecture_policy_prompt(ctx, labels)
    return f"""Plan constraints:
- Return JSON only and include exactly one contract for every requested label.
- The blueprint TeX is the only mathematical source of truth. Preserve the
  same objects, parameters, hypotheses, and claim without weakening or
  strengthening it.
- Use each node's required generated Lean name. Mathlib-owned dependencies use
  their settled external declarations from the dependency table.
- `target_signature` describes one top-level public declaration but contains
  no body, proof, `sorry`, `axiom`, `constant`, or `opaque` declaration.
- Helpers may only be structure, inductive, or class type interfaces owned by
  that contract. Do not invent helper definitions or theorem declarations.
- Do not return Lean code blocks, prose outside the JSON object, or any
  alternate output format. Missing interface structure must be represented in
  the contract's helper surface and decisions; later deterministic and semantic
  gates decide whether blueprint decomposition is required.
{unavailable}

Local Lean library candidates (module paths verified by deterministic search):
{library_block or "- none found"}

Lean API idioms:
{LEAN_IDIOM_CHEATSHEET}
{conjecture_rules}"""


def _initial_declaration_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    timeout_s: int,
    feedback: str = "",
    previous_code: str = "",
) -> str:
    """Ask only for the provisional environment needed to start Phase 1.

    This is deliberately not a statement-acceptance prompt. Signatures must be
    faithful enough for consumers to elaborate, but every body and proof stays
    provisional until root-first Phase 1 validates and replaces it.
    """
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        f"```tex\n{ctx.stmt_blocks.get(label, '')[:3500]}\n```"
        for label in labels
    )
    signatures = _frozen_interface_digest(
        sections, import_modules, budget=14000
    )
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    feedback_block = ""
    if feedback:
        feedback_block = f"""

The previous provisional file did not compile. Correct only its declaration
syntax/types using this compiler output; do not start mathematical refinement:
```text
{feedback[-10000:]}
```

Previous provisional file:
```lean
{previous_code[:160000] or '-- unavailable'}
```
"""
    unavailable = ""
    if ctx.unavailable_imports:
        unavailable = (
            "\nDo not import these unavailable modules:\n"
            + "\n".join(f"- {item}" for item in sorted(ctx.unavailable_imports))
        )
    return f"""TASK: INITIAL-LEAN-DECLARATION-ENVIRONMENT

Return exactly one Lean 4 file in one code block. No commentary.

This is compilation scaffolding before mathematical statement refinement.
Create every requested Lean name with a faithful provisional type/signature so
that declarations which consume it can elaborate later. Do not prove or fully
implement anything in this call:
- theorem-like nodes must end in `:= by sorry`;
- use the Lean command `theorem` for every theorem-like node, including
  blueprint corollaries, claims, facts, and remarks; never emit `corollary`;
- definition-like nodes must expose the objects, fields, parameters, and result
  type described by the blueprint, but their body may also be `:= by sorry`;
- structures/inductives may be used when their named fields are required by
  consumers; otherwise prefer a typed `def ... := by sorry`;
- never use `axiom`, `constant`, `opaque`, `admit`, `True`, or a placeholder
  type that erases the node's parameters or mathematical role;
- use the exact generated name listed for every target and visibly use the
  supplied generated names for direct dependencies;
- emit every target. Never return NEEDS-DECOMPOSITION from this pass: missing
  helpers and exact contract corrections belong to Phase 1;
- do not attempt proofs, inspect the repository, run Lean, or search Mathlib.
  Use the verified imports and interfaces supplied below and spend the budget
  emitting complete code.

{_conjecture_policy_prompt(ctx, labels)}

The blueprint remains the source of truth, but these declarations are
provisional: the pipeline will not count them as accepted or proved. Phase 1
will deterministically check, compile, audit, and freeze their exact contracts
from roots down toward dependencies.

This call has a wall-clock budget of about {timeout_s}s.
{unavailable}
{feedback_block}

Blueprint name: {ctx.name}

Available imports for declarations already emitted:
```lean
{chr(10).join(f'import {m}' for m in import_modules) or '-- none'}
```

Available provisional interfaces (use these names; do not redefine them):
```lean
{signatures or '-- none'}
```

Resolved direct dependency ownership:
```text
{dependency_contracts}
```

Target nodes for this provisional file, in dependency order:
{target_text}
"""


def _skeleton_prompt(
    ctx: Ctx,
    labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    *,
    feedback: str = "",
    previous_code: str = "",
    timeout_s: int = 0,
    initial_only: bool = False,
) -> str:
    if initial_only:
        return _initial_declaration_prompt(
            ctx,
            labels,
            sections,
            import_modules,
            timeout_s=timeout_s,
            feedback=feedback,
            previous_code=previous_code,
        )
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        # Phase 1 still emits only the public declaration plus terminal
        # ``sorry``.  The complete node is nevertheless required here because
        # its proof sketch can impose representation/interface obligations that
        # the independent statement audit will later enforce.
        f"```tex\n{ctx.tex_blocks.get(label, '')[:6000]}\n```"
        for label in labels
    )
    feedback_block = ""
    if feedback:
        previous_block = (
            f"\nYour previous file (START FROM IT; change only what the feedback requires):\n"
            f"```lean\n{previous_code[:45000]}\n```\n"
            if previous_code
            else ""
        )
        feedback_block = f"""

Previous attempt feedback (fix ALL of it; statements may still be adjusted at
this phase, but only to encode the SAME blueprint content correctly):
```text
{feedback[-14000:]}
```
{previous_block}"""
    interface_rule = _phase1_interface_prompt_rule(feedback)
    signatures = _minimal_dependency_interface(
        ctx,
        labels,
        sections,
        import_modules,
        local_code=previous_code,
        budget=10000,
    )
    dependency_contracts = _dependency_contract_table(ctx, labels, sections)
    return f"""TASK: BLUEPRINT-SKELETON-SECTION

Return exactly one Lean 4 file (one code block). No commentary.

Generate ONE declaration per target node listed below — statements only:
- definition-kind nodes (definition/defn/construction/notation/convention):
  emit the exact public type/interface. For an ordinary definition, output
  only `def NAME ... : TYPE := sorry` (or `abbrev`): do not write the defining
  formula after `:=`, and do not move that formula into `TYPE`. A predicate
  described by conditions or witnesses is an ordinary `def ... : Prop :=
  sorry`, not a structure containing those conditions as fields. Use a
  `structure`/`class`/`inductive` only when the blueprint node genuinely
  defines a bundled data object with named stored components; list its real
  fields/constructors and do not use `sorry`. The one narrow
  exception is a type-valued target whose complete contract is a plan-owned
  structure/class/inductive: emit that helper completely and make the target a
  transparent alias such as `def target (n) : Type := OwnedInterface n`;
- theorem-like nodes (lemma/proposition/theorem/corollary and EVERY other
  environment kind, e.g. claim/fact/remark): the exact statement as a
  `theorem` ending in `:= sorry`. Do NOT attempt proofs at this phase: a
  proof body is discarded by the Phase-1 schema even if it succeeds. Never
  encode a theorem-like node as a bare
  `def : Prop`, except for conjectures explicitly governed by the `record`
  policy below.
- Emit no auxiliary `def`, `abbrev`, theorem, lemma, or instance declarations.
  A structural helper may be emitted only when needed to state a requested
  target. Return its complete typed declaration together with that target;
  this same Lean response becomes the persisted typed contract. A genuinely
  separate mathematical obligation requires `NEEDS-DECOMPOSITION`.
- Order declarations so nothing is used before it is declared.
- A statement should visibly use the generated Lean declarations of the
  definition nodes it `uses`; imports of earlier skeleton modules make them
  available (do not redefine them).
{_text_only_budget_rule(timeout_s)}

{_common_rules(ctx, labels)}
{interface_rule}
{feedback_block}

Blueprint name: {ctx.name}

Available imports for earlier accepted skeleton declarations:
```lean
{chr(10).join(f'import {m}' for m in import_modules) or '-- none'}
```

Minimal generated dependency interface (deterministically complete for the
target nodes; use these exact names and do not inspect generated files):
```lean
{signatures or '-- none'}
```

Resolved direct dependency contracts (generated deterministically):
```text
{dependency_contracts}
```
The ownership above is authoritative. In particular, a Mathlib-owned
dependency is already available under its settled declaration name and is not
a reason to return NEEDS-DECOMPOSITION.

{_design_plan_block(ctx, labels)}

Nearby blueprint nodes (orientation only; targets, their direct dependencies,
and their direct consumers):
{_local_node_summary(ctx, labels)}

Target nodes for THIS file:
{target_text}
"""


def _targeted_skeleton_patch_prompt(
    ctx: Ctx,
    patch_labels: list[str],
    sections: list[Section],
    import_modules: list[str],
    module_code: str,
    findings: list[SkeletonFinding],
    *,
    timeout_s: int,
    provisional_only: bool = False,
    findings_already_persisted: bool = False,
) -> str:
    target_text = "\n\n".join(
        f"## {label} ({ctx.nodes[label].kind}; Lean name `{_lean_name(label)}`; "
        f"statement uses "
        f"[{', '.join(sorted(_statement_uses(ctx.nodes[label]))) or 'none'}]; "
        f"proof-only uses "
        f"[{', '.join(sorted(_proof_uses(ctx.nodes[label]) - _statement_uses(ctx.nodes[label]))) or 'none'}])\n"
        # Keep compiler correction under the same semantic contract as fresh
        # generation.  Otherwise a patch can compile while erasing an
        # obligation stated only in the blueprint proof sketch.
        f"```tex\n{ctx.tex_blocks.get(label, '')[:6000]}\n```"
        for label in patch_labels
    )
    relevant = [
        finding
        for finding in findings
        if finding.label in set(patch_labels) or finding.lean_name in {_lean_name(label) for label in patch_labels}
    ]
    signatures = _minimal_dependency_interface(
        ctx,
        patch_labels,
        sections,
        import_modules,
        local_code=module_code,
        budget=8000,
    )
    provisional_rule = (
        "Repair the signature/type only. Return an ordinary target `def`/`abbrev` "
        "in the exact form `def NAME ... : TYPE := sorry`; do not write its "
        "defining formula after `:=` or move that formula into `TYPE`. A "
        "predicate is `def ... : Prop := sorry`, never a structure packaging "
        "its conditions. A target theorem must end in `:= sorry`; Phase 2 "
        "implements bodies and proofs. Structure/inductive fields and "
        "constructors must be exact only when the blueprint genuinely defines "
        "a bundled data object. "
        "A type-valued target may instead be a transparent alias directly to its "
        "same-node plan-owned structural interface; that alias is the public type "
        "contract, not a Phase-2 implementation."
    )
    planned_helpers = _planned_helper_specs(ctx, patch_labels)
    parsed_current = _parse_module(module_code)
    patch_names = {_lean_name(label) for label in patch_labels}
    helper_names = {
        str(helper.get("name") or "")
        for _owner, helper in planned_helpers
        if str(helper.get("name") or "")
    }
    focused_decls = [
        decl.text
        for decl in parsed_current.decls
        if decl.name in patch_names | helper_names
    ]
    focused_code, _focused_ranges = _compose_module(
        parsed_current.imports,
        parsed_current.preamble,
        focused_decls,
    )
    persisted_feedback = _generation_feedback_for(
        ctx,
        patch_labels,
        max_chars=12000,
    )
    interface_rule = _phase1_interface_prompt_rule(persisted_feedback)
    persisted_feedback_block = (
        "No earlier semantic or compiler rejection remains unresolved."
        if not persisted_feedback
        else """Unresolved correction constraints from earlier retries:
```text
{feedback}
```
These constraints remain mandatory. The current compiler finding supplements
them; it does not supersede them. Do not restore any previously rejected
weakening while fixing the current error.""".format(feedback=persisted_feedback)
    )
    current_findings = (
        "No additional findings; the exact active findings are in the persisted "
        "rejection evidence above."
        if findings_already_persisted and persisted_feedback
        else _format_skeleton_findings(relevant)[-10000:]
    )
    helper_rule = (
        "No plan-owned auxiliary type interface is required for these targets."
        if not planned_helpers and not interface_rule
        else (
            "The exact interface-usability evidence permits bounded named "
            "structure/class/inductive declarations owned by the same target. "
            "They must only package that node's existing mathematical data and "
            "obligations; they are not separate blueprint helpers."
            if not planned_helpers
            else
            "The only permitted auxiliary declarations are these exact plan-owned "
            "type interfaces; emit a complete replacement for any one named by a "
            "finding:\n"
            + "\n".join(
                f"  - {helper.get('kind')} {helper.get('name')} (owner {label}):\n"
                + "\n".join(
                    f"      {member.get('name')} : {member.get('type')}"
                    for member in helper.get("members") or []
                )
                for label, helper in planned_helpers
            )
        )
    )
    return f"""TASK: PATCH-BLUEPRINT-SKELETON-DECLARATIONS

Return exactly one Lean 4 code block. No commentary.

The large skeleton section below was generated in one batch. Most of it may be
usable. Replace ONLY the target declaration(s) listed below so the whole section
can pass the deterministic skeleton audit.

Rules:
- Return replacement declarations only; do not return the whole file.
- For each target blueprint node, include exactly one declaration with the
  required Lean name.
- {provisional_rule}
- Target theorem-like nodes and ordinary target `def`/`abbrev` bodies must end
  with terminal `:= sorry`; retain the transparent structural-alias exception
  described above. Recorded conjectures are instead exact proposition-valued
  `def` declarations as required by the policy below.
- The candidate-derived `TARGET` text is interface guidance, not permission to
  preserve a rejected declaration body. If it contains an implementation from
  an older candidate, retain its public header and replace the body with
  terminal `:= sorry`.
- Use the Lean command `theorem` for theorem-like nodes; never use `corollary`.
- If a finding concerns a partial or failing proof on a theorem-like node,
  replace that proof with terminal `:= sorry` — do not try to complete it;
  proofs are a later phase.
- The replacement statement must still encode the same blueprint node. Do not
  weaken, abstract away, or replace it with `True`.
- If a replacement must use another blueprint node listed in `uses`, visibly
  mention that node's generated Lean name.
- {helper_rule}
- Do not emit any helper `def`, `abbrev`, theorem, lemma, or instance beyond
  the exact plan-owned interfaces named above.
{_text_only_budget_rule(timeout_s)}

{_common_rules(ctx, patch_labels)}
{interface_rule}

Blueprint name: {ctx.name}

Available imports for earlier accepted skeleton declarations:
```lean
{chr(10).join(f'import {m}' for m in import_modules) or '-- none'}
```

Minimal generated dependency interface (deterministically complete for the
target declarations; do not inspect generated files):
```lean
{signatures or '-- none'}
```

{_design_plan_block(ctx, patch_labels, budget=4000)}

{persisted_feedback_block}

Deterministic audit findings to fix:
```text
{current_findings}
```

Current declarations owned by the repair targets (the complete dependency
interface is provided above):
```lean
{focused_code[:24000]}
```

Target blueprint nodes to patch:
{target_text}
"""


def _proof_prompt(
    ctx: Ctx,
    targets: list[tuple[str, str]],  # (label, frozen declaration text)
    sections: list[Section],
    import_modules: list[str],
    *,
    errors: dict[str, str] | None = None,
    singleton: bool = False,
    timeout_s: int = 0,
) -> str:
    errors = errors or {}
    parts: list[str] = []
    for label, decl_text in targets:
        node = ctx.nodes[label]
        deps = [
            _lean_name(dep)
            for dep in sorted(node.uses)
            if dep in ctx.nodes and not ctx.nodes[dep].mathlibok
        ]
        error_block = (
            f"\nPrevious attempt failed with:\n```text\n{errors[label][-4000:]}\n```"
            if label in errors
            else ""
        )
        parts.append(
            f"## {label}\n"
            f"Blueprint kind: {node.kind}\n"
            f"Frozen declaration (header/interface is IMMUTABLE):\n```lean\n{decl_text[:6000]}\n```\n"
            f"Required dependency mentions in the implementation or statement: "
            f"{', '.join(deps) or '(none)'}\n"
            f"Blueprint node with proof sketch:\n```tex\n{ctx.tex_blocks.get(label, '')[:6000]}\n```"
            f"{error_block}"
        )
    signatures = _frozen_interface_digest(sections, import_modules, budget=20000)
    downstream_context = _downstream_proof_context(
        ctx, [label for label, _decl in targets], sections
    )
    single_note = (
        "\nThis is an escalated single-declaration call; think as long as needed "
        "within the budget.\n"
        if singleton
        else ""
    )
    return f"""TASK: IMPLEMENT-FROZEN-DECLARATION-BODIES

Return exactly one Lean 4 code block. No commentary.

For EACH target declaration below, return that declaration with its terminal
`sorry` replaced by a real `:= by ...` body:
- Copy the frozen declaration header EXACTLY. Only the tactic body after
  `:= by` is used; any header or statement change is discarded.
- For theorem-like targets, produce a proof. For `def`/`abbrev` targets,
  construct the exact value/function/predicate described by the blueprint.
- Bodies must be self-contained tactic blocks (`have`/`let`/`calc` inside are
  fine). Do NOT add new top-level declarations; if an implementation genuinely
  needs a helper node, reply with NEEDS-DECOMPOSITION for that label instead.
- The implementation must certify or realize the blueprint obligations for
  this node. It does
  not need to mirror the prose line by line, but it must not bypass the
  blueprint argument by using an abstract theorem/tag/witness that erases the
  construction, case split, reduction, invariant, or intermediate claim the
  blueprint proof relies on.
- If a node's blueprint entry lists dependencies, the body (or statement)
  must visibly use their generated Lean names; a proof that re-derives a
  dependency inline will be rejected.
- You may add `import` lines for tactic modules you need.
- Dependency declarations may still have deferred bodies in the skeleton;
  using their frozen interfaces is exactly how the blueprint dependency graph
  is supposed to work.
{_text_only_budget_rule(timeout_s)}
{single_note}
{_common_rules(ctx, [label for label, _decl in targets])}

Blueprint name: {ctx.name}

Frozen Lean interface (same module and imported skeleton modules; use these
exact names — dependencies must be cited by them).
{FROZEN_INTERFACE_NOTE}
```lean
{signatures or '-- none'}
```

Higher-level obligations that consume this frontier (orientation only; do not
reference these downstream declarations from the current proof):
{downstream_context or '- This frontier contains public roots or has no theorem-like consumers.'}

Target declarations:
{chr(10).join(parts)}
"""
