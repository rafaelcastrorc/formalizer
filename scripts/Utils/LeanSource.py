"""Lean module parsing, model-output canonicalization, helper namespacing, body defer/splice.

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


def _block_comment_line_spans(lines: list[str]) -> tuple[dict[int, int], set[int]]:
    """Locate Lean block comments that span whole lines.

    Returns ``(opened_by, covered)`` where ``opened_by`` maps the index of the
    line closing a top-level block comment to the index of the line that opened
    it, and ``covered`` is every line index belonging to a block comment.

    Lean block comments nest, so depth is tracked rather than matched pairwise.
    A ``--`` line comment is only honoured outside a block comment, matching
    Lean's own lexer.  An unterminated comment still marks its remaining lines
    as covered so a truncated model response cannot leak prose into a
    declaration boundary.
    """
    opened_by: dict[int, int] = {}
    covered: set[int] = set()
    depth = 0
    start: int | None = None
    for idx, line in enumerate(lines):
        pos = 0
        width = len(line)
        while pos < width:
            pair = line[pos : pos + 2]
            if depth == 0 and pair == "--":
                break
            if pair == "/-":
                if depth == 0:
                    start = idx
                depth += 1
                pos += 2
                continue
            if pair == "-/" and depth > 0:
                depth -= 1
                pos += 2
                if depth == 0 and start is not None:
                    opened_by[idx] = start
                    covered.update(range(start, idx + 1))
                    start = None
                continue
            pos += 1
        if depth > 0 and start is not None:
            covered.update(range(start, idx + 1))
    return opened_by, covered


def _parse_module(code: str) -> ParsedModule:
    lines = code.splitlines()
    imports: list[str] = []
    body_lines: list[tuple[int, str]] = []
    for idx, line in enumerate(lines):
        stripped = line.strip()
        if stripped.startswith("import "):
            if stripped not in imports:
                imports.append(stripped)
            continue
        if stripped in {
            "set_option autoImplicit false",
            "set_option linter.unusedVariables false",
        }:
            continue
        body_lines.append((idx, line))

    # A multi-line `/-- ... -/` docstring is one prefix unit, not a sequence of
    # unrecognized module-level commands.  Without this, only its opening line
    # matches `_DECL_PREFIX_RE`, the backward walk stops immediately, and the
    # continuation lines are reported as invalid preamble.
    comment_opened_by, comment_covered = _block_comment_line_spans(
        [line for _orig, line in body_lines]
    )

    starts: list[int] = []  # indices into body_lines
    for pos, (_orig, line) in enumerate(body_lines):
        if pos in comment_covered:
            continue
        if _DECL_START_RE.match(line):
            start = pos
            while start > 0:
                previous = start - 1
                if previous in comment_opened_by:
                    start = comment_opened_by[previous]
                    continue
                if _DECL_PREFIX_RE.match(body_lines[previous][1]):
                    start = previous
                    continue
                break
            if not starts or start > starts[-1]:
                starts.append(start)

    preamble = [
        line for _orig, line in body_lines[: starts[0] if starts else len(body_lines)]
        if line.strip()
    ]
    decls: list[DeclBlock] = []
    for i, start in enumerate(starts):
        end = starts[i + 1] if i + 1 < len(starts) else len(body_lines)
        text = "\n".join(line for _orig, line in body_lines[start:end]).strip()
        match = next(
            (
                _DECL_START_RE.match(line)
                for offset, (_orig, line) in enumerate(body_lines[start:end])
                if start + offset not in comment_covered
                and _DECL_START_RE.match(line)
            ),
            None,
        )
        decls.append(
            DeclBlock(
                kind=match.group(1) if match else "def",
                name=match.group(2) if match else None,
                text=text,
            )
        )
    return ParsedModule(imports=imports, preamble=preamble, decls=decls)


def _normalize_theorem_like_keywords(
    parsed: ParsedModule, nodes: dict[str, Node], labels: Iterable[str]
) -> ParsedModule:
    """Rewrite model-facing theorem synonyms to Lean's ``theorem`` command.

    Blueprint node kinds include ``corollary``, ``claim``, and other
    theorem-like prose categories, but Lean declarations use ``theorem`` (or
    ``lemma``).  Normalizing after parsing keeps an otherwise useful model
    response from becoming both an invalid command and an apparent omission.
    """
    theorem_names = {
        _lean_name(label)
        for label in labels
        if label in nodes and _is_theorem_like_kind(nodes[label].kind)
    }
    normalized: list[DeclBlock] = []
    for decl in parsed.decls:
        if decl.name in theorem_names and decl.kind == "corollary":
            text = re.sub(
                r"^(\s*(?:@\[[^\]]+\]\s*)*"
                r"(?:(?:noncomputable|private|protected|unsafe|partial)\s+)*)"
                r"corollary\b",
                r"\1theorem",
                decl.text,
                count=1,
            )
            normalized.append(DeclBlock("theorem", decl.name, text))
        else:
            normalized.append(decl)
    return ParsedModule(parsed.imports, parsed.preamble, normalized)


def _remove_model_module_wrappers(code: str) -> str:
    """Remove balanced module wrappers that are not part of declarations.

    Models often wrap otherwise valid output in ``namespace`` or ``section``.
    Generated declarations have globally fixed names, so wrappers are response
    formatting rather than mathematical content. They are removed before
    parsing; malformed/unbalanced wrappers are rejected instead of leaking into
    persistent state.
    """
    wrappers: list[tuple[str, str]] = []
    kept: list[str] = []
    for line in code.splitlines():
        start = _MODEL_WRAPPER_START_RE.match(line)
        if start and not line.strip().startswith("noncomputable"):
            wrappers.append((start.group("kind"), start.group("name") or ""))
            continue
        end = _MODEL_WRAPPER_END_RE.match(line)
        if end:
            if not wrappers:
                raise ValueError(f"unmatched model module wrapper `{line.strip()}`")
            _kind, expected_name = wrappers.pop()
            actual_name = end.group("name") or ""
            if expected_name and actual_name and expected_name != actual_name:
                raise ValueError(
                    "mismatched model module wrapper: "
                    f"expected `end {expected_name}`, got `{line.strip()}`"
                )
            continue
        kept.append(line)
    if wrappers:
        kind, name = wrappers[-1]
        raise ValueError(
            f"unclosed model module wrapper `{kind}{(' ' + name) if name else ''}`"
        )
    return "\n".join(kept)


def _declaration_owner_map(
    parsed: ParsedModule,
    label_by_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> dict[int, str]:
    """Assign targets and local helpers to blueprint-node owners.

    Planned helpers have explicit owners fixed by the accepted interface plan.
    Adjacency remains only as a fallback for genuinely unplanned helpers.
    """
    explicit = explicit_owner_by_name or {}
    owners: dict[int, str] = {}
    following: str | None = None
    for index in range(len(parsed.decls) - 1, -1, -1):
        direct = label_by_name.get(parsed.decls[index].name or "")
        if direct is not None:
            following = direct
        if following is not None:
            owners[index] = following
    previous: str | None = None
    for index, decl in enumerate(parsed.decls):
        direct = label_by_name.get(decl.name or "")
        if direct is not None:
            previous = direct
        elif index not in owners and previous is not None:
            owners[index] = previous
    for index, decl in enumerate(parsed.decls):
        owner = explicit.get(decl.name or "")
        if owner is not None:
            owners[index] = owner
    return owners


def _declaration_target_consumers(
    parsed: ParsedModule,
    target_by_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> dict[int, set[str]]:
    """Return every target that transitively references each declaration.

    Model responses may define one local helper that several blueprint targets
    consume. File adjacency cannot represent that relationship. This reference
    graph is the canonical ownership source used by namespacing, semantic cache
    keys, candidate slicing, and persistence.
    """
    index_by_name = {
        decl.name: index
        for index, decl in enumerate(parsed.decls)
        if decl.name
    }
    names = set(index_by_name)
    references: dict[int, set[int]] = {}
    for index, decl in enumerate(parsed.decls):
        own = decl.name or ""
        referenced = {
            name
            for name in names
            if name != own
            and re.search(
                rf"(?<![A-Za-z0-9_'.]){re.escape(name)}(?![A-Za-z0-9_'.])",
                decl.text,
            )
        }
        references[index] = {index_by_name[name] for name in referenced}

    consumers: dict[int, set[str]] = {
        index: set() for index in range(len(parsed.decls))
    }
    explicit = explicit_owner_by_name or {}
    for target_name, target in target_by_name.items():
        start = index_by_name.get(target_name)
        if start is None:
            continue
        consumers[start].add(target)
        stack = list(references.get(start, set()))
        seen: set[int] = set()
        while stack:
            index = stack.pop()
            if index in seen:
                continue
            seen.add(index)
            if (parsed.decls[index].name or "") not in target_by_name:
                consumers[index].add(target)
                stack.extend(references.get(index, set()))

    # Phase-1 target bodies are intentionally ``sorry``, so textual references
    # cannot recover ownership for plan-required helper interfaces. The plan is
    # authoritative for those helpers and must win over declaration adjacency.
    for index, decl in enumerate(parsed.decls):
        owner = explicit.get(decl.name or "")
        if owner is not None:
            consumers[index] = {owner}

    # Keep harmless unreferenced helpers deterministic. They cannot join two
    # components, but preserving their adjacent owner avoids silently dropping
    # model output before deterministic checks decide whether it is acceptable.
    fallback = _declaration_owner_map(
        parsed, target_by_name, explicit_owner_by_name
    )
    for index, owner in fallback.items():
        if not consumers[index]:
            consumers[index].add(owner)
    return consumers


def _target_components_from_helpers(
    parsed: ParsedModule,
    target_by_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None = None,
) -> list[set[str]]:
    """Connected target components induced by shared local declarations."""
    targets = list(dict.fromkeys(target_by_name.values()))
    parent = {target: target for target in targets}

    def find(item: str) -> str:
        while parent[item] != item:
            parent[item] = parent[parent[item]]
            item = parent[item]
        return item

    def union(left: str, right: str) -> None:
        left_root, right_root = find(left), find(right)
        if left_root != right_root:
            parent[right_root] = left_root

    consumers = _declaration_target_consumers(
        parsed, target_by_name, explicit_owner_by_name
    )
    for index, owners in consumers.items():
        name = parsed.decls[index].name or ""
        if name in target_by_name or len(owners) < 2:
            continue
        ordered = sorted(owners)
        for owner in ordered[1:]:
            union(ordered[0], owner)
    grouped: dict[str, set[str]] = {}
    for target in targets:
        grouped.setdefault(find(target), set()).add(target)
    return list(grouped.values())


def _lean_identifier_replace(text: str, old: str, new: str) -> str:
    """Replace one ordinary Lean identifier without touching longer names."""
    return re.sub(
        rf"(?<![A-Za-z0-9_'.]){re.escape(old)}(?![A-Za-z0-9_'.])",
        lambda _match: new,
        text,
    )


def _declared_name_replace(text: str, old: str, new: str) -> str:
    """Rename only the declaration introduced by this block.

    This is distinct from replacing references in the declaration body: a
    structure may bind a field with the same spelling as its own old global
    name, and that field must continue to shadow the global declaration.
    """
    match = _DECL_START_RE.match(text)
    if match is None or match.group(2) != old:
        return text
    start, end = match.span(2)
    return text[:start] + new + text[end:]


def _restore_planned_member_declarations(
    text: str,
    helper: dict[str, Any],
    aliases: dict[str, str],
) -> str:
    """Keep structure/class field names stable while helpers are namespaced.

    A plan may legitimately give a helper and one of its fields the same name,
    for example ``class weightOf where weightOf : ...``. Helper aliases name
    global declarations; they must not rename member declarations that happen
    to use the same token. References to the helper type remain canonicalized.
    """
    members = _planned_member_names(helper)
    for member in sorted(members):
        replacement = aliases.get(member)
        if not member or not replacement or replacement == member:
            continue
        text = re.sub(
            rf"(?m)^(\s*(?:\|\s*)?){re.escape(replacement)}(?=\s*:)",
            lambda match: match.group(1) + member,
            text,
        )
    return text


def _planned_member_names(helper: dict[str, Any]) -> set[str]:
    """Names bound by one planned structure/class declaration.

    These names shadow equally named global helper declarations throughout the
    declaration body. For example, after a field
    ``DensityOperator : Register -> Type``, a later field type
    ``DensityOperator R`` refers to that field, not to a global helper also
    called ``DensityOperator``.
    """
    members = {
        str(item.get("name") or "").strip()
        for item in helper.get("members") or []
        if isinstance(item, dict)
    }
    members.update(
        str(item).strip() for item in helper.get("required_members") or []
    )
    return {member for member in members if member}


def _owned_helper_name(ctx: Ctx, name: str, owners: Iterable[str]) -> str:
    """Canonical global name assigned to one model-created local helper."""
    owner_list = sorted(set(owners))
    if not name or not owner_list:
        return name
    digest = hashlib.sha256(
        (
            f"{getattr(ctx, 'name', 'blueprint')}\0"
            + "\0".join(owner_list)
        ).encode("utf-8")
    ).hexdigest()[:12]
    prefix = f"_autobp_{digest}_"
    if name.startswith(prefix):
        return name
    safe_name = re.sub(r"[^A-Za-z0-9_']", "_", name)
    return prefix + safe_name


def _planned_helper_specs(
    ctx: Ctx, labels: Iterable[str]
) -> list[tuple[str, dict[str, Any]]]:
    """Return valid plan-owned helper contracts for the requested nodes."""
    entries = getattr(ctx, "design_plan_entries", {})
    specs: list[tuple[str, dict[str, Any]]] = []
    for label in labels:
        entry = entries.get(label) or {}
        if int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION:
            continue
        for helper in entry.get("helpers") or []:
            if str(helper.get("name") or "").strip():
                specs.append((label, helper))
    return specs


def _planned_helper_owner_by_name(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, str]:
    """Map canonical plan helper names to their blueprint-node owners."""
    return {
        _owned_helper_name(ctx, str(helper["name"]), [label]): label
        for label, helper in _planned_helper_specs(ctx, labels)
    }


def _semantic_helper_owner_by_name(
    ctx: Ctx, labels: Iterable[str]
) -> dict[str, str]:
    """Unambiguous advisory vocabulary ownership for first-pass ingestion."""
    owners: dict[str, set[str]] = {}
    requested = set(labels)
    for label, entry in getattr(ctx, "semantic_plan_entries", {}).items():
        if label not in requested:
            continue
        for item in entry.get("vocabulary") or []:
            if not isinstance(item, dict):
                continue
            name = str(item.get("name") or "").strip()
            if name:
                owners.setdefault(name, set()).add(label)
    return {
        name: next(iter(labels_for_name))
        for name, labels_for_name in owners.items()
        if len(labels_for_name) == 1
    }


def _planned_helper_aliases(ctx: Ctx) -> dict[str, str]:
    """Map model-facing plan spellings to canonical helper declarations.

    Contract plans commonly write an owned helper as ``target.Helper`` while
    generated modules store globally unique names. Later batches do not emit
    the helper again, so canonical ingestion must normalize those dependency
    references using the complete accepted plan, not wait for Lean to reject
    every consumer separately.
    """
    entries = getattr(ctx, "design_plan_entries", {})
    aliases: dict[str, str] = {}
    bare_candidates: dict[str, set[str]] = {}
    for label, entry in entries.items():
        if int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION:
            continue
        owner_name = _lean_name(label)
        for helper in entry.get("helpers") or []:
            helper_name = str(helper.get("name") or "").strip()
            if not helper_name:
                continue
            canonical = _owned_helper_name(ctx, helper_name, [label])
            bare_candidates.setdefault(helper_name, set()).add(canonical)
            qualified = f"{owner_name}.{helper_name}"
            flattened = re.sub(r"[^A-Za-z0-9_']", "_", qualified)
            for alias in (
                qualified,
                flattened,
                _owned_helper_name(ctx, qualified, [label]),
                _owned_helper_name(ctx, flattened, [label]),
            ):
                if alias != canonical:
                    aliases[alias] = canonical
    # Plan target signatures deliberately use compact model-facing helper
    # names. Once providers and consumers are generated in separate modules,
    # those bare names must resolve to the persisted globally unique helper.
    # Rewrite only names that have exactly one owner across the complete plan;
    # ambiguous helper spellings remain untouched and are rejected normally.
    for helper_name, canonical_names in bare_candidates.items():
        if len(canonical_names) == 1:
            canonical = next(iter(canonical_names))
            if helper_name != canonical:
                aliases[helper_name] = canonical
    return aliases


def _planned_helper_assignments(
    ctx: Ctx,
    labels: list[str],
    parsed: ParsedModule,
    target_names: set[str],
) -> dict[int, tuple[str, str]]:
    """Match emitted helper declarations to accepted interface contracts.

    Models often qualify a planned helper with the target namespace or emit an
    already-canonical name. Exact name/suffix matches are unambiguous. If the
    name differs, kind plus the complete required-member surface may identify
    a helper, but only a mutual unique match is accepted. Ambiguous output is
    left untouched for the deterministic handoff gate to reject; this function
    never guesses ownership.
    """
    specs = _planned_helper_specs(ctx, labels)
    candidates = [
        index
        for index, decl in enumerate(parsed.decls)
        if decl.name and decl.name not in target_names
    ]
    assigned: dict[int, tuple[str, str]] = {}
    used_specs: set[int] = set()

    def canonical_for(spec_index: int) -> str:
        label, helper = specs[spec_index]
        return _owned_helper_name(ctx, str(helper["name"]), [label])

    def exact_name_match(decl_name: str, spec_index: int) -> bool:
        _label, helper = specs[spec_index]
        helper_name = str(helper["name"])
        safe_name = re.sub(r"[^A-Za-z0-9_']", "_", helper_name)
        return (
            decl_name == helper_name
            or decl_name == canonical_for(spec_index)
            or decl_name.endswith("." + helper_name)
            or (
                decl_name.startswith("_autobp_")
                and decl_name.endswith("_" + safe_name)
            )
        )

    # Contract names are globally unique within a valid plan. Resolve those
    # matches first, independent of declaration adjacency or target bodies.
    for spec_index, (label, helper) in enumerate(specs):
        matches = [
            index
            for index in candidates
            if index not in assigned
            and exact_name_match(parsed.decls[index].name or "", spec_index)
        ]
        if len(matches) == 1:
            assigned[matches[0]] = (label, str(helper["name"]))
            used_specs.add(spec_index)

    # A model may choose a different local name. Recover it only when the
    # accepted kind/member contract creates a one-to-one correspondence.
    candidate_specs: dict[int, list[int]] = {}
    spec_candidates: dict[int, list[int]] = {}
    for spec_index, (_label, helper) in enumerate(specs):
        if spec_index in used_specs:
            continue
        expected_kind = str(helper.get("kind") or "")
        members = [str(item) for item in helper.get("required_members") or []]
        if not members:
            continue
        for index in candidates:
            if index in assigned:
                continue
            decl = parsed.decls[index]
            if decl.kind != expected_kind:
                continue
            if not all(
                re.search(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(member)}"
                    rf"(?![A-Za-z0-9_'.])",
                    decl.text,
                )
                for member in members
            ):
                continue
            candidate_specs.setdefault(index, []).append(spec_index)
            spec_candidates.setdefault(spec_index, []).append(index)
    for spec_index, matches in spec_candidates.items():
        if len(matches) != 1:
            continue
        index = matches[0]
        if len(candidate_specs.get(index, [])) != 1:
            continue
        label, helper = specs[spec_index]
        assigned[index] = (label, str(helper["name"]))
    return assigned


def _namespace_owned_helpers(
    ctx: Ctx, labels: Iterable[str], parsed: ParsedModule
) -> ParsedModule:
    """Give model-created helpers stable node-owned global names.

    Candidate modules are compiled independently and later imported together.
    A harmless local name such as ``ceilLog`` therefore becomes a global Lean
    collision when two candidates choose it. Public blueprint declarations keep
    their required names; only non-target declarations are alpha-renamed using
    the blueprint name and owning node. The transformation is deterministic and
    requires no model call.
    """
    label_list = list(labels)
    label_by_name = {_lean_name(label): label for label in label_list}
    planned = _planned_helper_assignments(
        ctx, label_list, parsed, set(label_by_name)
    )
    explicit_raw_owners = {
        parsed.decls[index].name or "": label
        for index, (label, _helper_name) in planned.items()
    }
    for name, label in _semantic_helper_owner_by_name(ctx, label_list).items():
        if any(decl.name == name for decl in parsed.decls):
            explicit_raw_owners.setdefault(name, label)
    consumers = _declaration_target_consumers(
        parsed, label_by_name, explicit_raw_owners
    )
    renames: dict[str, str] = {}
    for index, decl in enumerate(parsed.decls):
        name = decl.name or ""
        planned_assignment = planned.get(index)
        if planned_assignment is not None:
            owner, helper_name = planned_assignment
            canonical_name = _owned_helper_name(ctx, helper_name, [owner])
            if canonical_name != name:
                renames[name] = canonical_name
            continue
        owners = sorted(consumers.get(index) or [])
        if not name or name in label_by_name or not owners:
            continue
        canonical_name = _owned_helper_name(ctx, name, owners)
        if canonical_name != name:
            renames[name] = canonical_name
    plan_aliases = _planned_helper_aliases(ctx)
    if not renames and not planned and not plan_aliases:
        return parsed

    renamed: list[DeclBlock] = []
    applied_plan_aliases: set[str] = set()
    helper_specs = {
        (label, str(helper.get("name") or "")): helper
        for label, helper in _planned_helper_specs(ctx, label_list)
    }
    all_aliases = dict(plan_aliases)
    all_aliases.update(renames)
    for index, decl in enumerate(parsed.decls):
        text = decl.text
        assignment = planned.get(index)
        helper = helper_specs.get(assignment) if assignment is not None else None
        shadowed_members = _planned_member_names(helper) if helper else set()
        declared_name = decl.name or ""
        if declared_name in shadowed_members and declared_name in renames:
            text = _declared_name_replace(
                text, declared_name, renames[declared_name]
            )
        # Replace qualified declaration names before their shorter planned
        # aliases so ``target.Helper`` cannot become ``target._autobp_...``.
        for old, new in sorted(renames.items(), key=lambda item: -len(item[0])):
            if old in shadowed_members:
                continue
            text = _lean_identifier_replace(text, old, new)
        for helper_index, (_owner, helper_name) in planned.items():
            if helper_name in shadowed_members:
                continue
            old_name = parsed.decls[helper_index].name or ""
            canonical_name = renames.get(old_name, old_name)
            if helper_name != old_name:
                text = _lean_identifier_replace(text, helper_name, canonical_name)
        for alias, canonical_name in sorted(
            plan_aliases.items(), key=lambda item: -len(item[0])
        ):
            if alias in shadowed_members:
                continue
            rewritten = _lean_identifier_replace(text, alias, canonical_name)
            if rewritten != text:
                applied_plan_aliases.add(alias)
            text = rewritten
        if helper is not None:
            text = _restore_planned_member_declarations(
                text, helper, all_aliases
            )
        renamed.append(
            DeclBlock(decl.kind, renames.get(decl.name or "", decl.name), text)
        )
    if hasattr(ctx, "telemetry"):
        _record(
            ctx.telemetry,
            "model_helpers_namespaced",
            labels=label_list,
            helper_count=len(renames),
            original_names=sorted(renames),
            planned_helpers=len(planned),
            planned_aliases=sorted(applied_plan_aliases),
        )
    return ParsedModule(parsed.imports, parsed.preamble, renamed)


def _canonicalize_model_lean(
    ctx: Ctx,
    labels: Iterable[str],
    code: str,
    *,
    strict_duplicates: bool = True,
) -> CanonicalModelModule:
    """Convert raw model Lean into the only representation the pipeline stores.

    Imports are retained for later availability checks. The pipeline keeps only
    the small preamble it knows how to render, normalizes theorem-like commands,
    enforces globally unique declaration names, and records helper ownership.
    """
    label_list = list(labels)
    wrapper_count = sum(
        1
        for line in code.splitlines()
        if _MODEL_WRAPPER_START_RE.match(line)
        and not line.strip().startswith("noncomputable")
    )
    source = _remove_model_module_wrappers(code)
    parsed = _parse_module(source)
    theorem_keyword_normalizations = sum(
        1
        for decl in parsed.decls
        if decl.kind == "corollary"
        and decl.name in {_lean_name(label) for label in label_list}
    )
    parsed = _normalize_theorem_like_keywords(parsed, ctx.nodes, label_list)

    invalid_preamble = [
        line
        for line in parsed.preamble
        if line.strip()
        and not line.lstrip().startswith(("--", "/-"))
        and not _ALLOWED_MODEL_PREAMBLE_RE.match(line)
    ]
    if invalid_preamble:
        raise ValueError(
            "model response contains unsupported module-level command(s): "
            + ", ".join(repr(line.strip()) for line in invalid_preamble[:4])
        )
    parsed.preamble = [
        line.strip()
        for line in parsed.preamble
        if _ALLOWED_MODEL_PREAMBLE_RE.match(line)
    ]

    seen: set[str] = set()
    unique: list[DeclBlock] = []
    duplicates: list[str] = []
    for decl in parsed.decls:
        if decl.name and decl.name in seen:
            duplicates.append(decl.name)
            if not strict_duplicates:
                continue
        if decl.name:
            seen.add(decl.name)
        unique.append(decl)
    if duplicates and strict_duplicates:
        raise ValueError(
            "model response repeats declaration name(s): "
            + ", ".join(sorted(set(duplicates)))
        )
    parsed.decls = unique

    parsed = _namespace_owned_helpers(ctx, label_list, parsed)

    label_by_name = {_lean_name(label): label for label in label_list}
    owner_by_index = _declaration_owner_map(
        parsed,
        label_by_name,
        _planned_helper_owner_by_name(ctx, label_list),
    )
    helper_count = sum(
        1
        for decl in parsed.decls
        if decl.name and decl.name not in label_by_name
    )
    if hasattr(ctx, "telemetry"):
        _record(
            ctx.telemetry,
            "model_lean_canonicalized",
            labels=label_list,
            declarations=len(parsed.decls),
            helpers=helper_count,
            wrappers_removed=wrapper_count,
            theorem_keywords_normalized=theorem_keyword_normalizations,
            strict_duplicates=strict_duplicates,
        )
    return CanonicalModelModule(
        parsed=parsed,
        owner_by_index=owner_by_index,
    )


def _realize_typed_contracts_from_candidate(
    ctx: Ctx,
    labels: Iterable[str],
    canonical: CanonicalModelModule,
) -> set[str]:
    """Make the checked Lean candidate its own authoritative typed contract.

    Fresh runs no longer ask the global planner to predict Lean signatures.
    The first Phase-1 response supplies the target and structural-helper
    declarations atomically. Any later compiler/audit patch refreshes the same
    entries from the replacement candidate, so code cannot be forced to obey a
    stale independently generated plan.
    """
    requested = [label for label in labels if label in ctx.nodes]
    if not requested or not getattr(ctx, "semantic_plan_entries", {}):
        return set()
    entries = getattr(ctx, "design_plan_entries", {})
    ctx.design_plan_entries = entries
    target_by_name = {_lean_name(label): label for label in requested}
    owner_by_index = dict(canonical.owner_by_index)
    explicit_owners = _planned_helper_owner_by_name(ctx, requested)
    owner_by_name = {
        decl.name: owner_by_index[index]
        for index, decl in enumerate(canonical.parsed.decls)
        if decl.name and index in owner_by_index
    }
    for index, decl in enumerate(canonical.parsed.decls):
        if (
            decl.name
            and decl.name not in target_by_name
            and decl.kind in {"structure", "class", "inductive"}
            and index in owner_by_index
        ):
            explicit_owners.setdefault(decl.name, owner_by_index[index])
    realized: set[str] = set()
    changed: set[str] = set()
    for label in requested:
        previous = entries.get(label) or {}
        # Preserve a resumed legacy contract. Only contracts created at this
        # atomic boundary follow subsequent candidate revisions.
        if previous and previous.get("origin") != "phase1_candidate":
            continue
        target_name = _lean_name(label)
        target = next(
            (decl for decl in canonical.parsed.decls if decl.name == target_name),
            None,
        )
        if target is None:
            continue
        helpers: list[dict[str, Any]] = []
        for index, decl in enumerate(canonical.parsed.decls):
            if (
                not decl.name
                or decl.name in target_by_name
                or owner_by_index.get(index) != label
                or decl.kind not in DESIGN_PLAN_HELPER_KINDS
            ):
                continue
            declaration = _decl_interface_text(decl)
            members = sorted(_planned_target_members(declaration, decl.name))
            helpers.append(
                {
                    "name": decl.name,
                    "kind": decl.kind,
                    "declaration": declaration,
                    "members": [],
                    "required_members": members,
                    "purpose": "Typed structural interface realized with the Phase-1 candidate.",
                }
            )
        semantic = getattr(ctx, "semantic_plan_entries", {}).get(label) or {}
        decisions = []
        representation = str(semantic.get("representation") or "").strip()
        if representation:
            decisions.append("Representation: " + representation)
        decisions.extend(
            "Preserve: " + str(item).strip()
            for item in semantic.get("obligations") or []
            if str(item).strip()
        )
        progress = {
            key: previous.get(key)
            for key in _PLAN_ENTRY_PROGRESS_KEYS
            if key in previous
        }
        expected_kind = _phase1_target_kinds(ctx, [label]).get(target_name, "")
        structural_alias = _is_phase1_structural_target_alias(
            target,
            expected_kind,
            canonical.parsed,
            owner_by_name,
            explicit_owners,
        )
        replacement = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": ctx.stmt_fps[label],
            # Phase 1 owns the public declaration surface, never an ordinary
            # definition body or theorem proof.  Keeping a completed body here
            # made the next repair prompt call it an "exact typed contract";
            # the model then moved that body into the result type to satisfy the
            # simultaneous `:= sorry` rule.  Strip ordinary bodies even when a
            # caller presents an unnormalised historical candidate.
            "target_signature": (
                _decl_interface_text(target)
                if structural_alias
                else _phase1_target_interface_text(target)
            ),
            "helpers": helpers,
            "decisions": decisions,
            "origin": "phase1_candidate",
            **progress,
        }
        if replacement != previous:
            changed.add(label)
        entries[label] = replacement
        realized.add(label)
    if realized:
        if changed:
            # This is the result of the current generation transaction, not a
            # new plan or generation strategy. Crossing the full epoch
            # boundary here used to erase the candidate's persisted retry
            # lifecycle every time a compiler/audit correction changed its
            # declaration header. That made repeated failures look like
            # independent first failures and prevented bounded exhaustion.
            #
            # True authority changes (blueprint edits, plan replacement, and
            # first blueprint-direct activation) still use
            # ``_transition_phase1_generation_epoch``. A candidate-owned
            # contract refresh only updates the compatibility plan view; the
            # new candidate is stored by the caller in the same lifecycle.
            _sync_design_plan(ctx)
            _record(
                ctx.telemetry,
                "phase1_candidate_contract_refreshed",
                labels=sorted(changed),
                retry_lifecycle_preserved=True,
                generation_candidates_preserved=True,
                exchange_history_preserved=True,
            )
        else:
            _sync_design_plan(ctx)
        _record(
            ctx.telemetry,
            "phase1_typed_contract_realized",
            labels=sorted(realized),
            source="same_model_response_as_lean_candidate",
            typed_contract_model_calls=0,
            semantic_plan_authoritative=False,
        )
    return realized


def _ingest_model_lean(
    ctx: Ctx,
    labels: Iterable[str],
    response: str,
    *,
    strict_duplicates: bool = True,
    realize_contracts: bool = False,
    defer_phase1_bodies: bool = False,
) -> CanonicalModelModule:
    """Extract and canonicalize a Lean code block returned by a model."""
    canonical = _canonicalize_model_lean(
        ctx,
        labels,
        _extract_lean_code(response),
        strict_duplicates=strict_duplicates,
    )
    if defer_phase1_bodies:
        canonical = _defer_phase1_target_bodies(ctx, labels, canonical)
    if realize_contracts:
        _realize_typed_contracts_from_candidate(ctx, labels, canonical)
    return canonical


def _compose_module(
    imports: list[str], preamble: list[str], decl_texts: list[str]
) -> tuple[str, list[tuple[int, int]]]:
    """Compose a module file; return (text, per-decl (start,end) 1-based line ranges)."""
    lines: list[str] = []
    seen: set[str] = set()
    for item in imports:
        if item not in seen:
            seen.add(item)
            lines.append(item)
    if not lines:
        lines.append("import Mathlib.Data.Real.Basic")
    lines += ["", "set_option autoImplicit false", "set_option linter.unusedVariables false", ""]
    lines += [line for line in preamble if line.strip()]
    if preamble:
        lines.append("")
    ranges: list[tuple[int, int]] = []
    for text in decl_texts:
        start = len(lines) + 1
        decl_lines = text.splitlines()
        lines.extend(decl_lines)
        ranges.append((start, len(lines)))
        lines.append("")
    return "\n".join(lines) + "\n", ranges


def _has_terminal_sorry(decl_text: str) -> bool:
    return bool(_TERMINAL_SORRY_RE.search(decl_text.rstrip()))


def _normalize_terminal_sorry(decl_text: str) -> str:
    return _TERMINAL_SORRY_RE.sub(":= sorry", decl_text.rstrip())


def _terminal_sorry_interface_text(decl_text: str) -> str | None:
    """Remove only a declaration's final Phase-1 ``:= sorry`` marker.

    A declaration result type may itself contain unparenthesized ``let`` or
    ``letI`` assignments.  Those assignments are part of the public contract,
    so finding the first top-level ``:=`` would truncate valid Lean.  The
    terminal marker is unambiguous and is therefore authoritative whenever it
    is present.
    """
    text = decl_text.rstrip()
    match = _TERMINAL_SORRY_RE.search(text)
    if match is None:
        return None
    return text[: match.start()].rstrip()


def _top_level_assignment_index(decl_text: str) -> int | None:
    """Locate a declaration's top-level ``:=`` without matching binder syntax.

    Phase 1 receives model-authored Lean, so a plain ``split(':=', 1)`` is not
    safe: binder types, strings, and comments may themselves contain ``:=``.
    This small lexer recognizes exactly the boundary needed to retain a public
    declaration header while deferring its body.
    """
    depths = {"(": 0, "[": 0, "{": 0}
    closing = {")": "(", "]": "[", "}": "{"}
    block_depth = 0
    line_comment = False
    in_string = False
    escaped = False
    index = 0
    while index < len(decl_text):
        pair = decl_text[index : index + 2]
        char = decl_text[index]
        if line_comment:
            if char == "\n":
                line_comment = False
            index += 1
            continue
        if block_depth:
            if pair == "/-":
                block_depth += 1
                index += 2
            elif pair == "-/":
                block_depth -= 1
                index += 2
            else:
                index += 1
            continue
        if in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        if pair == "--":
            line_comment = True
            index += 2
            continue
        if pair == "/-":
            block_depth = 1
            index += 2
            continue
        if char == '"':
            in_string = True
            index += 1
            continue
        if char in depths:
            depths[char] += 1
            index += 1
            continue
        if char in closing:
            opener = closing[char]
            depths[opener] = max(0, depths[opener] - 1)
            index += 1
            continue
        if pair == ":=" and not any(depths.values()):
            return index
        index += 1
    return None


def _phase1_target_interface_text(decl: DeclBlock) -> str:
    """Return a Phase-1 target contract without an implementation/proof body."""
    if decl.kind in {"def", "abbrev", "theorem", "lemma"}:
        deferred = _terminal_sorry_interface_text(decl.text)
        if deferred is not None:
            return deferred
        boundary = _top_level_assignment_index(decl.text)
        if boundary is not None:
            return decl.text[:boundary].rstrip()
    return _decl_interface_text(decl)


def _deferred_prop_structure(decl: DeclBlock) -> str | None:
    """Convert the invalid Phase-1 shape ``structure ... : Prop where``.

    A structure whose sort is ``Prop`` cannot be the bundled data interface
    allowed by Phase 1. Models sometimes use its fields to spell a predicate's
    conditions. The public interface is already present in the structure
    header, so retain that header as an ordinary deferred predicate instead of
    paying for a compiler failure and model repair.
    """
    if decl.kind != "structure":
        return None
    match = re.match(
        r"\s*structure\s+(?P<header>[\s\S]*?:\s*Prop)\s+where\b",
        decl.text,
    )
    if match is None:
        return None
    return "def " + match.group("header").strip() + " := sorry"


def _defer_phase1_target_bodies(
    ctx: Ctx,
    labels: Iterable[str],
    canonical: CanonicalModelModule,
) -> CanonicalModelModule:
    """Enforce the Phase-1 output contract at the shared model boundary.

    Models choose public Lean headers; the pipeline owns the provisional body.
    This prevents a provider from spending Phase 1 implementing a definition or
    proof and, more importantly, prevents that body from becoming authoritative
    input to the next correction prompt. Candidate-owned structural interfaces
    and their transparent type aliases remain unchanged.
    """
    label_list = [label for label in labels if label in ctx.nodes]
    target_kinds = _phase1_target_kinds(ctx, label_list)
    explicit_owners = _planned_helper_owner_by_name(ctx, label_list)
    for index, decl in enumerate(canonical.parsed.decls):
        if (
            decl.name
            and decl.name not in target_kinds
            and decl.kind in {"structure", "class", "inductive"}
            and index in canonical.owner_by_index
        ):
            explicit_owners.setdefault(
                decl.name, canonical.owner_by_index[index]
            )
    owner_by_name = {
        decl.name: canonical.owner_by_index[index]
        for index, decl in enumerate(canonical.parsed.decls)
        if decl.name and index in canonical.owner_by_index
    }
    changed: list[str] = []
    for decl in canonical.parsed.decls:
        expected_kind = target_kinds.get(decl.name or "")
        if not expected_kind or expected_kind == OPEN_CONJECTURE_TARGET_KIND:
            continue
        if _is_phase1_structural_target_alias(
            decl,
            expected_kind,
            canonical.parsed,
            owner_by_name,
            explicit_owners,
        ):
            continue
        malformed_prop_structure = _deferred_prop_structure(decl)
        if malformed_prop_structure is not None and not _is_theorem_like_kind(
            expected_kind
        ):
            decl.kind = "def"
            decl.text = malformed_prop_structure
            if decl.name:
                changed.append(decl.name)
            continue
        ordinary_definition = (
            not _is_theorem_like_kind(expected_kind)
            and decl.kind in {"def", "abbrev"}
        )
        theorem = (
            _is_theorem_like_kind(expected_kind)
            and decl.kind in {"theorem", "lemma"}
        )
        if not (ordinary_definition or theorem):
            continue
        # This is already the exact Phase-1 representation.  In particular,
        # preserve any unparenthesized `let`/`letI := ...` assignments in the
        # result type instead of mistaking the first one for the target body.
        if _has_terminal_sorry(decl.text):
            continue
        boundary = _top_level_assignment_index(decl.text)
        if boundary is None:
            continue
        deferred = decl.text[:boundary].rstrip() + " := sorry"
        if deferred != decl.text.rstrip():
            decl.text = deferred
            if decl.name:
                changed.append(decl.name)
    if changed and hasattr(ctx, "telemetry"):
        _record(
            ctx.telemetry,
            "phase1_model_body_deferred",
            labels=label_list,
            declarations=changed,
            count=len(changed),
        )
    return canonical


def _may_defer_target_body(decl: DeclBlock, expected_kind: str | None) -> bool:
    """Whether Phase 1 may leave this target's implementation for Phase 2."""
    if not expected_kind or not _has_terminal_sorry(decl.text):
        return False
    if expected_kind == OPEN_CONJECTURE_TARGET_KIND:
        return False
    if _is_theorem_like_kind(expected_kind):
        return decl.kind in {"theorem", "lemma"}
    return decl.kind in {"def", "abbrev"}


def _is_phase1_structural_target_alias(
    decl: DeclBlock,
    expected_kind: str | None,
    parsed: ParsedModule,
    owner_by_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None,
) -> bool:
    """Whether a completed target body is only a transparent type interface.

    Phase 1 normally defers every target ``def`` body. A type-valued blueprint
    definition is different when its mathematical contract is a plan-owned
    structure/class/inductive: ``def target : Type := OwnedInterface`` merely
    gives that complete interface its canonical blueprint name. It contains no
    executable implementation for Phase 2 to fill.

    Keep this exception deliberately narrow. The right-hand side must be a
    direct application of one structural helper owned by the same blueprint
    node; arbitrary completed definitions remain forbidden.
    """
    if (
        not expected_kind
        or _is_theorem_like_kind(expected_kind)
        or decl.kind not in {"def", "abbrev"}
        or _has_terminal_sorry(decl.text)
        or ":=" not in decl.text
    ):
        return False
    result_type = _planned_target_result_type(decl.text, decl.name or "")
    explicit_type_alias = bool(
        re.match(r"^(?:Type(?:\s+[A-Za-z0-9_'.]+)?|Sort\s+\S+)$", result_type)
    )
    # Lean permits an ``abbrev`` to infer its result sort from the right-hand
    # side.  When that side is the direct application of a same-node owned
    # structure/class/inductive, the alias is still only the public type
    # interface.  Requiring a redundant ``: Type`` here made the shared Phase-1
    # body deferrer replace a valid alias by ``sorry`` and erase the interface
    # immediately before semantic audit.  Ordinary ``def`` bodies still need
    # the explicit type-valued declaration and remain deferred otherwise.
    inferred_abbrev_alias = decl.kind == "abbrev" and not result_type
    if not (explicit_type_alias or inferred_abbrev_alias):
        return False

    owner = owner_by_name.get(decl.name or "")
    if not owner:
        return False
    helper_kinds = {
        helper.name: helper.kind
        for helper in parsed.decls
        if helper.name and helper.kind in {"structure", "class", "inductive"}
    }
    owned_helpers = [
        name
        for name, helper_owner in (explicit_owner_by_name or {}).items()
        if helper_owner == owner and name in helper_kinds
    ]
    rhs = decl.text.split(":=", 1)[1].strip()
    for helper in owned_helpers:
        simple_application = re.fullmatch(
            rf"@?{re.escape(helper)}"
            r"(?:\s+(?:[A-Za-z_][A-Za-z0-9_'.]*|\([^()\n]*\)|\{[^{}\n]*\}))*",
            rhs,
        )
        if simple_application:
            return True
    return False


def _splice_proof(decl_text: str, proof: str) -> str:
    """Replace a terminal ``:= sorry`` with a tactic body; header untouched."""
    base = _TERMINAL_SORRY_RE.sub("", decl_text.rstrip()).rstrip()
    if base.endswith(":="):
        base = base[: -len(":=")].rstrip()
    return f"{base} := {proof.strip()}"


def _extract_by_proof(model_decl_text: str) -> str | None:
    """Pull the ``by ...`` proof out of a model-returned declaration.

    Only the proof is ever used; the frozen statement in our module is the one
    that gets compiled, so a model that silently reshapes the statement cannot
    smuggle the change in.
    """
    match = re.search(r":=\s*(by\b[\s\S]*)", model_decl_text)
    if match is None:
        return None
    proof = match.group(1).strip()
    return proof or None
