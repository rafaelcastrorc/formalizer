"""Deterministic skeleton audit and the model-driven blueprint-alignment audit.

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


def _skeleton_code_findings(
    code: str,
    target_kinds: dict[str, str],
    label_by_lean_name: dict[str, str],
    explicit_owner_by_name: dict[str, str] | None = None,
    *,
    allow_deferred_bodies: bool = True,
) -> list[SkeletonFinding]:
    """Correctness audit variant for the skeleton phase.

    Like ``_audit_lean_code`` but ``sorry`` is legal exactly as a target's
    terminal deferred body: theorem proofs and typed ``def``/``abbrev`` bodies
    are implemented in Phase 2. Helpers, structures, preamble, and interior
    declaration positions must remain sorry-free.
    """
    findings: list[SkeletonFinding] = []

    parsed = _parse_module(code)
    owner_by_index = _declaration_owner_map(
        parsed, label_by_lean_name, explicit_owner_by_name
    )
    owner_by_name = {
        decl.name: owner_by_index[index]
        for index, decl in enumerate(parsed.decls)
        if decl.name and index in owner_by_index
    }
    target_names = set(target_kinds)
    planned_helper_names = set((explicit_owner_by_name or {}).keys())

    def decl_finding(
        name: str | None, message: str, *, category: str = ""
    ) -> SkeletonFinding:
        return SkeletonFinding(
            message=message,
            label=owner_by_name.get(name or ""),
            lean_name=name,
            category=category,
        )

    if re.search(r"\badmit\b|by\s*\?", code):
        findings.append(SkeletonFinding("contains a forbidden placeholder (`admit` or `by ?`)"))
    if "set_option autoImplicit true" in code:
        findings.append(SkeletonFinding("enables `autoImplicit`"))
    bad = [f"{kind} {name}" for kind, name in FORBIDDEN_ASSUMPTIONS.findall(code)]
    if bad:
        findings.append(
            SkeletonFinding(
                f"uses top-level assumptions instead of implementations: {', '.join(bad[:12])}"
            )
        )
    invented = sorted(set(FORBIDDEN_BLUEPRINT_STUBS.findall(code)))
    if invented:
        findings.append(
            SkeletonFinding(f"calls invented paper/blueprint helpers: {', '.join(invented[:12])}")
        )
    if _FORBIDDEN_TOPLEVEL_RE.search(code):
        findings.append(
            SkeletonFinding(
                "contains top-level `variable`/`namespace`/`section`/`example` commands; "
                "each declaration must be self-contained"
            )
        )
    # Comment-aware preamble lint. Lean block comments (`/- ... -/`, including
    # doc comments) span lines and nest; a continuation line of a multi-line
    # comment is comment TEXT, not a command. Flagging it produced an
    # unfixable false positive: the model's file was valid Lean, so identical
    # regens looped until the round budget was exhausted.
    comment_depth = 0
    for line in parsed.preamble:
        stripped = line.strip()
        inside_comment = comment_depth > 0
        if not inside_comment and not stripped.startswith("--"):
            if stripped and not stripped.startswith(
                ("open", "/-", "noncomputable section")
            ):
                findings.append(
                    SkeletonFinding(f"unexpected non-`open` preamble command: `{stripped[:80]}`")
                )
        # Track block-comment depth. `--` starts a line comment (its content
        # has no delimiter meaning) unless we are already inside a block
        # comment, where `--` is plain text and `-/` still closes.
        if inside_comment or not stripped.startswith("--"):
            comment_depth += stripped.count("/-") - stripped.count("-/")
            if comment_depth < 0:
                comment_depth = 0
    for decl in parsed.decls:
        expected_kind = target_kinds.get(decl.name or "")
        name = decl.name or ""
        if (
            name
            and name not in target_names
            and name not in planned_helper_names
        ):
            findings.append(
                decl_finding(
                    name,
                    f"Phase 1 emitted unplanned helper `{name}`. The outline may "
                    "contain only blueprint targets and exact plan-owned "
                    "structure/inductive/class interfaces; executable helper "
                    "definitions and theorems belong in Phase 2 or require a "
                    "blueprint contract change",
                    category="unplanned_phase1_helper",
                )
            )
        if expected_kind == OPEN_CONJECTURE_TARGET_KIND:
            if decl.kind not in {"def", "abbrev"}:
                findings.append(
                    decl_finding(
                        name,
                        f"recorded conjecture `{name}` must be an exact `def ... : Prop := ...`, "
                        "not a theorem or proof obligation",
                        category="wrong_kind",
                    )
                )
            elif _has_terminal_sorry(decl.text):
                findings.append(
                    decl_finding(
                        name,
                        f"recorded conjecture `{name}` must define its proposition without `sorry`",
                        category="recorded_conjecture_sorry",
                    )
                )
            elif not re.search(r":\s*Prop\s*:=", decl.text):
                findings.append(
                    decl_finding(
                        name,
                        f"recorded conjecture `{name}` must have proposition-valued result type `Prop`",
                        category="recorded_conjecture_not_prop",
                    )
                )
        if (
            allow_deferred_bodies
            and expected_kind
            and expected_kind != OPEN_CONJECTURE_TARGET_KIND
            and not _is_theorem_like_kind(expected_kind)
            and decl.kind in {"def", "abbrev"}
            and not _has_terminal_sorry(decl.text)
            and not _is_phase1_structural_target_alias(
                decl,
                expected_kind,
                parsed,
                owner_by_name,
                explicit_owner_by_name,
            )
        ):
            findings.append(
                decl_finding(
                    decl.name,
                    f"Phase 1 target `{decl.name}` must expose only its exact typed "
                    "interface and end in `:= sorry`; its implementation belongs in Phase 2",
                )
            )
        if "sorry" not in decl.text:
            continue
        if allow_deferred_bodies and _may_defer_target_body(decl, expected_kind):
            inner = _TERMINAL_SORRY_RE.sub("", decl.text)
            if re.search(r"\bsorry\b", inner):
                findings.append(
                    decl_finding(decl.name, f"`{decl.name}` uses sorry outside the terminal proof position")
                )
            continue
        findings.append(
            decl_finding(
                decl.name,
                (
                    f"`{decl.name or decl.kind}` contains `sorry`, but a Phase 2 "
                    "whole-node transaction must return a complete declaration"
                    if not allow_deferred_bodies
                    else f"`{decl.name or decl.kind}` contains sorry outside an allowed "
                    "terminal target body; helpers and structure declarations must be complete"
                ),
            )
        )
    for decl in parsed.decls:
        name = decl.name or ""
        # Blueprint labels own their canonical Lean names. A legitimate label
        # such as ``remark:geometric-recursion-gap`` must not become an
        # unfixable deterministic rejection merely because its required name
        # contains a placeholder-like word. Keep applying the heuristic to
        # every helper name, including helpers explicitly proposed by a plan.
        if name not in target_names and PLACEHOLDER_NAME_RE.search(name):
            findings.append(decl_finding(name, f"placeholder declaration name `{name}`"))
        if decl.kind in {"def", "abbrev"} and re.search(r":\s*Prop\s*:=\s*True\b", decl.text):
            findings.append(decl_finding(name, f"`{name}` defines a proposition as `True`"))
        if decl.kind in {"theorem", "lemma"} and re.search(r":\s*True\s*:=", decl.text):
            findings.append(decl_finding(name, f"`{name}` proves only `True`"))
    return findings


def _skeleton_code_issues(code: str, target_kinds: dict[str, str]) -> list[str]:
    return [finding.message for finding in _skeleton_code_findings(code, target_kinds, {})]


def _format_skeleton_findings(findings: list[SkeletonFinding]) -> str:
    lines: list[str] = []
    for finding in findings:
        prefix = ""
        if finding.label and finding.lean_name:
            prefix = f"{finding.label} / `{finding.lean_name}`: "
        elif finding.label:
            prefix = f"{finding.label}: "
        elif finding.lean_name:
            prefix = f"`{finding.lean_name}`: "
        lines.append(prefix + finding.message)
    if not lines:
        return ""
    return "Deterministic skeleton audit rejected the file:\n- " + "\n- ".join(lines)


def _skeleton_finding_class(message: str) -> str:
    """Stable, paper-independent class for deterministic skeleton routing."""
    if "missing generated declaration" in message:
        return "missing_decl"
    if "placeholder declaration name" in message:
        return "placeholder_name"
    if "outside the terminal proof position" in message:
        return "nonterminal_sorry"
    if "contains sorry but is not a theorem-like" in message:
        return "non_theorem_sorry"
    if "does not mention required dependency" in message:
        return "missing_dependency_mention"
    if "is a definition but generated" in message:
        return "wrong_kind"
    if "is theorem-like but generated" in message:
        return "wrong_kind"
    if "forbidden placeholder" in message:
        return "forbidden_placeholder"
    if "invented paper/blueprint helpers" in message:
        return "invented_helper"
    if "unexpected non-`open` preamble" in message or "top-level" in message:
        return "bad_file_shape"
    return "other"


def _skeleton_findings_fingerprint(
    findings: list[SkeletonFinding],
) -> tuple[tuple[str, str], ...]:
    """Deterministic stagnation key for Phase 1 audit failures.

    If this key is unchanged after a model patch, the model call did not move
    the section toward acceptance; route to a smaller/escalated attempt instead
    of repeating the same patch/regenerate cycle.
    """
    return tuple(
        sorted(
            (finding.label or "", obligation)
            for finding in findings
            for obligation in _finding_obligation_ids(finding)
        )
    )


def _dependency_closed_subset(ctx: Ctx, labels: list[str], targets: list[str]) -> list[str]:
    """Smallest original-order subset containing targets and same-section deps."""
    label_set = set(labels)
    needed: set[str] = set()

    def visit(label: str) -> None:
        if label in needed or label not in label_set:
            return
        needed.add(label)
        node = ctx.nodes.get(label)
        if node is None:
            return
        for dep in sorted(node.uses):
            if dep in label_set:
                visit(dep)

    for label in targets:
        visit(label)
    return [label for label in labels if label in needed]


# ---------------------------------------------------------------------------
# Alignment audit (skeleton-aware)


def _plan_owned_declaration_cycle_findings(
    code: str, ctx: Ctx, labels: Iterable[str]
) -> list[SkeletonFinding]:
    """Detect impossible owner/helper cycles in emitted Phase-1 declarations."""
    decls = _lean_declarations(code)
    entries = getattr(ctx, "design_plan_entries", {})
    findings: list[SkeletonFinding] = []
    for label in labels:
        target_name = _lean_name(label)
        if target_name not in decls:
            continue
        helper_names: list[str] = []
        for helper in (entries.get(label) or {}).get("helpers") or []:
            raw_name = str(helper.get("name") or "").strip()
            canonical = _owned_helper_name(ctx, raw_name, [label])
            emitted = canonical if canonical in decls else raw_name
            if emitted in decls:
                helper_names.append(emitted)
        local_names = [target_name, *helper_names]
        graph = {
            source: {
                target
                for target in local_names
                if target != source
                and _mentions_lean_symbol(decls[source].text, target)
            }
            for source in local_names
        }

        def reaches(source: str, target: str) -> bool:
            todo = list(graph.get(source, set()))
            seen: set[str] = set()
            while todo:
                current = todo.pop()
                if current == target:
                    return True
                if current in seen:
                    continue
                seen.add(current)
                todo.extend(graph.get(current, set()) - seen)
            return False

        cyclic_helpers = sorted(
            helper
            for helper in helper_names
            if reaches(target_name, helper) and reaches(helper, target_name)
        )
        if cyclic_helpers:
            findings.append(
                SkeletonFinding(
                    f"{label} interface plan creates an impossible declaration "
                    f"cycle between `{target_name}` and plan-owned helper(s): "
                    + ", ".join(f"`{name}`" for name in cyclic_helpers),
                    label=label,
                    lean_name=target_name,
                    category="plan_contract_closure",
                )
            )
    return findings


def _skeleton_deterministic_findings(code: str, ctx: Ctx, labels: list[str]) -> list[SkeletonFinding]:
    """Coverage/kind checks for a section. Dependency-mention checks are only
    applied to declarations whose bodies are already complete; deferred theorem
    proofs and def/abbrev bodies get theirs during Phase 2."""
    findings: list[SkeletonFinding] = []
    parsed_for_contract = _parse_module(code)
    decls = _lean_declarations(code)
    generated_by_name = {
        _lean_name(other_label): other_label
        for other_label, other_node in ctx.nodes.items()
        if not other_node.mathlibok
    }
    label_by_name = {_lean_name(label): label for label in labels}
    consumers_by_index = _declaration_target_consumers(
        parsed_for_contract,
        label_by_name,
        _planned_helper_owner_by_name(ctx, labels),
    )
    plan_entries = getattr(ctx, "design_plan_entries", {})
    for label in labels:
        entry = plan_entries.get(label) or {}
        if int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION:
            continue
        for helper in entry.get("helpers") or []:
            helper_name = str(helper.get("name") or "").strip()
            canonical_helper_name = _owned_helper_name(ctx, helper_name, [label])
            helper_decl = decls.get(helper_name) or decls.get(canonical_helper_name)
            if helper_name and helper_decl is None:
                findings.append(
                    SkeletonFinding(
                        f"{label} omitted helper `{helper_name}` required by its "
                        "accepted interface contract",
                        label=label,
                        lean_name=canonical_helper_name,
                    )
                )
                continue
            if helper_decl is None:
                continue
            expected_kind = str(helper.get("kind") or "").strip()
            actual_kind = helper_decl.kind
            kind_matches = expected_kind == actual_kind or {
                expected_kind, actual_kind
            } <= {"theorem", "lemma"}
            if expected_kind and not kind_matches:
                findings.append(
                    SkeletonFinding(
                        f"{label} helper `{helper_name}` must be a {expected_kind}, "
                        f"but generation emitted a {actual_kind}",
                        label=label,
                        lean_name=canonical_helper_name,
                    )
                )
            missing_members = [
                member
                for member in helper.get("required_members") or []
                if not re.search(
                    rf"(?<![A-Za-z0-9_'.]){re.escape(str(member))}"
                    rf"(?![A-Za-z0-9_'.])",
                    helper_decl.text,
                )
            ]
            if missing_members:
                findings.append(
                    SkeletonFinding(
                        f"{label} helper `{helper_name}` omits required member(s): "
                        + ", ".join(f"`{item}`" for item in missing_members),
                        label=label,
                        lean_name=canonical_helper_name,
                    )
                )
    for label in labels:
        node = ctx.nodes[label]
        if node.mathlibok:
            continue
        expected_kind = _phase1_target_kind(ctx, label)
        lean_name = _lean_name(label)
        decl = decls.get(_lean_name(label))
        if decl is None:
            findings.append(
                SkeletonFinding(
                    f"missing generated declaration for {label} -> `{lean_name}`",
                    label=label,
                    lean_name=lean_name,
                )
            )
            continue
        if expected_kind in DEFINITION_LIKE_KINDS and decl.kind in {"theorem", "lemma"}:
            findings.append(
                SkeletonFinding(
                    f"{label} is a definition but generated `{decl.kind} {decl.name}`",
                    label=label,
                    lean_name=lean_name,
                )
            )
        if _is_theorem_like_kind(expected_kind) and decl.kind not in {"theorem", "lemma"}:
            findings.append(
                SkeletonFinding(
                    f"{label} is theorem-like but generated `{decl.kind} {decl.name}`",
                    label=label,
                    lean_name=lean_name,
                    category="wrong_kind",
                )
            )
        elif (
            _is_theorem_like_kind(expected_kind)
            and _planned_target_result_type(decl.text, lean_name) == "Prop"
        ):
            findings.append(
                SkeletonFinding(
                    f"{label} is theorem-like but generated the bare proposition "
                    f"sort `{decl.kind} {decl.name} : Prop`; its public contract "
                    "must state the actual proposition proved by the blueprint",
                    label=label,
                    lean_name=lean_name,
                    category="wrong_kind",
                )
            )
        # A deferred Phase-1 declaration contains only its public type. Once a
        # body/proof is present, proof-scoped graph edges are authorized too.
        allowed_dependencies = (
            _transitive_statement_dependencies(ctx.nodes, label)
            if _has_terminal_sorry(decl.text) or _records_conjecture(ctx, label)
            else _transitive_dependencies(ctx.nodes, label)
        )
        # A target's public interface includes every local helper it consumes,
        # not only the canonical target declaration.  Inspect that complete
        # interface surface so a provider referenced inside a structure field
        # cannot evade the dependency-closure gate.
        interface_surface = "\n".join(
            parsed_for_contract.decls[index].text
            for index, consumers in consumers_by_index.items()
            if label in consumers
        ) or decl.text
        unexpected = sorted(
            other_label
            for lean_name, other_label in generated_by_name.items()
            if other_label != label
            and other_label not in allowed_dependencies
            and _mentions_lean_symbol(interface_surface, lean_name)
        )
        if unexpected:
            findings.append(
                SkeletonFinding(
                    f"{label} references generated declaration(s) outside its "
                    "blueprint dependency closure: "
                    + ", ".join(
                        f"{dep} -> `{_lean_name(dep)}`" for dep in unexpected[:12]
                    ),
                    label=label,
                    lean_name=lean_name,
                    category="outside_dependency_closure",
                    dependencies=tuple(unexpected),
                )
            )
        if not _has_terminal_sorry(decl.text):
            dependency_node = node
            if _records_conjecture(ctx, label):
                dependency_node = copy.copy(node)
                dependency_node.uses = _statement_uses(node)
            missing = _nonmathlib_uses_missing_from_decl(
                label, dependency_node, decl, ctx.nodes, decls
            )
            if missing:
                findings.append(
                    SkeletonFinding(
                        f"{label} does not mention required dependency generated name(s): "
                        + ", ".join(f"`{_lean_name(dep)}`" for dep in missing[:12]),
                        label=label,
                        lean_name=lean_name,
                    )
                )
    findings.extend(_plan_owned_declaration_cycle_findings(code, ctx, labels))

    # Candidate-derived contracts are an atomic result of this deterministic
    # transaction.  A rejected candidate must never rewrite the next patch's
    # authoritative target: doing so made a theorem-like ``def ... : Prop``
    # self-perpetuating even though the same pass rejected it immediately.
    if not findings and getattr(ctx, "semantic_plan_entries", {}):
        label_by_name_for_contract = {
            _lean_name(label): label for label in labels
        }
        owner_by_index = _declaration_owner_map(
            parsed_for_contract,
            label_by_name_for_contract,
            _planned_helper_owner_by_name(ctx, labels),
        )
        _realize_typed_contracts_from_candidate(
            ctx,
            labels,
            CanonicalModelModule(parsed_for_contract, owner_by_index),
        )
    _record_phase1_dependency_observations(ctx, findings, code)
    return findings


def _skeleton_deterministic_audit(code: str, ctx: Ctx, labels: list[str]) -> list[str]:
    return [finding.message for finding in _skeleton_deterministic_findings(code, ctx, labels)]


def _alignment_issue_failure_identity(
    issue: Mapping[str, Any],
    *,
    routed_kind: str,
    failure_origin: str,
    required_dependencies: Iterable[str],
    forbidden_dependencies: Iterable[str] = (),
) -> dict[str, Any]:
    """Build a provider-neutral identity from one critic's structured facts.

    The critic's explanatory ``reason`` is deliberately excluded.  If none of
    the required structured arrays contains a fact, return no identity so the
    evidence ledger conservatively falls back to exact normalized prose.
    """
    fact_fields = (
        "missing_plan_requirements",
        "interface_defects",
        "deferred_body_obligations",
        "missing_blueprint_information",
        "missing_helpers",
    )
    facts = {
        field: [
            str(item).strip()
            for item in issue.get(field) or []
            if str(item).strip()
        ]
        for field in fact_fields
    }
    dependencies = sorted(
        {str(item).strip() for item in required_dependencies if str(item).strip()}
    )
    forbidden = sorted(
        {str(item).strip() for item in forbidden_dependencies if str(item).strip()}
    )
    if not dependencies and not forbidden and not any(facts.values()):
        return {}
    return _canonical_failure_identity(
        {
            "source": "statement_alignment",
            "classification": str(issue.get("classification") or "").strip(),
            "routed_kind": routed_kind,
            "failure_origin": failure_origin,
            "required_dependencies": dependencies,
            "forbidden_dependencies": forbidden,
            **facts,
        }
    )


def _append_alignment_failure_identity(
    identities: dict[str, dict[str, Any]],
    label: str,
    identity: Mapping[str, Any],
) -> None:
    if not identity:
        return
    existing = identities.setdefault(label, {"issues": []})
    issues = list(existing.get("issues") or [])
    canonical = _canonical_failure_identity(dict(identity))
    encoded = json.dumps(canonical, sort_keys=True, separators=(",", ":"))
    if all(
        json.dumps(item, sort_keys=True, separators=(",", ":")) != encoded
        for item in issues
    ):
        issues.append(canonical)
    existing["issues"] = _canonical_failure_identity(issues)


def _model_alignment_audit(
    ctx: Ctx,
    labels: list[str],
    code: str,
    *,
    tag: str = "",
) -> AlignmentAuditResult | None:
    """Batched blueprint-contract audit. None means accepted.

    Rejections remain four-value iterable for existing callers. Structured
    statement-dependency evidence is available on ``required_dependencies``.
    Phase-1 issues also identify whether the rejected plan, emitted Lean, or
    both introduced the mismatch. ``kind`` remains ``blueprint``,
    ``decomposition``, or ``lean-generation`` for compatibility.
    """
    decls = _lean_declarations(code)
    parsed = _parse_module(code)
    label_by_name = {_lean_name(label): label for label in labels}
    consumers_by_index = _declaration_target_consumers(parsed, label_by_name)
    owned_material: dict[str, list[str]] = {label: [] for label in labels}
    for index, decl in enumerate(parsed.decls):
        for owner in consumers_by_index.get(index, set()):
            if owner in owned_material:
                owned_material[owner].append(decl.text)
    cache = getattr(ctx, "statement_audit_cache", None)
    if cache is None:
        cache = set()
        setattr(ctx, "statement_audit_cache", cache)

    def cache_key(label: str) -> str:
        decl = decls.get(_lean_name(label))
        material = {
            "label": label,
            "blueprint": ctx.tex_blocks.get(label, ""),
            # Origin routing compares blueprint, plan, and Lean. A plan change
            # must therefore invalidate a cached verdict even when the emitted
            # declaration has not changed yet.
            "design_plan": (getattr(ctx, "design_plan_entries", {}) or {}).get(
                label
            ),
            # Include local helpers owned by this target as well as the public
            # declaration. A compiler patch that changes a helper can change
            # the meaning of an otherwise byte-identical target statement and
            # must therefore invalidate the semantic verdict.
            "lean": "\n\n".join(owned_material.get(label) or [])
            or (decl.text if decl else "(missing)"),
            "paper": hashlib.sha256(ctx.paper_text.encode("utf-8")).hexdigest(),
        }
        return hashlib.sha256(
            json.dumps(material, sort_keys=True).encode("utf-8")
        ).hexdigest()

    keys = {label: cache_key(label) for label in labels}
    cached_labels = [label for label in labels if keys[label] in cache]
    audit_labels = [label for label in labels if keys[label] not in cache]
    if cached_labels:
        _log(
            f"  statement audit reused {len(cached_labels)} unchanged "
            "declaration verdict(s)"
        )
        _record(
            ctx.telemetry,
            "statement_audit_cache_hit",
            labels=cached_labels,
            count=len(cached_labels),
        )
    if not audit_labels:
        return None

    nodes = {label: ctx.nodes[label] for label in audit_labels}
    prompt = _statement_audit_prompt(
        ctx.name,
        nodes,
        ctx.tex_blocks,
        decls,
        ctx.paper_text,
        skeleton_phase=True,
        design_plan_entries={
            label: (getattr(ctx, "design_plan_entries", {}) or {}).get(label)
            for label in audit_labels
        },
    )
    recorded_conjectures = [
        label for label in audit_labels if _records_conjecture(ctx, label)
    ]
    if recorded_conjectures:
        prompt += (
            "\nConjecture-policy note: the following nodes are intentionally "
            "recorded as exact proposition-valued `def` declarations, not "
            "claimed as proved theorems: "
            + ", ".join(recorded_conjectures)
            + ". Audit whether each proposition exactly matches its blueprint "
            "claim. In wording such as 'it remains open whether P', the `def` "
            "must define P itself: defining a proposition does not assert or "
            "prove it. The open status is tracked separately by the pipeline "
            "and must not be encoded inside the proposition. Do not reject the "
            "positive proposition P merely because the blueprint says its truth "
            "is open; reject only when the defined P differs from the mathematical "
            "question in the blueprint.\n"
        )
    prompt += (
        "\nExisting blueprint labels available for `required_dependencies` "
        "(use only when the public statement truly requires one):\n"
        + "\n".join(
            f"- {label} ({node.kind})"
            for label, node in sorted(
                ctx.nodes.items(), key=lambda item: (item[1].file, item[1].line, item[0])
            )
        )
        + "\n"
    )
    # Judge independence: the audit NEVER shares a session with the generator
    # or with its own earlier verdicts (no `sessions` passed — each audit is a
    # fresh conversation seeing only the artifact and the blueprint). A judge
    # that resumes the producer's session inherits its self-justification
    # (rubber-stamp risk) or anchors on its own prior verdict instead of
    # re-reading the new file. Producers share sessions; judges must not.
    result = _call_model(
        ctx,
        prompt,
        purpose="statement_audit",
        timeout=ctx.base_timeout,
        effort=ctx.base_effort,
        labels=audit_labels,
        tag=tag,
    )
    if result.status != "ok" and len(audit_labels) == 1:
        # An unavailable auditor must not silently pass statements; retry once
        # via the escalation budget for a singleton. Multi-node audit failures
        # return to the shared scope router instead of repeating the whole call.
        result = _call_model(
            ctx,
            prompt,
            purpose="statement_audit",
            timeout=ctx.hard_timeout,
            effort=ctx.escalation_effort,
            labels=audit_labels,
            escalated=True,
            tag=tag,
        )
    if result.status != "ok":
        return AlignmentAuditResult(
            "lean-generation",
            f"blueprint contract audit call failed: {result.error}",
            set(audit_labels),
            [],
        )
    try:
        payload = _extract_json(result.text)
    except ValueError as exc:
        return AlignmentAuditResult(
            "lean-generation",
            f"blueprint contract audit returned invalid JSON: {exc}",
            set(audit_labels),
            [],
        )
    issues = payload.get("issues") or []
    deferred_body_obligations: dict[str, list[str]] = {}
    effective_issues: list[object] = []
    deferred_rejections: set[str] = set()
    for raw_issue in issues if isinstance(issues, list) else []:
        if not isinstance(raw_issue, dict):
            effective_issues.append(raw_issue)
            continue
        issue = dict(raw_issue)
        label = str(issue.get("node") or "")
        decl = decls.get(_lean_name(label))
        node = nodes.get(label)
        is_deferred_definition = bool(
            node is not None
            and node.kind in DEFINITION_LIKE_KINDS
            and decl is not None
            and decl.kind in {"def", "abbrev"}
            and _has_terminal_sorry(decl.text)
        )
        interface_defects = issue.get("interface_defects")
        obligations = [
            str(item).strip()
            for item in issue.get("deferred_body_obligations") or []
            if str(item).strip()
        ]
        if (
            is_deferred_definition
            and str(issue.get("severity", "reject")).lower() == "reject"
            and isinstance(interface_defects, list)
            and not any(str(item).strip() for item in interface_defects)
            and obligations
            and not any(
                str(item).strip()
                for key in (
                    "missing_blueprint_information",
                    "required_dependencies",
                    "forbidden_dependencies",
                    "missing_helpers",
                )
                for item in issue.get(key) or []
            )
        ):
            # Phase 1 owns only the public header of a deferred definition.
            # A critic may record missing body semantics, but that evidence
            # cannot turn implementation work into a different result type.
            issue["severity"] = "defer"
            deferred_rejections.add(label)
        if is_deferred_definition and obligations:
            deferred_body_obligations.setdefault(label, []).extend(obligations)
        effective_issues.append(issue)
    issues = effective_issues
    blocking_rejection = any(
        str(issue.get("severity", "")).lower() == "reject"
        for issue in issues
        if isinstance(issue, dict)
    )
    accepted = not blocking_rejection and (
        bool(payload.get("accepted")) or bool(deferred_rejections)
    )
    _record(
        ctx.telemetry,
        "statement_audit",
        labels=audit_labels,
        source="model",
        accepted=accepted,
        classification=str(payload.get("classification") or ""),
        deferred_body_obligations={
            label: list(dict.fromkeys(values))
            for label, values in sorted(deferred_body_obligations.items())
        },
    )
    if accepted:
        cache.update(keys[label] for label in audit_labels)
        return None
    formatted: list[str] = []
    rejected: set[str] = set()
    required_dependencies: dict[str, set[str]] = {}
    forbidden_dependencies: dict[str, set[str]] = {}
    kinds_by_label: dict[str, str] = {}
    helpers_by_label: dict[str, list[str]] = {}
    reasons_by_label: dict[str, str] = {}
    missing_info_by_label: dict[str, list[str]] = {}
    origins_by_label: dict[str, str] = {}
    plan_requirements_by_label: dict[str, list[str]] = {}
    failure_identities_by_label: dict[str, dict[str, Any]] = {}
    global_classification = str(payload.get("classification") or "")
    for issue in issues if isinstance(issues, list) else []:
        if not isinstance(issue, dict):
            continue
        node = str(issue.get("node") or "(unknown)")
        issue_line = (
            f"{node} [{issue.get('severity', 'reject')}]: "
            f"{issue.get('reason', '')}"
        )
        formatted.append(issue_line)
        if str(issue.get("severity", "reject")).lower() == "reject" and node in nodes:
            rejected.add(node)
            issue_classification = str(
                issue.get("classification") or global_classification
            )
            if issue_classification == "needs_decomposition":
                issue_kind = "decomposition"
                missing_info: list[str] = []
            else:
                issue_kind, missing_info = _authorized_alignment_failure_kind(
                    issue_classification, [issue_line], [issue]
                )
            # The structured issue classification is authoritative. In
            # particular, prose such as "erases the concrete terms" still
            # describes a translation/plan defect when the critic explicitly
            # reports ``lean_translation_issue`` and names existing blueprint
            # dependencies. Required dependency edges and plan defects have
            # their own deterministic routes below; free-text keywords must not
            # authorize blueprint decomposition.
            # More specific blueprint/decomposition evidence must not be lost
            # when a critic reports several findings for the same node.
            priority = {"lean-generation": 0, "decomposition": 1, "blueprint": 2}
            if priority.get(issue_kind, 0) >= priority.get(
                kinds_by_label.get(node, "lean-generation"), 0
            ):
                kinds_by_label[node] = issue_kind
            reasons_by_label.setdefault(node, issue_line)
            missing_info_by_label.setdefault(node, []).extend(missing_info)
            raw_origin = str(issue.get("failure_origin") or "lean").strip().lower()
            plan_requirements = [
                str(item).strip()
                for item in issue.get("missing_plan_requirements") or []
                if str(item).strip()
            ]
            # Plan routing is useful only for ordinary translation failures and
            # only when the independent critic names concrete blueprint content
            # absent from the plan. Unsupported labels fall back to the existing
            # Lean retry lifecycle rather than trusting a bare model category.
            origin = (
                raw_origin
                if issue_kind == "lean-generation"
                and raw_origin in {"plan", "both"}
                and plan_requirements
                else "lean"
            )
            origin_priority = {"lean": 0, "plan": 1, "both": 2}
            if origin_priority[origin] >= origin_priority.get(
                origins_by_label.get(node, "lean"), 0
            ):
                origins_by_label[node] = origin
            if origin in {"plan", "both"}:
                plan_requirements_by_label.setdefault(node, []).extend(
                    plan_requirements
                )
            helpers_by_label.setdefault(node, []).extend(
                str(helper).strip()
                for helper in issue.get("missing_helpers") or []
                if str(helper).strip()
            )
            requested_dependencies = {
                str(dep).strip()
                for dep in issue.get("required_dependencies") or []
                if str(dep).strip() in ctx.nodes and str(dep).strip() != node
            }
            forbidden = {
                str(dep).strip()
                for dep in issue.get("forbidden_dependencies") or []
                if str(dep).strip() in ctx.nodes and str(dep).strip() != node
            }
            contradictory = requested_dependencies & forbidden
            certified = requested_dependencies - contradictory
            if certified:
                required_dependencies[node] = certified
            if forbidden:
                forbidden_dependencies[node] = forbidden
                removal = (
                    "Remove generated public references to blueprint dependencies "
                    "that this node does not require: "
                    + ", ".join(sorted(forbidden))
                    + "."
                )
                reasons_by_label[node] = reasons_by_label[node] + "\n" + removal
                formatted.append(f"{node} [dependency-removal]: {removal}")
            if contradictory:
                conflict = (
                    "The audit returned contradictory add/remove dependency actions "
                    "for: "
                    + ", ".join(sorted(contradictory))
                    + "; no dependency edge was added for those labels."
                )
                reasons_by_label[node] = reasons_by_label[node] + "\n" + conflict
                formatted.append(f"{node} [audit-schema-conflict]: {conflict}")
            _append_alignment_failure_identity(
                failure_identities_by_label,
                node,
                _alignment_issue_failure_identity(
                    issue,
                    routed_kind=issue_kind,
                    failure_origin=origin,
                    required_dependencies=certified,
                    forbidden_dependencies=forbidden,
                ),
            )
    if not rejected:
        rejected = set(audit_labels)
        for label in rejected:
            kinds_by_label[label] = "lean-generation"
            origins_by_label[label] = "lean"
            reasons_by_label[label] = (
                "The critic rejected the declaration without attributable "
                "per-node routing evidence."
            )
    # The critic reports issues per node. Non-rejected nodes in the same
    # response have received a positive judgment and remain reusable even if a
    # sibling is routed to correction or blueprint repair.
    cache.update(keys[label] for label in audit_labels if label not in rejected)
    classification = global_classification
    routed_kinds = set(kinds_by_label.values())
    kind = next(iter(routed_kinds)) if len(routed_kinds) == 1 else "mixed"
    missing_blueprint_information = list(
        dict.fromkeys(
            item
            for label in sorted(rejected)
            for item in missing_info_by_label.get(label, [])
        )
    )
    _record(
        ctx.telemetry,
        "statement_audit_routing",
        labels=sorted(rejected),
        reported_classification=classification,
        routed_kind=kind,
        routed_kinds={
            label: kinds_by_label.get(label, "lean-generation")
            for label in sorted(rejected)
        },
        blueprint_repair_authorized=any(
            value in {"blueprint", "decomposition"}
            for value in kinds_by_label.values()
        ),
        missing_blueprint_information=missing_blueprint_information,
        required_dependencies={
            label: sorted(dependencies)
            for label, dependencies in required_dependencies.items()
        },
        forbidden_dependencies={
            label: sorted(dependencies)
            for label, dependencies in forbidden_dependencies.items()
        },
        failure_origins={
            label: origins_by_label.get(label, "lean")
            for label in sorted(rejected)
        },
        missing_plan_requirements={
            label: list(dict.fromkeys(requirements))
            for label, requirements in sorted(plan_requirements_by_label.items())
        },
    )
    decomposition_helpers = list(
        dict.fromkeys(
            helper
            for label in sorted(rejected)
            if kinds_by_label.get(label) == "decomposition"
            for helper in helpers_by_label.get(label, [])
        )
    )
    reason = "Blueprint contract audit rejected:\n- " + "\n- ".join(formatted)
    if required_dependencies:
        reason += "\nRequired existing blueprint statement dependencies:\n- " + "\n- ".join(
            f"{label} -> {', '.join(sorted(dependencies))}"
            for label, dependencies in sorted(required_dependencies.items())
        )
    if kind == "lean-generation" and classification == "blueprint_issue":
        reason += (
            "\nBlueprint repair was not authorized because the audit named no "
            "mathematical information absent from the blueprint."
        )
    decomposition_labels = {
        label for label, routed in kinds_by_label.items()
        if routed == "decomposition"
    }
    if decomposition_labels:
        if not decomposition_helpers:
            decomposition_helpers = [
                "split each decomposition-routed node's bundled declaration-level obligations "
                "into explicit helper nodes without weakening or dropping any claim"
            ]
        reason += "\nMissing helper statements:\n- " + "\n- ".join(
            dict.fromkeys(decomposition_helpers)
        )
    return AlignmentAuditResult(
        kind=kind,
        reason=reason,
        rejected=rejected,
        helpers=list(dict.fromkeys(decomposition_helpers)),
        required_dependencies=required_dependencies,
        kinds_by_label=kinds_by_label,
        helpers_by_label={
            label: list(dict.fromkeys(values))
            for label, values in helpers_by_label.items()
        },
        reasons_by_label=reasons_by_label,
        origins_by_label=origins_by_label,
        plan_requirements_by_label={
            label: list(dict.fromkeys(values))
            for label, values in plan_requirements_by_label.items()
        },
        failure_identities_by_label=failure_identities_by_label,
        forbidden_dependencies=forbidden_dependencies,
    )
