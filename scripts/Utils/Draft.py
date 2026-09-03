"""Blueprint draft lifecycle, conjecture policy predicates, and the scoped TeX repair writer.

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


def _is_conjecture_node(label: str, node: Node | None) -> bool:
    """Recognize declared conjectures and explicitly open mathematical claims."""
    return bool(node) and (
        str(getattr(node, "kind", "")).strip().lower() == "conjecture"
        or label.startswith("conj:")
        or bool(getattr(node, "open_claim", False))
    )


def _records_conjecture(ctx: Ctx, label: str) -> bool:
    return (
        getattr(ctx, "conjecture_policy", "record") == "record"
        and _is_conjecture_node(label, ctx.nodes.get(label))
    )


def _phase1_target_kind(ctx: Ctx, label: str) -> str:
    if _records_conjecture(ctx, label):
        return OPEN_CONJECTURE_TARGET_KIND
    return ctx.nodes[label].kind


def _phase1_target_kinds(ctx: Ctx, labels: Iterable[str]) -> dict[str, str]:
    return {_lean_name(label): _phase1_target_kind(ctx, label) for label in labels}


def _blueprint_block_has_proof(block: str) -> bool:
    match = re.search(
        r"\\begin\{proof\}([\s\S]*?)\\end\{proof\}", block, flags=re.IGNORECASE
    )
    if not match:
        return False
    proof = re.sub(r"%[^\n]*", "", match.group(1)).strip()
    return bool(proof)


def _blueprint_node_has_proof(ctx: Ctx, label: str) -> bool:
    tex_blocks = getattr(ctx, "tex_blocks", None)
    if not isinstance(tex_blocks, Mapping):
        tex_blocks = getattr(ctx, "stmt_blocks", {})
    return _blueprint_block_has_proof(str(tex_blocks.get(label, "")))


def _canonical_blueprint_dir(name: str) -> Path:
    return REPO_ROOT / "blueprints" / name


def _draft_blueprint_dir(name: str) -> Path:
    return SCRATCH_DIR / name / "blueprint-draft"


def _prepare_blueprint_draft(name: str, *, continue_run: bool) -> Path:
    """Create or resume the unpublished blueprint working tree."""
    canonical = _canonical_blueprint_dir(name)
    if not canonical.is_dir():
        raise FileNotFoundError(f"blueprints/{name} does not exist")
    draft = _draft_blueprint_dir(name)
    if continue_run and (draft / "blueprint" / "src" / "content.tex").is_file():
        _log(f"==> Continuing from unpublished blueprint draft: {draft.relative_to(REPO_ROOT)}")
        return draft
    if draft.exists():
        shutil.rmtree(draft)
    draft.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(canonical, draft)
    _log(f"==> Created unpublished blueprint draft: {draft.relative_to(REPO_ROOT)}")
    return draft


def _validate_draft(ctx: Ctx):
    return validate_blueprint(REPO_ROOT, ctx.name, blueprint_dir=ctx.blueprint_dir)


def _read_blueprint_source_at(name: str, blueprint_dir: Path) -> str:
    content = blueprint_dir / "blueprint" / "src" / "content.tex"
    parts = [
        f"% FILE: {content.relative_to(REPO_ROOT)}\n"
        + content.read_text(encoding="utf-8")
    ]
    common = blueprint_dir / "blueprint" / "src" / "macros" / "common.tex"
    if common.is_file():
        parts.append(
            f"% FILE: {common.relative_to(REPO_ROOT)}\n"
            + common.read_text(encoding="utf-8")
        )
    return "\n\n".join(parts)


def _read_draft_blueprint_source(ctx: Ctx) -> str:
    return _read_blueprint_source_at(ctx.name, ctx.blueprint_dir)


def _write_api_refinement_to(path: Path, text: str) -> None:
    payload = _extract_json(text)
    content_tex = str(payload.get("content_tex") or "").strip()
    if not content_tex:
        raise ValueError("refinement JSON did not include non-empty content_tex")
    if r"\begin{document}" in content_tex or r"\end{document}" in content_tex:
        raise ValueError("content_tex must not include a document environment")
    path.write_text(content_tex.rstrip() + "\n", encoding="utf-8")
    notes = str(payload.get("notes") or "").strip()
    if notes:
        print(f"  refinement notes: {notes}")


def _scoped_blueprint_repair_content(
    original_content: str,
    response_text: str,
    *,
    requested_labels: Iterable[str],
    existing_blocks: Mapping[str, str],
    existing_labels: Iterable[str],
) -> tuple[str, dict[str, Any]]:
    """Apply model-returned node replacements without granting file scope.

    Every requested target must be returned as one complete TeX node (including
    its following proof, when present). A replacement may prepend brand-new
    helper nodes, but it cannot contain or edit any other pre-existing label.
    The transformation is computed against the immutable pre-call source so a
    model backend has no way to smuggle unrelated draft edits into the result.
    """
    payload, repaired_backslashes = _extract_json_object_with_key(
        response_text, "replacements"
    )
    raw_replacements = payload.get("replacements")
    if not isinstance(raw_replacements, Mapping):
        raise ValueError("repair JSON did not include a replacements object")

    requested = list(dict.fromkeys(str(label).strip() for label in requested_labels))
    requested_set = {label for label in requested if label}
    replacements: dict[str, str] = {}
    for label, chunk in raw_replacements.items():
        normalized_label = str(label).strip()
        if not normalized_label:
            continue
        if not isinstance(chunk, str):
            raise ValueError(
                f"replacement for {normalized_label} must be a TeX string"
            )
        replacements[normalized_label] = chunk.strip()
    missing = requested_set - set(replacements)
    unexpected = set(replacements) - requested_set
    if missing or unexpected:
        details: list[str] = []
        if missing:
            details.append("missing target(s): " + ", ".join(sorted(missing)))
        if unexpected:
            details.append("unauthorized target(s): " + ", ".join(sorted(unexpected)))
        raise ValueError("scoped repair target mismatch (" + "; ".join(details) + ")")
    if not requested_set:
        raise ValueError("scoped repair requested no blueprint targets")

    existing = {str(label) for label in existing_labels}
    new_label_owner: dict[str, str] = {}
    spans: list[tuple[int, int, str, str]] = []
    for target in requested:
        old_block = str(existing_blocks.get(target) or "")
        if not old_block:
            raise ValueError(f"cannot locate complete existing TeX block for {target}")
        if original_content.count(old_block) != 1:
            raise ValueError(
                f"existing TeX block for {target} is not uniquely locatable"
            )

        replacement = replacements[target]
        if not replacement:
            raise ValueError(f"replacement for {target} is empty")
        if r"\begin{document}" in replacement or r"\end{document}" in replacement:
            raise ValueError(f"replacement for {target} contains a document environment")

        chunk_labels = _TEX_LABEL_RE.findall(replacement)
        counts = {label: chunk_labels.count(label) for label in set(chunk_labels)}
        repeated = sorted(label for label, count in counts.items() if count != 1)
        if repeated:
            raise ValueError(
                f"replacement for {target} repeats label(s): "
                + ", ".join(repeated)
            )
        if counts.get(target) != 1:
            raise ValueError(
                f"replacement for {target} must contain exactly one \\label{{{target}}}"
            )
        foreign_existing = (set(chunk_labels) & existing) - {target}
        if foreign_existing:
            raise ValueError(
                f"replacement for {target} contains pre-existing non-target label(s): "
                + ", ".join(sorted(foreign_existing))
            )
        for helper in set(chunk_labels) - existing:
            owner = new_label_owner.get(helper)
            if owner is not None and owner != target:
                raise ValueError(
                    f"new helper label {helper} is returned by both {owner} and {target}"
                )
            new_label_owner[helper] = target

        start = original_content.index(old_block)
        spans.append((start, start + len(old_block), target, replacement))

    spans.sort()
    for previous, current in zip(spans, spans[1:]):
        if current[0] < previous[1]:
            raise ValueError(
                f"scoped repair blocks overlap: {previous[2]} and {current[2]}"
            )

    parts: list[str] = []
    cursor = 0
    for start, end, _target, replacement in spans:
        parts.append(original_content[cursor:start])
        parts.append(replacement)
        cursor = end
    parts.append(original_content[cursor:])
    updated = "".join(parts)
    if not updated.endswith("\n"):
        updated += "\n"
    return updated, {
        "replacement_labels": requested,
        "new_helper_labels": sorted(new_label_owner),
        "notes": str(payload.get("notes") or "").strip(),
        "repaired_json_backslashes": repaired_backslashes,
    }


def _write_scoped_blueprint_repair_to(
    path: Path,
    text: str,
    *,
    original_content: str,
    requested_labels: Iterable[str],
    existing_blocks: Mapping[str, str],
    existing_labels: Iterable[str],
) -> dict[str, Any]:
    """Validate and atomically write one provider-neutral scoped repair."""
    updated, metadata = _scoped_blueprint_repair_content(
        original_content,
        text,
        requested_labels=requested_labels,
        existing_blocks=existing_blocks,
        existing_labels=existing_labels,
    )
    replacement = path.with_name(f".{path.name}.auto-blueprint-scoped-repair")
    replacement.write_text(updated, encoding="utf-8")
    os.replace(replacement, path)
    notes = str(metadata.get("notes") or "")
    if notes:
        print(f"  refinement notes: {notes}")
    return metadata


def _promote_blueprint_draft(ctx: Ctx) -> Path:
    """Atomically publish the successful draft content into the blueprint."""
    destination = _canonical_blueprint_dir(ctx.name) / "blueprint" / "src" / "content.tex"
    replacement = destination.with_name(".content.tex.auto-blueprint-promote")
    replacement.write_bytes(ctx.content_path.read_bytes())
    os.replace(replacement, destination)
    _record(
        ctx.telemetry,
        "blueprint_draft_promoted",
        draft=str(ctx.content_path.relative_to(REPO_ROOT)),
        destination=str(destination.relative_to(REPO_ROOT)),
    )
    return destination
