"""Generated-section paths, compile fingerprints, olean cache, and object probes.

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


def _state_path(name: str) -> Path:
    return SCRATCH_DIR / name / "skeleton_state.json"


def _section_module(name: str, number: int) -> tuple[str, Path]:
    base = _module_safe_name(name)
    module = f"AutoBlueprint.Generated.{base}.Skeleton{number:02d}"
    path = REPO_ROOT / "AutoBlueprint" / "Generated" / base / f"Skeleton{number:02d}.lean"
    return module, path


def _lake_olean_path(path: Path) -> Path:
    source_rel = path.resolve().relative_to(REPO_ROOT)
    return (REPO_ROOT / ".lake" / "build" / "lib" / "lean" / source_rel).with_suffix(".olean")


def _lean_environment_fingerprint(lean_command: list[str]) -> str:
    digest = hashlib.sha256()
    digest.update(json.dumps(lean_command).encode("utf-8"))
    for relative in ("lean-toolchain", "lakefile.lean", "lake-manifest.json"):
        path = REPO_ROOT / relative
        digest.update(relative.encode("utf-8"))
        try:
            digest.update(path.read_bytes())
        except OSError:
            digest.update(b"<missing>")
    return digest.hexdigest()


def _section_exact_source_fingerprint(path: Path) -> str:
    """Hash the exact generated source persisted by the scheduler.

    This is deliberately different from the reusable-object fingerprint below:
    state restoration and final publication care about every source byte, while
    an imported Lean object cannot observe an opaque theorem proof body.
    """
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _section_object_source_fingerprint(path: Path) -> str:
    """Hash source that can affect this module's importable Lean object.

    Theorem and lemma proof bodies are opaque to importers, so only their exact
    headers participate. Definition-like bodies, structures, instances,
    imports, options, preamble commands, and all other declarations remain
    exact. If parsing fails, fall back to the complete source so reuse is
    conservative.
    """
    try:
        source = path.read_text(encoding="utf-8")
        parsed = _parse_module(source)
    except (OSError, UnicodeError, ValueError):
        try:
            return _section_exact_source_fingerprint(path)
        except OSError:
            return hashlib.sha256(b"<missing-source>").hexdigest()

    options = [
        line.strip()
        for line in source.splitlines()
        if line.strip().startswith("set_option ")
    ]
    declarations = []
    for decl in parsed.decls:
        text = (
            _phase1_target_interface_text(decl)
            if decl.kind in {"theorem", "lemma"}
            else decl.text.strip()
        )
        declarations.append(
            {"kind": decl.kind, "name": decl.name or "", "text": text}
        )
    canonical = {
        "imports": parsed.imports,
        "options": options,
        "preamble": parsed.preamble,
        "declarations": declarations,
    }
    return hashlib.sha256(
        json.dumps(canonical, sort_keys=True, ensure_ascii=False).encode("utf-8")
    ).hexdigest()


def _section_compile_fingerprint(
    sec: Section,
    lean_command: list[str],
    sections: Iterable[Section] = (),
) -> str:
    """Fingerprint inputs that can change one module's importable object.

    In particular, an opaque theorem proof edit does not invalidate this
    module or cascade through its importers. Statement edits and every
    definition-body edit still do.
    """
    digest = hashlib.sha256()
    digest.update(_lean_environment_fingerprint(lean_command).encode("ascii"))
    digest.update(_section_object_source_fingerprint(sec.path).encode("ascii"))
    by_module = {item.module: item for item in sections}
    for module in sorted(sec.import_modules):
        digest.update(module.encode("utf-8"))
        imported = by_module.get(module)
        if imported is not None:
            digest.update((imported.compile_fingerprint or "<unrecorded>").encode("ascii"))
    return _SECTION_OBJECT_FINGERPRINT_PREFIX + digest.hexdigest()


def _migrate_section_compile_fingerprints(
    sections: Iterable[Section], lean_command: list[str]
) -> int:
    """Upgrade pre-v2 object keys without rebuilding known-good objects.

    Saved state already verifies the exact source hash before reaching this
    migration. Phase 2 either retained an object after theorem-only work or
    rebuilt it after definition work, so recomputing the cache identity is
    sufficient and avoids a one-time full rebuild on ``--continue``.
    """
    section_list = list(sections)
    legacy = [
        sec
        for sec in section_list
        if sec.compile_fingerprint
        and not sec.compile_fingerprint.startswith(
            _SECTION_OBJECT_FINGERPRINT_PREFIX
        )
        and not sec.deferred
        and not sec.provisional_environment
        and _section_objects_exist(sec)
    ]
    if not legacy:
        return 0

    by_module = {sec.module: sec for sec in section_list}
    visited: set[str] = set()

    def visit(sec: Section) -> None:
        if sec.module in visited:
            return
        visited.add(sec.module)
        for module in sec.import_modules:
            imported = by_module.get(module)
            if imported is not None:
                visit(imported)
        if _section_objects_exist(sec):
            sec.compile_fingerprint = _section_compile_fingerprint(
                sec, lean_command, section_list
            )

    # Re-key the complete graph, not only legacy entries. A missing importer
    # object may have been rebuilt earlier in resume using an imported legacy
    # key; recomputing every surviving key topologically prevents that importer
    # from paying one unnecessary integration rebuild immediately afterward.
    for sec in section_list:
        visit(sec)
    return len(legacy)


def _section_objects_exist(sec: Section) -> bool:
    return sec.path.with_suffix(".olean").is_file() and _lake_olean_path(sec.path).is_file()


def _mark_section_compiled(
    sec: Section, lean_command: list[str], sections: Iterable[Section] = ()
) -> None:
    sec.compile_fingerprint = _section_compile_fingerprint(
        sec, lean_command, sections
    )


def _compile_section_olean(
    sec: Section, lean_command: list[str], sections: Iterable[Section] = ()
):
    attempt = _compile_module_olean(sec.path, lean_command)
    if attempt.ok:
        _mark_section_compiled(sec, lean_command, sections)
    else:
        sec.compile_fingerprint = ""
    return attempt


def _phase1_integration_gate_path(ctx: Ctx) -> Path:
    return SCRATCH_DIR / ctx.name / "phase1_integration_gate.lean"


def _generated_lake_module_dir(name: str) -> Path:
    return (
        REPO_ROOT
        / ".lake"
        / "build"
        / "lib"
        / "lean"
        / "AutoBlueprint"
        / "Generated"
        / _module_safe_name(name)
    )


def _discard_section_objects(path: Path) -> None:
    """Remove every compiled object for a generated source, retaining source."""
    with contextlib.suppress(OSError, ValueError):
        _lake_olean_path(path).unlink(missing_ok=True)
    with contextlib.suppress(OSError):
        path.with_suffix(".olean").unlink(missing_ok=True)


def _discard_section_artifacts(path: Path) -> None:
    """Remove the source and objects of a section that was NOT frozen.

    A section file is written before Lean checks it, so an abandoned attempt
    used to survive on disk. Later generation calls glob the generated
    directory, find that orphan, and `import` it — resolving the import
    against a stale `.olean` from an earlier run, which fails in ways that
    have nothing to do with the nodes being stated. Every abandoned section
    must leave the workspace exactly as it found it.
    """
    with contextlib.suppress(OSError):
        path.unlink(missing_ok=True)
    _discard_section_objects(path)


def _statement_surface_probe_code(
    module_code: str, target_names: set[str]
) -> tuple[str, list[str]]:
    """Replace only target implementation bodies by ``sorry`` for diagnosis.

    This is never accepted or persisted.  It answers one operational question
    after object generation times out: is the expensive part already present
    in the public statement/interface, or only in the completed Phase-2 body?
    Structures/classes/inductives are left intact because their fields *are*
    their public interface.
    """
    parsed = _parse_module(module_code)
    changed: list[str] = []
    for decl in parsed.decls:
        name = decl.name or ""
        if name not in target_names or decl.kind not in {
            "theorem",
            "lemma",
            "def",
            "abbrev",
            "instance",
        }:
            continue
        original = decl.text.rstrip()
        header = _TERMINAL_PROOF_RE.sub("", original).rstrip()
        if header == original:
            # The normal Phase-2 contract requires tactic bodies.  Keep the
            # diagnostic conservative when a term-style body cannot be split
            # without a Lean parser: do not claim that its statement was
            # independently measured.
            continue
        decl.text = header + " := sorry"
        changed.append(name)
    probe_code, _ranges = _compose_module(
        parsed.imports,
        parsed.preamble,
        [decl.text for decl in parsed.decls],
    )
    return probe_code, changed


def _run_statement_surface_object_probe(
    ctx: Ctx,
    module_code: str,
    labels: list[str],
) -> tuple[Any | None, list[str]]:
    """Compile a disposable statement-only control for a timed-out candidate."""
    probe_code, changed = _statement_surface_probe_code(
        module_code, {_lean_name(label) for label in labels}
    )
    if not changed:
        return None, []
    digest = hashlib.sha256(probe_code.encode("utf-8")).hexdigest()[:16]
    probe_dir = SCRATCH_DIR / ctx.name / "object-probes"
    probe_dir.mkdir(parents=True, exist_ok=True)
    probe_path = probe_dir / (
        f"StatementSurface-{digest}-{threading.get_ident()}-{time.time_ns()}.lean"
    )
    probe_path.write_text(probe_code, encoding="utf-8")
    try:
        attempt = _compile_module_olean(
            probe_path,
            ctx.lean_command,
            timeout=OBJECT_COMPILE_USABILITY_TIMEOUT,
        )
        return attempt, changed
    finally:
        _discard_section_artifacts(probe_path)


def _object_gate_evidence(
    ctx: Ctx,
    labels: list[str],
    module_code: str,
    object_attempt: Any,
    *,
    complete_bodies: bool,
) -> tuple[str, str]:
    """Classify an object-build failure without asking a model to guess.

    Returns ``(failure_class, evidence)``.  A completed Phase-2 node gets one
    statement-only control compile after a timeout.  Phase-1 candidates already
    contain deferred bodies, so their timed-out object is itself the control.
    """
    if getattr(object_attempt, "kind", "") != "object-timeout":
        return (
            "object_compile",
            "Lean object compilation rejected delivered statements:\n"
            + str(getattr(object_attempt, "output", ""))[-12000:],
        )

    timeout_s = OBJECT_COMPILE_USABILITY_TIMEOUT
    canonical_duration = float(getattr(object_attempt, "duration_s", timeout_s))
    if not complete_bodies:
        evidence = (
            f"{OBJECT_INTERFACE_FAILURE_PREFIX}:\n"
            f"- Plain Lean validation passed, but `lean -o` did not finish within "
            f"{timeout_s}s ({canonical_duration:.1f}s measured).\n"
            "- This candidate already contains deferred bodies, so changing a "
            "proof cannot fix the timeout.\n"
            "- Preserve the exact blueprint mathematics, but revise this node's "
            "Lean interface plan to use a bounded named representation (for "
            "example, a same-node structure with named fields) instead of deeply "
            "nested dependent products, repeated casts, or long projection chains.\n"
            "- This is an interface-plan correction, not authorization to edit or "
            "weaken the blueprint."
        )
        return "interface_usability", evidence

    probe_attempt, changed = _run_statement_surface_object_probe(
        ctx, module_code, labels
    )
    if probe_attempt is not None and getattr(probe_attempt, "ok", False):
        evidence = (
            f"{OBJECT_IMPLEMENTATION_FAILURE_PREFIX}:\n"
            f"- The complete node exceeded the {timeout_s}s object-build budget "
            f"({canonical_duration:.1f}s measured).\n"
            f"- A statement-only control for {', '.join(changed)} compiled in "
            f"{float(getattr(probe_attempt, 'duration_s', 0.0)):.1f}s.\n"
            "- Preserve the public statement and interface exactly. Simplify only "
            "the implementation/proof term so object generation remains bounded."
        )
        return "implementation_object", evidence
    if probe_attempt is not None and getattr(probe_attempt, "kind", "") == "object-timeout":
        probe_duration = float(getattr(probe_attempt, "duration_s", timeout_s))
        evidence = (
            f"{OBJECT_INTERFACE_FAILURE_PREFIX}:\n"
            f"- The complete node exceeded the {timeout_s}s object-build budget "
            f"({canonical_duration:.1f}s measured).\n"
            f"- Replacing only the target body by `sorry` still exceeded the same "
            f"budget ({probe_duration:.1f}s), so proof regeneration cannot fix it.\n"
            "- Preserve the exact blueprint statement and proof semantics, but "
            "refactor this node's Lean public representation using bounded named "
            "structures/fields or simpler equivalent indices instead of deeply "
            "nested dependent products, repeated casts, or projection chains.\n"
            "- Return the complete statement and body together; this is not "
            "authorization to edit or weaken the blueprint."
        )
        return "interface_usability", evidence

    diagnostic = (
        str(getattr(probe_attempt, "output", ""))[-4000:]
        if probe_attempt is not None
        else "The target body could not be separated conservatively for a control compile."
    )
    return (
        "object_compile",
        "Lean object compilation timed out, but the statement-only diagnostic "
        "was inconclusive. Preserve the exact blueprint statement and complete "
        "body while correcting the generated Lean module.\n\nDiagnostic:\n"
        + diagnostic,
    )


def _phase1_interface_usability_evidence(evidence: str) -> str:
    """Normalize Phase-1 elaboration-budget failures as interface evidence.

    Phase 1 mechanically replaces ordinary definition bodies and theorem
    proofs by ``sorry`` before Lean sees the candidate. A plain-check timeout
    or heartbeat exhaustion at that boundary therefore cannot be repaired by
    proving harder or by decomposing the blueprint: Lean is struggling with
    the public type/interface itself.
    """
    text = str(evidence or "").strip()
    if not text:
        return ""
    if text.startswith(OBJECT_INTERFACE_FAILURE_PREFIX):
        return text
    lowered = text.lower()
    markers = (
        "lean check timed out after",
        "maximum number of heartbeats has been reached",
        "maximum number of heartbeats",
        "(deterministic) timeout at",
        "deterministic timeout at",
    )
    if not any(marker in lowered for marker in markers):
        return ""
    return (
        f"{OBJECT_INTERFACE_FAILURE_PREFIX}:\n"
        "- Phase 1 had already replaced target implementations and proofs by "
        "`sorry`, so this failure is in elaborating the public Lean interface.\n"
        "- Preserve the exact blueprint mathematics. Replace deeply nested "
        "dependent products or projection chains by bounded same-node named "
        "structures/fields when needed. Do not add blueprint nodes merely to "
        "make Lean elaborate.\n"
        "- If no faithful bounded same-node representation exists, return the "
        "documented NEEDS-DECOMPOSITION result; compiler timeout evidence alone "
        "does not authorize blueprint decomposition.\n\n"
        "Exact Lean evidence:\n"
        + text[-10000:]
    )


def _phase1_interface_prompt_rule(feedback: str) -> str:
    """Prompt rule for one exact, diagnosed public-interface failure."""
    evidence = _phase1_interface_usability_evidence(feedback)
    if not evidence:
        return ""
    return """
Interface-usability correction for this exact statement version:
- The previous Phase-1 candidate already had every proof/ordinary body replaced
  by `sorry`; do not spend time proving anything.
- You MAY replace an anonymous/deep public type by one or more named structural
  declarations owned by the same target node, immediately before that target.
  Preserve every parameter, witness, equation, and mathematical obligation.
- These same-node structural declarations are Lean representation, not new
  blueprint lemmas. Do not invent a separate theorem or executable helper.
- Emit a complete bounded Lean interface now. Do not inspect files or run tools.
- If the blueprint genuinely requires a separate mathematical statement that
  cannot be represented inside this node, return NEEDS-DECOMPOSITION explicitly.
"""


def _compile_fast_candidate_object(
    ctx: Ctx,
    path: Path,
    module_code: str,
    labels: list[str],
    *,
    complete_bodies: bool,
) -> tuple[Any, str, str]:
    """Run the fast pipeline's bounded object gate and return exact evidence."""
    attempt = _compile_module_olean(
        path,
        ctx.lean_command,
        timeout=OBJECT_COMPILE_USABILITY_TIMEOUT,
    )
    _record(
        ctx.telemetry,
        "lean_object_compilation",
        labels=labels,
        owner_phase="phase2" if complete_bodies else "phase1",
        status="passed" if attempt.ok else getattr(attempt, "kind", "failed"),
        timeout_s=OBJECT_COMPILE_USABILITY_TIMEOUT,
        duration_s=float(getattr(attempt, "duration_s", 0.0)),
    )
    if attempt.ok:
        return attempt, "", ""
    failure_class, evidence = _object_gate_evidence(
        ctx,
        labels,
        module_code,
        attempt,
        complete_bodies=complete_bodies,
    )
    _record(
        ctx.telemetry,
        "lean_object_usability_gate",
        labels=labels,
        owner_phase="phase2" if complete_bodies else "phase1",
        classification=failure_class,
        evidence=evidence[-4000:],
    )
    return attempt, failure_class, evidence
