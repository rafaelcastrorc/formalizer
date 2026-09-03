"""Lean compilation, per-declaration error attribution, and import resolution.

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


def _errors_by_decl(
    output: str, file_name: str, ranges: list[tuple[int, int]]
) -> tuple[dict[int, list[str]], list[str]]:
    """Group Lean error messages by declaration index; extras are file-level."""
    records: list[tuple[int, str]] = []
    current: list[str] | None = None
    current_line = 0
    for line in output.splitlines():
        match = _LOC_RE.match(line)
        if match:
            if current is not None:
                records.append((current_line, "\n".join(current)))
            if match.group("sev") == "error" and file_name in match.group("path"):
                current = [line]
                current_line = int(match.group("line"))
            else:
                current = None
        elif current is not None:
            current.append(line)
    if current is not None:
        records.append((current_line, "\n".join(current)))

    by_decl: dict[int, list[str]] = {}
    file_level: list[str] = []
    for line_no, text in records:
        idx = next(
            (i for i, (start, end) in enumerate(ranges) if start <= line_no <= end), None
        )
        if idx is None:
            file_level.append(text)
        else:
            by_decl.setdefault(idx, []).append(text)
    return by_decl, file_level


def _lean_compile_findings(
    parsed: ParsedModule,
    owner_labels: list[str],
    ranges: list[tuple[int, int]],
    output: str,
    file_name: str,
    explicit_owner_by_name: dict[str, str] | None = None,
) -> list[SkeletonFinding]:
    """Turn Lean diagnostics into declaration-targeted skeleton findings."""
    by_decl, file_level = _errors_by_decl(output, file_name, ranges)
    label_by_name = {_lean_name(label): label for label in owner_labels}
    owner_by_index = _declaration_owner_map(
        parsed, label_by_name, explicit_owner_by_name
    )
    findings: list[SkeletonFinding] = []
    for index, messages in sorted(by_decl.items()):
        decl = parsed.decls[index] if index < len(parsed.decls) else None
        lean_name = decl.name if decl is not None else None
        label = owner_by_index.get(index)
        findings.append(
            SkeletonFinding(
                "Lean rejected this generated declaration:\n"
                + "\n".join(messages)[-6000:],
                label=label,
                lean_name=lean_name,
            )
        )
    findings.extend(
        SkeletonFinding("Lean file-level error:\n" + message[-6000:])
        for message in file_level
    )
    if not findings:
        findings.append(SkeletonFinding("Lean rejected the file:\n" + output[-6000:]))
    return findings


def _check_lean(path: Path, lean_command: list[str], *, timeout: int = LEAN_CHECK_TIMEOUT) -> tuple[bool, str]:
    """Compile a module, allowing sorry warnings (skeleton phase only)."""
    proc = subprocess.Popen(
        lean_command + [str(path)],
        cwd=str(REPO_ROOT),
        env=_lean_env(),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        start_new_session=True,
    )
    start = time.time()
    while True:
        try:
            stdout, stderr = proc.communicate(timeout=30)
            break
        except subprocess.TimeoutExpired:
            elapsed = int(time.time() - start)
            if elapsed >= timeout:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                stdout, stderr = proc.communicate()
                combined = "\n".join(p for p in (stdout or "", stderr or "") if p)
                return False, f"Lean check timed out after {timeout}s.\n{combined}"
    combined = "\n".join(p for p in (stdout or "", stderr or "") if p)
    if proc.returncode != 0:
        repaired_levels = _repair_unknown_universe_levels(path, combined)
        if repaired_levels:
            _log(
                "  deterministically declared missing Lean universe level(s): "
                + ", ".join(repaired_levels)
                + "; retrying the same compile"
            )
            return _check_lean(path, lean_command, timeout=timeout)
    return proc.returncode == 0, combined


def _lean_failure_may_be_fixed_by_broad_mathlib(output: str) -> bool:
    """Whether adding ``import Mathlib`` can plausibly change this failure.

    Broad-import diagnosis used to run after every failed candidate, including
    type mismatches, unfinished tactics, and heartbeat exhaustion. Those errors
    cannot be fixed by importing more declarations, so compiling the identical
    bad candidate a second time only adds latency. Keep the fallback for the
    missing-name class it was designed to diagnose.
    """
    return bool(_MISSING_LEAN_SURFACE_RE.search(output))


def _missing_lean_surface_names(output: str) -> list[str]:
    """Extract unresolved Lean names without treating other errors as imports."""
    return list(
        dict.fromkeys(
            match.group(1).rstrip("'\"`")
            for match in _MISSING_LEAN_NAME_RE.finditer(output)
        )
    )


def _specific_import_modules_for_missing_names(ctx: Ctx, output: str) -> list[str]:
    """Resolve missing declarations to local library modules deterministically.

    The complete ``Mathlib`` import remains a correctness-safe diagnostic, but
    persisting it makes every dependent generated module pay Mathlib's complete
    import cost. Search the already selected local libraries for declarations
    whose terminal name exactly matches each unresolved name. Returning an
    empty list means the resolution was ambiguous or incomplete, so the caller
    keeps the broad fallback instead of guessing.
    """
    missing = _missing_lean_surface_names(output)
    if not missing:
        return []
    terms = list(
        dict.fromkeys(
            term
            for name in missing
            for term in (name, name.rsplit(".", 1)[-1])
        )
    )
    roots = _library_roots(_blueprint_library_preference(ctx.name))
    candidates = _rg_library_candidates(
        roots,
        terms,
        max_candidates=max(40, len(terms) * 12),
    )
    modules: list[str] = []

    def import_module(candidate: Any) -> str:
        module = str(candidate.module)
        library = str(candidate.library)
        if module == library or module.startswith(library + "."):
            return module
        return f"{library}.{module}"

    for name in missing:
        terminal = name.rsplit(".", 1)[-1]
        matches = [
            import_module(candidate)
            for candidate in candidates
            if candidate.declaration == name
            or candidate.declaration == terminal
            or candidate.declaration.endswith("." + terminal)
        ]
        if not matches:
            return []
        modules.extend(matches)
    return list(dict.fromkeys(module for module in modules if module != "Mathlib"))
