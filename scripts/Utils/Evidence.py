"""Quarantine, local bisection, the diagnostic-evidence ledger, and generation feedback.

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


def _quarantine_labels(ctx: Ctx, labels: Iterable[str], failure_class: str) -> None:
    """Route exact failing statement versions as singletons.

    Quarantine is scheduling evidence, not a permanent property of a label.
    A later blueprint repair changes the statement fingerprint and
    ``refresh_nodes`` removes the stale entry automatically.
    """
    added: dict[str, dict[str, str]] = {}
    for label in labels:
        statement_fp = ctx.stmt_fps.get(label, "")
        if not statement_fp:
            continue
        previous = ctx.quarantine.get(label)
        ctx.quarantined_labels.add(label)
        if previous and previous.get("statement_fp") == statement_fp:
            # Preserve the first observed failure class for classifier data;
            # repeated symptoms for the same contract do not change routing.
            continue
        ctx.quarantine[label] = {
            "statement_fp": statement_fp,
            "failure_class": failure_class,
        }
        added[label] = dict(ctx.quarantine[label])
    telemetry = getattr(ctx, "telemetry", None)
    if added and telemetry is not None:
        _record(
            telemetry,
            "skeleton_quarantine_created",
            labels=sorted(added),
            records={label: added[label] for label in sorted(added)},
        )


def _release_quarantine(
    ctx: Ctx, labels: Iterable[str], *, reason: str = "statement_frozen"
) -> None:
    quarantine = getattr(ctx, "quarantine", {})
    quarantined_labels = getattr(ctx, "quarantined_labels", set())
    released: dict[str, dict[str, str]] = {}
    for label in labels:
        if label in quarantine:
            released[label] = dict(quarantine[label])
        quarantined_labels.discard(label)
        quarantine.pop(label, None)
    telemetry = getattr(ctx, "telemetry", None)
    if released and telemetry is not None:
        _record(
            telemetry,
            "skeleton_quarantine_released",
            labels=sorted(released),
            reason=reason,
            records={label: released[label] for label in sorted(released)},
        )


def _prune_stale_quarantine(ctx: Ctx) -> set[str]:
    """Drop routing evidence whose label or statement version has changed."""
    stale = {
        label
        for label in ctx.quarantined_labels
        if label not in ctx.nodes
        or ctx.quarantine.get(label, {}).get("statement_fp")
        != ctx.stmt_fps.get(label)
    }
    if stale:
        _release_quarantine(
            ctx, stale, reason="statement_fingerprint_changed"
        )
    return stale


def _release_local_group_partitions(
    ctx: Ctx, labels: Iterable[str], *, reason: str = "statement_frozen"
) -> None:
    """Release local bisection records involving any accepted/changed label."""
    partitions = getattr(ctx, "local_group_partitions", {})
    touched = set(labels)
    partition_ids = {
        str(entry.get("partition_id") or "")
        for label, entry in partitions.items()
        if label in touched or touched.intersection(entry.get("group") or [])
    }
    removed = {
        label: dict(entry)
        for label, entry in partitions.items()
        if str(entry.get("partition_id") or "") in partition_ids
    }
    for label in removed:
        partitions.pop(label, None)
    if removed and getattr(ctx, "telemetry", None) is not None:
        _record(
            ctx.telemetry,
            "phase1_local_partition_released",
            labels=sorted(removed),
            reason=reason,
        )


def _prune_stale_local_group_partitions(ctx: Ctx) -> set[str]:
    """Drop local bisections once any participating statement has changed."""
    partitions = getattr(ctx, "local_group_partitions", {})
    stale: set[str] = set()
    for label, entry in partitions.items():
        group_fps = entry.get("statement_fps") or {}
        if (
            label not in ctx.nodes
            or entry.get("statement_fp") != ctx.stmt_fps.get(label)
            or any(ctx.stmt_fps.get(item) != fp for item, fp in group_fps.items())
        ):
            stale.add(label)
    if stale:
        _release_local_group_partitions(
            ctx, stale, reason="statement_fingerprint_changed"
        )
    return stale


def _store_local_bisection(ctx: Ctx, route: FailureScopeDecision) -> None:
    """Persist one failure route without reducing unrelated batch capacity."""
    partitions = getattr(ctx, "local_group_partitions", None)
    if partitions is None:
        partitions = {}
        ctx.local_group_partitions = partitions
    _release_local_group_partitions(
        ctx, route.failed_labels, reason="local_bisection_replaced"
    )
    stored_parts: list[list[str]] = []
    for part_index, raw_part in enumerate(route.parts):
        part = [label for label in raw_part if label in ctx.stmt_fps]
        if not part:
            continue
        group_fps = {label: ctx.stmt_fps[label] for label in part}
        partition_id = hashlib.sha256(
            json.dumps(group_fps, sort_keys=True).encode("utf-8")
        ).hexdigest()
        for label in part:
            partitions[label] = {
                "partition_id": f"{partition_id}:{part_index}",
                "statement_fp": ctx.stmt_fps[label],
                "statement_fps": group_fps,
                "group": list(part),
            }
        stored_parts.append(part)
    if stored_parts:
        _record(
            ctx.telemetry,
            "phase1_local_bisection_stored",
            labels=list(route.failed_labels),
            parts=stored_parts,
            global_section_size=ctx.effective_section_size or ctx.section_size,
        )


def _apply_phase1_retry_scheduling(ctx: Ctx, request: RepairRequest) -> None:
    """Apply generation evidence to scheduling without conflating plan shape.

    Adaptive capacity and quarantine describe emitted statement-generation
    behavior. A pre-generation contract-plan closure failure has emitted no
    statements, so it must leave both controls unchanged; its corrected or
    invalidated plan entry already supplies the next retry's state transition.
    """
    if request.plan_revision_required:
        _record(
            ctx.telemetry,
            "phase1_plan_revision_retry_scheduled",
            labels=request.labels,
            scheduler_size=ctx.effective_section_size or ctx.section_size,
            scheduler_unchanged=True,
        )
        return
    if request.failure_route is None:
        _quarantine_labels(ctx, request.labels, "phase1_generation_retry")
        return

    routes = request.failure_routes or [request.failure_route]
    for route in routes:
        if route.action in {"isolate", "singleton", "independent"}:
            _quarantine_labels(
                ctx,
                route.failed_labels,
                "phase1_generation_retry",
            )
        elif route.action == "bisect":
            _store_local_bisection(ctx, route)
    _record(
        ctx.telemetry,
        "phase1_failure_routes_applied",
        route_count=len(routes),
        actions=[route.action for route in routes],
        failing_groups=[list(route.failed_labels) for route in routes],
    )


def _current_diagnostic_candidate_fp(ctx: Ctx, label: str) -> str:
    """Return the exact candidate currently eligible for correction."""
    phase2 = (getattr(ctx, "phase2_node_candidates", {}) or {}).get(label)
    if isinstance(phase2, dict) and str(phase2.get("candidate_hash") or ""):
        return str(phase2["candidate_hash"])
    phase1 = (getattr(ctx, "generation_candidates", {}) or {}).get(label)
    if not isinstance(phase1, dict):
        return ""
    working = phase1.get("working_candidate")
    if isinstance(working, dict) and str(working.get("candidate_hash") or ""):
        return str(working["candidate_hash"])
    return str(
        phase1.get("candidate_hash")
        or (
            _candidate_hash(str(phase1.get("code") or ""))
            if str(phase1.get("code") or "").strip()
            else ""
        )
    )


def _diagnostic_evidence_policy(source: str) -> tuple[str, str]:
    """Classify one producer by fact kind and validity boundary.

    Explicit semantic/audit requirements describe the blueprint statement and
    survive candidate/plan replacement. Plan findings survive candidate edits
    but not a plan replacement. Mechanical diagnostics describe exact emitted
    code and expire with that candidate. Unknown producers conservatively keep
    statement-scoped evidence; they cannot authorize mutation by themselves.
    """
    normalized = source.strip().lower()
    if "phase1_interface_usability" in normalized:
        # This is not the raw compiler diagnostic.  The interface gate has
        # already established that every implementation/proof body was `sorry`
        # and normalized the failure into a strategy requirement for this
        # unchanged blueprint statement.  Keep that requirement across a plan
        # replacement so the replacement prompt does not rediscover the same
        # unusable public representation.  Raw Lean/compiler evidence remains
        # candidate-scoped below.
        return "operational", "statement"
    if "plan" in normalized:
        return "plan", "plan"
    if any(
        token in normalized
        for token in (
            "compile",
            "compiler",
            "deterministic",
            "interface_usability",
            "candidate_regression",
        )
    ):
        kind = "compiler" if "compil" in normalized else "deterministic"
        return kind, "candidate"
    if any(
        token in normalized
        for token in ("alignment", "semantic", "blueprint_direct", "audit")
    ):
        return "semantic", "statement"
    return "operational", "statement"


def _canonical_failure_identity(value: Any) -> Any:
    """Normalize structured failure facts without interpreting prose.

    Lists in diagnostic payloads represent sets of obligations, dependencies,
    or helpers.  Sorting them makes equivalent structured reports stable while
    leaving free-text-only failures distinct.
    """
    if isinstance(value, Mapping):
        return {
            str(key): _canonical_failure_identity(item)
            for key, item in sorted(value.items(), key=lambda pair: str(pair[0]))
            if item not in (None, "", [], {}, ())
        }
    if isinstance(value, (list, tuple, set, frozenset)):
        normalized = [_canonical_failure_identity(item) for item in value]
        encoded = {
            json.dumps(item, sort_keys=True, separators=(",", ":")): item
            for item in normalized
            if item not in (None, "", [], {})
        }
        return [encoded[key] for key in sorted(encoded)]
    if isinstance(value, str):
        return " ".join(value.split())
    return value


def _diagnostic_failure_signature(
    *,
    kind: str,
    text: str,
    identity: Mapping[str, Any] | None = None,
) -> str:
    """Fingerprint one failure by objective facts when they are available.

    Compiler diagnostics use their existing location-insensitive error shape.
    Semantic and operational prose is never guessed to be equivalent: without
    structured facts it falls back to the exact normalized text hash.
    """
    canonical_identity = _canonical_failure_identity(dict(identity or {}))
    if canonical_identity:
        # The same objective fact may pass through an exact producer and an
        # outer orchestration wrapper that assign different policy kinds. The
        # structured fact itself is authoritative; producer kind controls its
        # lifetime, not whether it is a new failure.
        material: dict[str, Any] = {"identity": canonical_identity}
    elif kind == "compiler":
        material = {"kind": kind, "lean_error_shape": _lean_error_shape(text)}
    else:
        material = {
            "kind": kind,
            "text_sha256": hashlib.sha256(
                " ".join(text.split()).encode("utf-8")
            ).hexdigest(),
        }
    return hashlib.sha256(
        json.dumps(material, sort_keys=True, separators=(",", ":")).encode(
            "utf-8"
        )
    ).hexdigest()


def _diagnostic_evidence_id(payload: Mapping[str, Any]) -> str:
    signature = str(payload.get("failure_signature") or "") or (
        _diagnostic_failure_signature(
            kind=str(payload.get("kind") or "operational"),
            text=str(payload.get("text") or ""),
            identity=(
                payload.get("failure_identity")
                if isinstance(payload.get("failure_identity"), Mapping)
                else None
            ),
        )
    )
    identity = {
        "label": payload.get("label", ""),
        "statement_fp": payload.get("statement_fp", ""),
        "kind": payload.get("kind", ""),
        "lifetime": payload.get("lifetime", ""),
        "plan_fp": payload.get("plan_fp", ""),
        "candidate_fp": payload.get("candidate_fp", ""),
        "failure_signature": signature,
    }
    return hashlib.sha256(
        json.dumps(identity, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _record_diagnostic_evidence(
    ctx: Ctx,
    label: str,
    text: str,
    *,
    source: str,
    kind: str | None = None,
    lifetime: str | None = None,
    data: Mapping[str, Any] | None = None,
    failure_identity: Mapping[str, Any] | None = None,
    candidate_fp: str | None = None,
    plan_fp: str | None = None,
) -> str:
    """Store one immutable diagnostic fact with an explicit validity scope."""
    if label not in getattr(ctx, "nodes", {}):
        return ""
    inferred_kind, inferred_lifetime = _diagnostic_evidence_policy(source)
    kind = kind or inferred_kind
    lifetime = lifetime or inferred_lifetime
    if lifetime not in EVIDENCE_LIFETIMES:
        raise ValueError(f"unsupported diagnostic evidence lifetime: {lifetime}")
    statement_fp = getattr(ctx, "stmt_fps", {}).get(label, "")
    if not statement_fp:
        return ""
    resolved_plan_fp = (
        str(plan_fp)
        if plan_fp is not None
        else (_candidate_plan_fingerprint(ctx, label) if lifetime == "plan" else "")
    )
    resolved_candidate_fp = (
        str(candidate_fp)
        if candidate_fp is not None
        else (_current_diagnostic_candidate_fp(ctx, label) if lifetime == "candidate" else "")
    )
    # A mechanical fact is meaningful only for the exact emitted candidate.
    # Candidate persistence is the authoritative publication point for these
    # diagnostics, so never widen an unattached compiler/deterministic finding
    # into statement-scoped feedback. Doing so would let an error from discarded
    # Lean survive regeneration and poison the replacement candidate.
    if lifetime == "candidate" and not resolved_candidate_fp:
        telemetry = getattr(ctx, "telemetry", None)
        if telemetry is not None:
            _record(
                telemetry,
                "diagnostic_evidence_unattached_candidate_discarded",
                label=label,
                source=source,
                kind=kind,
                statement_fp=statement_fp,
                text_sha256=hashlib.sha256(text.encode("utf-8")).hexdigest(),
            )
        return ""
    canonical_identity = _canonical_failure_identity(dict(failure_identity or {}))
    failure_signature = _diagnostic_failure_signature(
        kind=kind,
        text=text,
        identity=canonical_identity,
    )
    payload = {
        "schema_version": DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION,
        "label": label,
        "statement_fp": statement_fp,
        "kind": kind,
        "lifetime": lifetime,
        "plan_fp": resolved_plan_fp if lifetime == "plan" else "",
        "candidate_fp": resolved_candidate_fp if lifetime == "candidate" else "",
        "text": text.strip()[-12000:],
        "data": copy.deepcopy(dict(data or {})),
        "failure_identity": canonical_identity,
        "failure_signature": failure_signature,
        "sources": [source],
        "consumed": False,
    }
    if not payload["text"] and not payload["data"]:
        return ""
    # Outer orchestration layers may repeat a failure while carrying it toward
    # the main loop. They cannot widen an exact candidate/plan fact into
    # generic statement-scoped feedback. If the exact producer arrives after a
    # compatibility producer, replace the broader record with the typed one.
    evidence_id = _diagnostic_evidence_id(payload)
    with _STATE_LOCK:
        ledger = getattr(ctx, "diagnostic_evidence", None)
        if ledger is None:
            ledger = {}
            ctx.diagnostic_evidence = ledger
        for previous_id, previous in list(ledger.items()):
            previous_signature = (
                _diagnostic_failure_signature(
                    kind=str(previous.get("kind") or "operational"),
                    text=str(previous.get("text") or ""),
                    identity=(
                        previous.get("failure_identity")
                        if isinstance(previous.get("failure_identity"), Mapping)
                        else None
                    ),
                )
                if isinstance(previous, dict)
                else ""
            )
            same_raw_fact = bool(
                isinstance(previous, dict)
                and str(previous.get("text") or "") == payload["text"]
                and (previous.get("data") or {}) == payload["data"]
            )
            if (
                not isinstance(previous, dict)
                or not _diagnostic_record_is_active(ctx, previous)
                or str(previous.get("label") or "") != label
                or str(previous.get("statement_fp") or "") != statement_fp
                or (
                    previous_signature != failure_signature
                    and not same_raw_fact
                )
            ):
                continue
            previous_kind = str(previous.get("kind") or "operational")
            if kind == "operational" and previous_kind != "operational":
                sources = list(previous.get("sources") or [])
                if source not in sources:
                    sources.append(source)
                previous["sources"] = sources[-8:]
                return previous_id
            if previous_kind == "operational" and kind != "operational":
                ledger.pop(previous_id, None)
        previous = ledger.get(evidence_id)
        if isinstance(previous, dict):
            sources = list(previous.get("sources") or [])
            if source not in sources:
                sources.append(source)
            previous["sources"] = sources[-8:]
            previous["consumed"] = False
        else:
            ledger[evidence_id] = payload
    return evidence_id


def _diagnostic_record_is_active(ctx: Ctx, entry: Mapping[str, Any]) -> bool:
    if bool(entry.get("consumed")):
        return False
    label = str(entry.get("label") or "")
    if (
        label not in getattr(ctx, "nodes", {})
        or str(entry.get("statement_fp") or "")
        != getattr(ctx, "stmt_fps", {}).get(label, "")
    ):
        return False
    lifetime = str(entry.get("lifetime") or "statement")
    if lifetime == "plan":
        return str(entry.get("plan_fp") or "") == _candidate_plan_fingerprint(
            ctx, label
        )
    if lifetime == "candidate":
        return str(entry.get("candidate_fp") or "") == _current_diagnostic_candidate_fp(
            ctx, label
        )
    return lifetime in {"statement", "transaction"}


def _prune_stale_diagnostic_evidence(ctx: Ctx) -> set[str]:
    """Remove facts whose explicit validity boundary no longer matches."""
    with _STATE_LOCK:
        ledger = getattr(ctx, "diagnostic_evidence", {})
        stale = {
            evidence_id
            for evidence_id, entry in ledger.items()
            if not isinstance(entry, dict) or not _diagnostic_record_is_active(ctx, entry)
        }
        for evidence_id in stale:
            ledger.pop(evidence_id, None)
    return stale


def _active_diagnostic_evidence(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    kinds: set[str] | None = None,
) -> list[dict[str, Any]]:
    wanted = set(labels)
    _prune_stale_diagnostic_evidence(ctx)
    with _STATE_LOCK:
        return [
            copy.deepcopy(entry)
            for entry in getattr(ctx, "diagnostic_evidence", {}).values()
            if isinstance(entry, dict)
            and str(entry.get("label") or "") in wanted
            and (kinds is None or str(entry.get("kind") or "") in kinds)
        ]


def _consume_diagnostic_evidence(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    kinds: set[str] | None = None,
) -> set[str]:
    wanted = set(labels)
    consumed: set[str] = set()
    with _STATE_LOCK:
        for evidence_id, entry in getattr(ctx, "diagnostic_evidence", {}).items():
            if not isinstance(entry, dict):
                continue
            if str(entry.get("label") or "") not in wanted:
                continue
            if kinds is not None and str(entry.get("kind") or "") not in kinds:
                continue
            entry["consumed"] = True
            consumed.add(evidence_id)
    _prune_stale_diagnostic_evidence(ctx)
    return consumed


def _migrate_legacy_generation_feedback(ctx: Ctx) -> None:
    """Import pre-ledger continuation state without broadening its authority."""
    existing = {
        (
            str(entry.get("label") or ""),
            str(entry.get("text") or "").strip(),
        )
        for entry in getattr(ctx, "diagnostic_evidence", {}).values()
        if isinstance(entry, dict)
    }
    for label, entry in list(getattr(ctx, "generation_feedback", {}).items()):
        if not isinstance(entry, dict):
            continue
        if str(entry.get("statement_fp") or "") != getattr(ctx, "stmt_fps", {}).get(label):
            continue
        evidence = str(entry.get("evidence") or "").strip()
        if (label, evidence) in existing:
            continue
        source = str(entry.get("source") or "unknown")
        kind, lifetime = _diagnostic_evidence_policy(source)
        _record_diagnostic_evidence(
            ctx,
            label,
            evidence,
            source=f"legacy:{source}",
            kind=kind,
            lifetime=lifetime,
        )


def _sync_generation_feedback_projection(ctx: Ctx) -> None:
    """Maintain the legacy per-label view from active prompt evidence."""
    prompt_kinds = {"compiler", "deterministic", "semantic", "plan", "operational"}
    records = _active_diagnostic_evidence(
        ctx, getattr(ctx, "nodes", {}), kinds=prompt_kinds
    )
    grouped: dict[str, list[dict[str, Any]]] = {}
    for entry in records:
        if str(entry.get("text") or "").strip():
            grouped.setdefault(str(entry["label"]), []).append(entry)
    projection: dict[str, dict[str, str]] = {}
    for label, entries in grouped.items():
        texts: list[str] = []
        sources: list[str] = []
        for entry in entries:
            text = str(entry.get("text") or "").strip()
            if text and text not in texts:
                texts.append(text)
            sources.extend(str(item) for item in entry.get("sources") or [])
        projection[label] = {
            "statement_fp": getattr(ctx, "stmt_fps", {}).get(label, ""),
            "evidence": "\n\n".join(texts)[-12000:],
            "source": sources[-1] if sources else "diagnostic_ledger",
        }
    ctx.generation_feedback = projection


def _prune_stale_generation_feedback(ctx: Ctx) -> set[str]:
    """Drop retry evidence outside its explicit validity boundary."""
    _migrate_legacy_generation_feedback(ctx)
    before = {
        str(entry.get("label") or "")
        for entry in getattr(ctx, "diagnostic_evidence", {}).values()
        if isinstance(entry, dict)
    }
    stale_evidence = _prune_stale_diagnostic_evidence(ctx)
    with _STATE_LOCK:
        feedback = getattr(ctx, "generation_feedback", {})
        stale = {
            label
            for label, entry in feedback.items()
            if label not in ctx.nodes
            or entry.get("statement_fp") != ctx.stmt_fps.get(label)
        }
        for label in stale:
            feedback.pop(label, None)
    _sync_generation_feedback_projection(ctx)
    if stale_evidence:
        after = {
            str(entry.get("label") or "")
            for entry in getattr(ctx, "diagnostic_evidence", {}).values()
            if isinstance(entry, dict)
        }
        stale.update(before - after)
    return stale


def _prune_stale_phase1_dependency_observations(ctx: Ctx) -> set[str]:
    """Drop generated-reference evidence for changed blueprint statements."""
    statement_fps = getattr(ctx, "stmt_fps", {})
    nodes = getattr(ctx, "nodes", {})
    with _STATE_LOCK:
        observations = getattr(ctx, "phase1_dependency_observations", {})
        stale = {
            label
            for label, entry in observations.items()
            if label not in nodes
            or entry.get("statement_fp") != statement_fps.get(label)
        }
        for label in stale:
            observations.pop(label, None)
    return stale


def _record_phase1_dependency_observations(
    ctx: Ctx,
    findings: Iterable[SkeletonFinding],
    code: str,
) -> dict[str, set[str]]:
    """Persist exact outside-closure references found in generated Lean.

    These observations are only one half of dependency-edge authorization.
    The independent statement critic must later name the same dependency for
    the same unchanged blueprint statement before the existing transactional
    edge writer can run.
    """
    observed: dict[str, set[str]] = {}
    for finding in findings:
        if (
            finding.category == "outside_dependency_closure"
            and finding.label in ctx.nodes
            and finding.dependencies
        ):
            observed.setdefault(str(finding.label), set()).update(
                dependency
                for dependency in finding.dependencies
                if dependency in ctx.nodes and dependency != finding.label
            )
    observed = {label: deps for label, deps in observed.items() if deps}
    if not observed:
        return {}

    candidate_hash = _candidate_hash(code)
    for label, dependencies in observed.items():
        _record_diagnostic_evidence(
            ctx,
            label,
            "",
            source="phase1_generated_dependency_reference",
            kind="dependency_reference",
            lifetime="statement",
            data={
                "dependencies": sorted(dependencies),
                "candidate_hashes": [candidate_hash],
            },
        )
    with _STATE_LOCK:
        store = getattr(ctx, "phase1_dependency_observations", None)
        if store is None:
            store = {}
            ctx.phase1_dependency_observations = store
        for label, dependencies in observed.items():
            statement_fp = getattr(ctx, "stmt_fps", {}).get(label, "")
            previous = store.get(label) or {}
            previous_dependencies = (
                set(previous.get("dependencies") or [])
                if previous.get("statement_fp") == statement_fp
                else set()
            )
            previous_hashes = (
                list(previous.get("candidate_hashes") or [])
                if previous.get("statement_fp") == statement_fp
                else []
            )
            if candidate_hash not in previous_hashes:
                previous_hashes.append(candidate_hash)
            store[label] = {
                "statement_fp": statement_fp,
                "dependencies": sorted(previous_dependencies | dependencies),
                "candidate_hashes": previous_hashes[-8:],
            }
    telemetry = getattr(ctx, "telemetry", None)
    if telemetry is not None:
        _record(
            telemetry,
            "phase1_dependency_reference_observed",
            labels=sorted(observed),
            dependencies={
                label: sorted(dependencies)
                for label, dependencies in sorted(observed.items())
            },
            candidate_sha256=candidate_hash,
            authorization="candidate_reference_only",
        )
    return observed


def _confirmed_phase1_dependency_observations(
    ctx: Ctx,
    required_dependencies: Mapping[str, set[str]],
) -> dict[str, set[str]]:
    """Join deterministic candidate evidence with independent critic evidence."""
    _prune_stale_phase1_dependency_observations(ctx)
    active_records = _active_diagnostic_evidence(
        ctx,
        required_dependencies,
        kinds={"dependency_reference"},
    )
    ledger_dependencies: dict[str, set[str]] = {}
    for record in active_records:
        ledger_dependencies.setdefault(str(record.get("label") or ""), set()).update(
            str(dependency)
            for dependency in (record.get("data") or {}).get("dependencies") or []
        )
    with _STATE_LOCK:
        observations = copy.deepcopy(
            getattr(ctx, "phase1_dependency_observations", {})
        )
    confirmed: dict[str, set[str]] = {}
    for label, required in required_dependencies.items():
        entry = observations.get(label) or {}
        if entry.get("statement_fp") != getattr(ctx, "stmt_fps", {}).get(label):
            continue
        observed_dependencies = set(entry.get("dependencies") or []) | ledger_dependencies.get(
            label, set()
        )
        matched = observed_dependencies & set(required)
        if matched:
            confirmed[label] = matched
    telemetry = getattr(ctx, "telemetry", None)
    if confirmed and telemetry is not None:
        _record(
            telemetry,
            "phase1_dependency_repair_authorized",
            labels=sorted(confirmed),
            required_dependencies={
                label: sorted(dependencies)
                for label, dependencies in sorted(confirmed.items())
            },
            authorization=(
                "persisted deterministic candidate reference and independent "
                "statement critic agree"
            ),
            avoided_route="plan_revision_or_generation_retry",
        )
    return confirmed


def _clear_phase1_dependency_observations(
    ctx: Ctx,
    required_dependencies: Mapping[str, set[str]],
) -> None:
    """Consume dependency observations after an edge transaction is attempted."""
    with _STATE_LOCK:
        for entry in getattr(ctx, "diagnostic_evidence", {}).values():
            if not isinstance(entry, dict) or entry.get("kind") != "dependency_reference":
                continue
            label = str(entry.get("label") or "")
            if label not in required_dependencies:
                continue
            data = dict(entry.get("data") or {})
            remaining = set(data.get("dependencies") or []) - set(
                required_dependencies[label]
            )
            if remaining:
                data["dependencies"] = sorted(remaining)
                entry["data"] = data
            else:
                entry["consumed"] = True
    _prune_stale_diagnostic_evidence(ctx)
    with _STATE_LOCK:
        observations = getattr(ctx, "phase1_dependency_observations", {})
        for label, dependencies in required_dependencies.items():
            entry = observations.get(label)
            if not isinstance(entry, dict):
                continue
            remaining = set(entry.get("dependencies") or []) - set(dependencies)
            if remaining:
                entry["dependencies"] = sorted(remaining)
            else:
                observations.pop(label, None)


def _explicit_generation_evidence_by_label(
    labels: Iterable[str], evidence: str
) -> dict[str, str]:
    """Split formatted audit/compiler findings without leaking sibling errors.

    Phase-1 findings use stable prefixes such as ``- lem:x [reject]:`` and
    ``- lem:x / `lem_x`:``.  Preserve each complete finding (including wrapped
    continuation lines) only for its named owner.  Unattributed file-level
    diagnostics are safe for a singleton; a multi-node caller must provide a
    structured ``evidence_by_label`` mapping instead of copying them to every
    node.
    """
    ordered = list(dict.fromkeys(labels))
    text = evidence.strip()
    if not text:
        return {}
    if len(ordered) == 1:
        return {ordered[0]: text}

    alternatives = "|".join(
        sorted((re.escape(label) for label in ordered), key=len, reverse=True)
    )
    marker = re.compile(
        rf"(?m)^\s*-?\s*(?P<label>{alternatives})"
        rf"(?:\s*/\s*`[^`]+`)?(?:\s*\[reject\])?\s*:"
    )
    matches = list(marker.finditer(text))
    scoped: dict[str, list[str]] = {}
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(text)
        block = text[match.start():end].strip()
        if block:
            scoped.setdefault(match.group("label"), []).append(block)
    return {
        label: "\n".join(blocks)[-12000:]
        for label, blocks in scoped.items()
        if blocks
    }


def _generation_evidence_from_findings(
    labels: Iterable[str], findings: Iterable[SkeletonFinding]
) -> dict[str, str]:
    """Render declaration-owned deterministic/compiler findings per node."""
    ordered = list(dict.fromkeys(labels))
    grouped: dict[str, list[SkeletonFinding]] = {label: [] for label in ordered}
    unowned: list[SkeletonFinding] = []
    for finding in findings:
        if finding.label in grouped:
            grouped[finding.label].append(finding)
        else:
            unowned.append(finding)
    if len(ordered) == 1 and unowned:
        grouped[ordered[0]].extend(unowned)
    return {
        label: _format_skeleton_findings(items)[-12000:]
        for label, items in grouped.items()
        if items
    }


def _compiler_generation_evidence_by_label(
    ctx: Ctx, labels: Iterable[str], code: str, evidence: str
) -> dict[str, str]:
    """Attribute Lean diagnostics using declaration ranges and owner metadata."""
    ordered = list(dict.fromkeys(labels))
    if len(ordered) == 1:
        return {ordered[0]: evidence.strip()[-12000:]}
    parsed = _parse_module(code)
    _rendered, ranges = _compose_module(
        parsed.imports, parsed.preamble, [decl.text for decl in parsed.decls]
    )
    file_name = ""
    for line in evidence.splitlines():
        match = _LOC_RE.match(line)
        if match and match.group("sev") == "error":
            file_name = Path(match.group("path")).name
            break
    if not file_name:
        return {}
    findings = _lean_compile_findings(
        parsed,
        ordered,
        ranges,
        evidence,
        file_name,
        _planned_helper_owner_by_name(ctx, ordered),
    )
    return _generation_evidence_from_findings(ordered, findings)


def _store_generation_feedback(
    ctx: Ctx,
    labels: Iterable[str],
    evidence: str,
    *,
    source: str,
    evidence_by_label: Mapping[str, str] | None = None,
    evidence_identity_by_label: Mapping[str, Mapping[str, Any]] | None = None,
) -> None:
    """Persist cumulative correction evidence for the current statement epoch.

    A later failure must not erase the finding that motivated the candidate we
    retained.  Keep a compact, deduplicated history so the next correction sees
    both the best candidate and every still-relevant reason it was rejected.
    """
    label_list = list(dict.fromkeys(labels))
    scoped = (
        {
            label: str(value).strip()[-12000:]
            for label, value in evidence_by_label.items()
            if label in label_list and str(value).strip()
        }
        if evidence_by_label is not None
        else _explicit_generation_evidence_by_label(label_list, evidence)
    )
    if not scoped:
        if evidence.strip() and len(label_list) > 1:
            _record(
                ctx.telemetry,
                "phase1_retry_feedback_unattributed",
                labels=label_list,
                source=source,
                evidence_sha256=hashlib.sha256(
                    evidence.encode("utf-8")
                ).hexdigest(),
            )
        return
    stored: list[str] = []
    statement_fps: dict[str, str] = {}
    for label in label_list:
        label_evidence = scoped.get(label, "")
        if not label_evidence:
            continue
        evidence_id = _record_diagnostic_evidence(
            ctx,
            label,
            label_evidence,
            source=source,
            failure_identity=(
                evidence_identity_by_label.get(label)
                if evidence_identity_by_label is not None
                else None
            ),
        )
        if evidence_id:
            stored.append(label)
            statement_fps[label] = ctx.stmt_fps.get(label, "")
    _sync_generation_feedback_projection(ctx)
    if stored:
        _record(
            ctx.telemetry,
            "phase1_retry_feedback_saved",
            labels=stored,
            source=source,
            evidence_chars=sum(len(scoped[label]) for label in stored),
            statement_fps=statement_fps,
        )


def _generation_feedback_for(
    ctx: Ctx,
    labels: Iterable[str],
    *,
    max_chars: int | None = None,
) -> str:
    """Return deduplicated current-version evidence for a generation prompt.

    When a targeted prompt has a strict context budget, retain both the start
    and end of every affected evidence history. The original semantic finding
    is normally at the start while later compiler diagnostics accumulate at
    the end; dropping either side recreates an already-rejected contract.
    """
    label_list = list(dict.fromkeys(labels))
    _migrate_legacy_generation_feedback(ctx)
    records = _active_diagnostic_evidence(
        ctx,
        label_list,
        kinds={"compiler", "deterministic", "semantic", "plan", "operational"},
    )
    # The ledger may contain the same typed fact at more than one validity
    # boundary (for example, an exact producer plus an older continuation
    # projection).  Render its stable identity once.  Unstructured evidence
    # remains keyed by exact text; we do not guess that differently worded
    # diagnostics are equivalent.
    grouped: dict[str, tuple[str, list[str]]] = {}
    for entry in records:
        label = str(entry.get("label") or "")
        evidence = str(entry.get("text") or "").strip()
        if evidence:
            signature = str(entry.get("failure_signature") or "")
            key = signature or ("text:" + evidence)
            current = grouped.get(key)
            if current is None:
                grouped[key] = (evidence, [label])
                continue
            rendered_evidence, owners = current
            if label not in owners:
                owners.append(label)
    if not grouped:
        return ""
    rendered: list[str] = []
    group_budget = None
    if max_chars is not None:
        group_budget = max(512, max_chars // len(grouped) - 160)
    for evidence, group_labels in grouped.values():
        if group_budget is not None and len(evidence) > group_budget:
            half = max(1, (group_budget - 48) // 2)
            evidence = (
                evidence[:half]
                + "\n... persisted evidence compacted ...\n"
                + evidence[-half:]
            )
        rendered.append(
            "Persisted rejection evidence for "
            + ", ".join(group_labels)
            + ":\n"
            + evidence
        )
    text = "\n\n".join(rendered)
    _record(
        ctx.telemetry,
        "phase1_retry_feedback_injected",
        labels=list(
            dict.fromkeys(
                label
                for _evidence, group_labels in grouped.values()
                for label in group_labels
            )
        ),
        evidence_chars=len(text),
    )
    return text


def _clear_generation_feedback(ctx: Ctx, labels: Iterable[str]) -> None:
    """Forget correction evidence only after those statements are accepted."""
    label_list = list(labels)
    _consume_diagnostic_evidence(
        ctx,
        label_list,
        kinds={"compiler", "deterministic", "semantic", "plan", "operational"},
    )
    with _STATE_LOCK:
        feedback = getattr(ctx, "generation_feedback", {})
        for label in label_list:
            feedback.pop(label, None)
