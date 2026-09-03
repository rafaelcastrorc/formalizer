"""Phase-1 checkpoint and the Phase-2 repair transaction queue/lifecycle.

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


def _phase2_repair_context_fingerprint(ctx: "Ctx", labels: Iterable[str]) -> str:
    """Hash the exact blueprint dependency environment behind repair evidence.

    A queued diagnosis is reusable only while its target statements and their
    transitive statement/proof dependency graph remain unchanged. This is a
    deterministic graph walk; it adds no model call to the repair path.
    """
    nodes = getattr(ctx, "nodes", {})
    stmt_fps = getattr(ctx, "stmt_fps", {})
    roots = sorted({str(label) for label in labels if str(label) in nodes})
    closure: set[str] = set()
    stack = list(reversed(roots))
    while stack:
        label = stack.pop()
        if label in closure or label not in nodes:
            continue
        closure.add(label)
        current = nodes[label]
        dependencies = {
            str(dep)
            for dep in (
                set(getattr(current, "uses", set()) or set())
                | set(getattr(current, "statement_uses", set()) or set())
                | set(getattr(current, "proof_uses", set()) or set())
            )
            if str(dep) in nodes and str(dep) != label
        }
        stack.extend(sorted(dependencies - closure, reverse=True))
    payload = {
        "roots": roots,
        "nodes": {
            label: {
                "statement_fp": str(stmt_fps.get(label) or ""),
                "uses": sorted(
                    str(dep)
                    for dep in set(getattr(nodes[label], "uses", set()) or set())
                    if str(dep) in nodes and str(dep) != label
                ),
                "statement_uses": sorted(
                    str(dep)
                    for dep in set(
                        getattr(nodes[label], "statement_uses", set()) or set()
                    )
                    if str(dep) in nodes and str(dep) != label
                ),
                "proof_uses": sorted(
                    str(dep)
                    for dep in set(
                        getattr(nodes[label], "proof_uses", set()) or set()
                    )
                    if str(dep) in nodes and str(dep) != label
                ),
            }
            for label in sorted(closure)
        },
    }
    return hashlib.sha256(
        json.dumps(payload, sort_keys=True, separators=(",", ":")).encode("utf-8")
    ).hexdigest()


def _phase2_repair_transaction_dir(name: str, request_id: str) -> Path:
    """Durable rollback point for one unpublished Phase-2 graph edit."""
    return SCRATCH_DIR / name / "phase2-repair-transactions" / request_id


def _phase1_checkpoint_dir(name: str) -> Path:
    """Immutable restart point captured at the Phase 1/Phase 2 boundary."""
    return SCRATCH_DIR / name / "phase1-checkpoint"


def _phase1_checkpoint_available(name: str) -> bool:
    """Return whether a complete Phase 1 checkpoint is available to restore."""
    root = _phase1_checkpoint_dir(name)
    try:
        manifest = json.loads((root / "manifest.json").read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return False
    return bool(
        manifest.get("version") == 1
        and (root / "blueprint-draft" / "blueprint" / "src" / "content.tex").is_file()
        and (root / "skeleton_state.json").is_file()
    )


def _replace_tree_from_snapshot(source: Path, destination: Path) -> None:
    """Replace an optional directory with its exact snapshotted contents."""
    if destination.exists():
        shutil.rmtree(destination)
    if source.is_dir():
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copytree(source, destination)


def _create_phase1_checkpoint(ctx: "Ctx") -> bool:
    """Save one immutable, coherent copy of the completed Phase 1 state.

    Phase 2 mutates the live draft, generated modules, compiled objects, and
    scheduler state together.  The checkpoint therefore captures all four;
    copying only the state JSON would create an unusable mixed-version resume.
    The first committed checkpoint for a run wins and is never edited in place.
    """
    destination = _phase1_checkpoint_dir(ctx.name)
    if _phase1_checkpoint_available(ctx.name):
        return False

    if destination.exists():
        shutil.rmtree(destination)
    destination.parent.mkdir(parents=True, exist_ok=True)
    pending = destination.parent / (
        f".phase1-checkpoint.pending-{os.getpid()}-{threading.get_ident()}"
    )
    if pending.exists():
        shutil.rmtree(pending)
    pending.mkdir(parents=True)

    draft = Path(ctx.blueprint_dir)
    generated = _generated_module_dir(ctx.name)
    lake_generated = _generated_lake_module_dir(ctx.name)
    state = _state_path(ctx.name)
    if not state.is_file():
        raise RuntimeError("cannot checkpoint Phase 1 without persisted scheduler state")

    try:
        shutil.copytree(draft, pending / "blueprint-draft")
        if generated.is_dir():
            shutil.copytree(generated, pending / "generated")
        if lake_generated.is_dir():
            shutil.copytree(lake_generated, pending / "lake-generated")
        shutil.copy2(state, pending / "skeleton_state.json")
        (pending / "manifest.json").write_text(
            json.dumps(
                {
                    "version": 1,
                    "created_at": int(time.time()),
                    "blueprint_sha256": hashlib.sha256(
                        ctx.content_path.read_bytes()
                    ).hexdigest(),
                    "state_sha256": hashlib.sha256(state.read_bytes()).hexdigest(),
                    "generated_present": generated.is_dir(),
                    "lake_generated_present": lake_generated.is_dir(),
                },
                indent=2,
                sort_keys=True,
            )
            + "\n",
            encoding="utf-8",
        )
        os.replace(pending, destination)
    finally:
        if pending.exists():
            shutil.rmtree(pending, ignore_errors=True)

    if not _phase1_checkpoint_available(ctx.name):
        raise RuntimeError("Phase 1 checkpoint was not committed completely")
    _record(
        ctx.telemetry,
        "phase1_checkpoint_created",
        path=str(destination.relative_to(REPO_ROOT)),
        blueprint_sha256=hashlib.sha256(ctx.content_path.read_bytes()).hexdigest(),
    )
    _log(
        "==> Saved immutable Phase 1 checkpoint: "
        f"{destination.relative_to(REPO_ROOT)}"
    )
    return True


def _restore_phase1_checkpoint(name: str) -> Path:
    """Replace mutable unpublished state with its original Phase 1 snapshot."""
    source = _phase1_checkpoint_dir(name)
    if not _phase1_checkpoint_available(name):
        raise ValueError(
            f"no saved Phase 1 checkpoint exists for {name}; run Phase 1 to completion first"
        )

    draft = _draft_blueprint_dir(name)
    _replace_tree_from_snapshot(source / "blueprint-draft", draft)
    _replace_tree_from_snapshot(source / "generated", _generated_module_dir(name))
    _replace_tree_from_snapshot(
        source / "lake-generated", _generated_lake_module_dir(name)
    )
    state = _state_path(name)
    state.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source / "skeleton_state.json", state)
    shutil.rmtree(
        SCRATCH_DIR / name / "phase2-repair-transactions", ignore_errors=True
    )
    _log(
        "==> Restored original Phase 1 checkpoint; later unpublished Phase 2 "
        "changes were discarded"
    )
    return draft


def _begin_phase2_repair_transaction(
    ctx: "Ctx", request_id: str, *, replace_existing: bool = False
) -> None:
    """Persist the exact blueprint, Lean, and scheduler state before an edit.

    The repair model is allowed to add explicit blueprint helper nodes, but
    those nodes are provisional until their complete Lean declarations pass.
    This snapshot prevents a rejected provisional component from becoming the
    input to another repair or surviving an interrupted process.
    """
    if not request_id:
        return
    destination = _phase2_repair_transaction_dir(ctx.name, request_id)
    if (destination / "manifest.json").is_file() and not replace_existing:
        return
    if destination.exists():
        shutil.rmtree(destination)
    root = destination.parent
    root.mkdir(parents=True, exist_ok=True)
    pending = root / f".{request_id}.pending"
    if pending.exists():
        shutil.rmtree(pending)
    pending.mkdir(parents=True)
    draft = Path(ctx.blueprint_dir)
    generated = _generated_module_dir(ctx.name)
    lake_generated = _generated_lake_module_dir(ctx.name)
    state = _state_path(ctx.name)
    if not state.is_file():
        raise RuntimeError(
            "cannot begin Phase 2 blueprint transaction without persisted state"
        )
    shutil.copytree(draft, pending / "blueprint-draft")
    if generated.is_dir():
        shutil.copytree(generated, pending / "generated")
    if lake_generated.is_dir():
        shutil.copytree(lake_generated, pending / "lake-generated")
    shutil.copy2(state, pending / "skeleton_state.json")
    (pending / "manifest.json").write_text(
        json.dumps(
            {
                "version": 1,
                "request_id": request_id,
                "blueprint_sha256": hashlib.sha256(
                    ctx.content_path.read_bytes()
                ).hexdigest(),
                "generated_present": generated.is_dir(),
                "lake_generated_present": lake_generated.is_dir(),
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    os.replace(pending, destination)
    if not (destination / "manifest.json").is_file():
        raise RuntimeError(
            "Phase 2 blueprint transaction snapshot was not committed durably"
        )
    telemetry = getattr(ctx, "telemetry", None)
    if telemetry is not None:
        _record(
            telemetry,
            "phase2_repair_transaction_snapshot",
            request_id=request_id,
            labels=list(
                (getattr(ctx, "phase2_repair_active", {}) or {}).get("labels")
                or []
            ),
            blueprint_sha256=hashlib.sha256(
                ctx.content_path.read_bytes()
            ).hexdigest(),
        )


def _restore_phase2_repair_transaction_files(
    ctx: "Ctx", request_id: str
) -> None:
    """Restore the complete pre-edit filesystem state for one repair."""
    source = _phase2_repair_transaction_dir(ctx.name, request_id)
    if not (source / "manifest.json").is_file():
        raise RuntimeError(
            "active Phase 2 blueprint repair has no pre-edit transaction snapshot; "
            "start a fresh run rather than extending unverified blueprint edits"
        )
    _replace_tree_from_snapshot(source / "blueprint-draft", ctx.blueprint_dir)
    _replace_tree_from_snapshot(source / "generated", _generated_module_dir(ctx.name))
    _replace_tree_from_snapshot(
        source / "lake-generated", _generated_lake_module_dir(ctx.name)
    )
    state = _state_path(ctx.name)
    state.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source / "skeleton_state.json", state)


def _discard_phase2_repair_transaction(name: str, request_id: str) -> None:
    """Delete a rollback point only after its replacement Lean is accepted."""
    if request_id:
        shutil.rmtree(
            _phase2_repair_transaction_dir(name, request_id),
            ignore_errors=True,
        )


def _restore_interrupted_phase2_repair(
    name: str, blueprint_dir: Path
) -> str:
    """Undo an edit interrupted before it reached the verification stage.

    The state file is persisted before the repair model may write. A process
    killed during that write therefore resumes with stage ``repair``; restoring
    here happens before blueprint validation can observe a partial model edit.
    A persisted ``verify`` stage is intentionally retained for continuation.
    """
    state = _state_path(name)
    try:
        payload = json.loads(state.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return ""
    active = (
        (payload.get("scheduler") or {}).get("phase2_repair_active") or {}
    )
    request_id = str(active.get("request_id") or "")
    if not request_id or str(active.get("stage") or "repair") != "repair":
        return ""
    source = _phase2_repair_transaction_dir(name, request_id)
    if not (source / "manifest.json").is_file():
        return ""
    _replace_tree_from_snapshot(source / "blueprint-draft", blueprint_dir)
    _replace_tree_from_snapshot(source / "generated", _generated_module_dir(name))
    _replace_tree_from_snapshot(
        source / "lake-generated", _generated_lake_module_dir(name)
    )
    return request_id


def _merge_phase2_repair_followup(
    ctx: "Ctx", request_id: str, followup: RepairRequest
) -> RepairRequest:
    """Rebase new verification evidence onto the original repair component.

    The staged helper labels may no longer exist after rollback. They therefore
    remain diagnostic evidence, while edit authority returns to the original
    blueprint roots. The next repair must produce one complete replacement
    component from that clean graph rather than extending rejected helpers.
    """
    payload = next(
        (
            item
            for item in getattr(ctx, "phase2_repair_queue", [])
            if str(item.get("request_id") or "") == request_id
        ),
        None,
    )
    if payload is None:
        raise RuntimeError(f"Phase 2 repair queue lost active request {request_id}")
    original_labels = [
        str(label)
        for label in payload.get("labels") or []
        if str(label) in ctx.nodes
    ]
    if not original_labels:
        raise RuntimeError(
            "Phase 2 repair rollback lost every original repair root"
        )
    followup_note = (
        "The previous provisional blueprint component was discarded because "
        "its complete Lean verification exposed this additional blueprint "
        "defect. Replace the original component from its clean pre-edit graph; "
        "do not extend or refer to discarded provisional helper nodes.\n\n"
        + followup.evidence[-12000:]
    )
    original_evidence = str(payload.get("evidence") or "")[-12000:]
    payload["evidence"] = (
        original_evidence + "\n\n== Provisional component rejection ==\n" + followup_note
    )[-24000:]
    owned_verification_labels = {
        str(label)
        for label in payload.get("verification_owned_labels") or original_labels
    }
    followup_owned_labels = owned_verification_labels.intersection(
        str(label) for label in followup.labels
    )
    carried_followup_helpers = (
        [str(item) for item in followup.decomposition_helpers]
        if followup_owned_labels
        else []
    )
    payload["decomposition_helpers"] = list(
        dict.fromkeys(
            [
                *[str(item) for item in payload.get("decomposition_helpers") or []],
                *carried_followup_helpers,
            ]
        )
    )
    evidence_by_label = {
        str(label): str(value)
        for label, value in (payload.get("evidence_by_label") or {}).items()
        if str(label) in original_labels
    }
    for label in original_labels:
        previous = evidence_by_label.get(label, "")[-6000:]
        evidence_by_label[label] = (
            previous + "\n\n" + followup_note
        ).strip()[-12000:]
    payload["evidence_by_label"] = evidence_by_label
    payload["statement_fps"] = {
        label: str(ctx.stmt_fps.get(label) or "") for label in original_labels
    }
    payload["context_fp"] = _phase2_repair_context_fingerprint(
        ctx, original_labels
    )
    payload["model_repair_labels"] = list(
        dict.fromkeys(
            [
                *[str(label) for label in payload.get("model_repair_labels") or []],
                *original_labels,
            ]
        )
    )
    if followup.decomposition_helpers and not carried_followup_helpers:
        _record(
            ctx.telemetry,
            "phase2_repair_followup_helpers_scoped_out",
            request_id=request_id,
            original_labels=original_labels,
            owned_verification_labels=sorted(owned_verification_labels),
            followup_labels=list(followup.labels),
            scoped_out_helpers=list(followup.decomposition_helpers),
        )
    ctx.phase2_repair_active = {
        "request_id": request_id,
        "stage": "repair",
        "labels": original_labels,
        "verification_labels": [],
    }
    request = _pending_phase2_repair_request(ctx)
    if request is None:
        raise RuntimeError(
            "rolled-back Phase 2 repair did not return to the repair queue"
        )
    return request


def _restart_active_phase2_repair(
    ctx: "Ctx", sections: list["Section"], followup: RepairRequest
) -> tuple[list["Section"], RepairRequest]:
    """Roll back a rejected staged component and retry its original roots."""
    active = getattr(ctx, "phase2_repair_active", {}) or {}
    request_id = str(active.get("request_id") or "")
    if not request_id or str(active.get("stage") or "") != "verify":
        return sections, followup
    carried_queue = copy.deepcopy(getattr(ctx, "phase2_repair_queue", []))
    carried_active_payload = next(
        (
            payload
            for payload in carried_queue
            if str(payload.get("request_id") or "") == request_id
        ),
        None,
    )
    staged_labels = set(getattr(ctx, "nodes", {}))
    _restore_phase2_repair_transaction_files(ctx, request_id)
    validation = _validate_draft(ctx)
    if not validation.ok:
        raise RuntimeError(
            "pre-edit Phase 2 transaction snapshot no longer validates"
        )
    ctx.refresh_nodes(validation.nodes)
    restored_sections = _load_state(ctx, ctx.lean_command)
    restored_active_payload = next(
        (
            payload
            for payload in getattr(ctx, "phase2_repair_queue", [])
            if str(payload.get("request_id") or "") == request_id
        ),
        None,
    )
    if carried_active_payload is not None and restored_active_payload is not None:
        # The snapshot owns the clean graph/files. The live queue owns evidence
        # learned after earlier rejected provisional components.
        for key in (
            "evidence",
            "decomposition_helpers",
            "failure_routes",
            "plan_revision_required",
            "required_dependencies",
            "model_repair_labels",
            "evidence_by_label",
            "verification_owned_labels",
            "verification_recheck_labels",
        ):
            restored_active_payload[key] = copy.deepcopy(
                carried_active_payload.get(key)
            )
    existing_ids = {
        str(payload.get("request_id") or "")
        for payload in getattr(ctx, "phase2_repair_queue", [])
    }
    for payload in carried_queue:
        queued_id = str(payload.get("request_id") or "")
        labels = [str(label) for label in payload.get("labels") or []]
        if (
            queued_id
            and queued_id not in existing_ids
            and labels
            and all(label in ctx.nodes for label in labels)
        ):
            ctx.phase2_repair_queue.append(payload)
            existing_ids.add(queued_id)
    request = _merge_phase2_repair_followup(ctx, request_id, followup)
    _save_ctx_state(ctx, restored_sections)
    restored_labels = set(ctx.nodes)
    _record(
        ctx.telemetry,
        "phase2_repair_transaction_restarted",
        request_id=request_id,
        original_labels=list(request.labels),
        discarded_provisional_labels=sorted(staged_labels - restored_labels),
        followup_labels=list(followup.labels),
        followup_helpers=list(followup.decomposition_helpers),
    )
    _log(
        "==> Rejected provisional Phase 2 blueprint component rolled back; "
        "retrying the original component with exact verification evidence"
    )
    return restored_sections, request


def _reroute_active_phase2_repair_to_provider(
    ctx: "Ctx", sections: list["Section"], diagnosis: RepairRequest
) -> list["Section"]:
    """Roll back a consumer repair and queue its named provider separately.

    The boundary critic may discover that an unchanged dependency contract,
    rather than the provisional consumer edit, owns the mathematical defect.
    Edit authority must never cross that transaction boundary. Restore the
    consumer's pre-edit graph, retire its provisional request, and enqueue one
    provider-owned repair. The consumer remains unproved and is naturally
    rescheduled after the provider verifies.
    """
    active = getattr(ctx, "phase2_repair_active", {}) or {}
    request_id = str(active.get("request_id") or "")
    if not request_id or str(active.get("stage") or "") != "verify":
        raise RuntimeError(
            "provider-contract rerouting requires an active Phase 2 verification "
            "transaction"
        )
    providers = list(dict.fromkeys(diagnosis.provider_contract_labels))
    roots = list(dict.fromkeys(diagnosis.reschedule_labels))
    if not providers or not roots:
        raise RuntimeError(
            "provider-contract rerouting requires provider and consumer labels"
        )

    _restore_phase2_repair_transaction_files(ctx, request_id)
    validation = _validate_draft(ctx)
    if not validation.ok:
        raise RuntimeError(
            "pre-edit Phase 2 transaction snapshot no longer validates"
        )
    ctx.refresh_nodes(validation.nodes)
    restored_sections = _load_state(ctx, ctx.lean_command)
    eligible = _phase2_provider_contract_candidates(ctx, roots)
    invalid = [
        label for label in providers if label not in ctx.nodes or label not in eligible
    ]
    if invalid:
        raise RuntimeError(
            "boundary audit named provider(s) outside the original dependency "
            "closure after rollback: " + ", ".join(invalid)
        )

    _complete_phase2_repair_request(ctx, request_id)
    provider_request = RepairRequest(
        diagnosis.evidence,
        providers,
        section_labels=providers,
        context_labels=list(dict.fromkeys([*providers, *roots])),
        authorizes_blueprint_repair=True,
        model_repair_labels=providers,
        evidence_by_label={
            label: diagnosis.evidence[-12000:] for label in providers
        },
    )
    _enqueue_phase2_repair_requests(ctx, [provider_request])
    ctx.repair_boundary_pending = {}
    _save_ctx_state(ctx, restored_sections)
    _record(
        ctx.telemetry,
        "phase2_repair_rerouted_to_provider",
        superseded_request_id=request_id,
        provider_labels=providers,
        rescheduled_consumer_labels=roots,
        ownership="existing_dependency_closure",
    )
    _log(
        "==> Repaired consumer component rolled back; the boundary audit "
        "assigned the defect to dependency provider(s): " + ", ".join(providers)
    )
    return restored_sections


def _prune_stale_phase2_repair_queue(ctx: "Ctx") -> None:
    """Drop evidence whose target or dependency context has already changed."""
    current_fps = getattr(ctx, "stmt_fps", {})
    current_nodes = getattr(ctx, "nodes", {})
    active_id = str(
        (getattr(ctx, "phase2_repair_active", {}) or {}).get("request_id") or ""
    )
    retained: list[dict[str, Any]] = []
    superseded: list[dict[str, Any]] = []
    seen: set[str] = set()
    for payload in getattr(ctx, "phase2_repair_queue", []):
        if not isinstance(payload, dict):
            continue
        request_id = str(payload.get("request_id") or "")
        labels = [str(label) for label in payload.get("labels") or []]
        statement_fps = payload.get("statement_fps") or {}
        invalid_identity = (
            not request_id
            or request_id in seen
            or not labels
            or any(label not in current_nodes for label in labels)
        )
        statement_changed = any(
                str(statement_fps.get(label) or "")
                and str(statement_fps.get(label) or "") != current_fps.get(label)
                for label in labels
        )
        expected_context = str(payload.get("context_fp") or "")
        current_context = _phase2_repair_context_fingerprint(ctx, labels)
        context_changed = bool(expected_context and expected_context != current_context)
        if invalid_identity:
            continue
        # The active transaction is expected to change its own context. Keep
        # its authorization until the replacement Lean has been verified.
        if request_id != active_id and (statement_changed or context_changed):
            superseded.append(payload)
            continue
        if not expected_context:
            # State schema migration: establish a baseline without discarding
            # an older, otherwise valid persisted diagnosis.
            payload["context_fp"] = current_context
        retained.append(payload)
        seen.add(request_id)
    ctx.phase2_repair_queue = retained
    telemetry = getattr(ctx, "telemetry", None)
    if telemetry is not None:
        for payload in superseded:
            _record(
                telemetry,
                "phase2_repair_queue_superseded",
                request_id=str(payload.get("request_id") or ""),
                labels=[str(label) for label in payload.get("labels") or []],
                reason="dependency_context_changed",
                queue_size=len(retained),
            )


def _enqueue_phase2_repair_requests(
    ctx: "Ctx", requests: Iterable[RepairRequest]
) -> None:
    """Queue authorized worker failures without unioning their edit scopes."""
    if not hasattr(ctx, "phase2_repair_queue"):
        ctx.phase2_repair_queue = []
    _prune_stale_phase2_repair_queue(ctx)
    existing = {
        str(payload.get("request_id") or "")
        for payload in ctx.phase2_repair_queue
    }
    added: list[dict[str, Any]] = []
    for request in sorted(
        requests, key=lambda item: tuple(str(label) for label in item.labels)
    ):
        if not request.authorizes_blueprint_repair:
            raise ValueError("only blueprint-authorized requests may be queued")
        payload = _phase2_repair_request_payload(ctx, request)
        if payload["request_id"] in existing:
            continue
        ctx.phase2_repair_queue.append(payload)
        existing.add(payload["request_id"])
        added.append(payload)
    telemetry = getattr(ctx, "telemetry", None)
    if telemetry is not None and added:
        _record(
            telemetry,
            "phase2_repair_queue_enqueued",
            request_ids=[payload["request_id"] for payload in added],
            repair_scopes=[payload["labels"] for payload in added],
            queue_size=len(ctx.phase2_repair_queue),
            aggregation="independent",
        )


def _pending_phase2_repair_request(ctx: "Ctx") -> RepairRequest | None:
    """Return, but do not remove, the next persisted Phase-2 repair."""
    if not hasattr(ctx, "phase2_repair_queue"):
        ctx.phase2_repair_queue = []
    _prune_stale_phase2_repair_queue(ctx)
    if not ctx.phase2_repair_queue:
        return None
    active = getattr(ctx, "phase2_repair_active", {}) or {}
    active_id = str(active.get("request_id") or "")
    if active_id and str(active.get("stage") or "repair") == "verify":
        return None
    payload = next(
        (
            item
            for item in ctx.phase2_repair_queue
            if not active_id or str(item.get("request_id") or "") == active_id
        ),
        None,
    )
    if payload is None:
        ctx.phase2_repair_active = {}
        payload = ctx.phase2_repair_queue[0]
    routes = [
        _failure_route_from_payload(route)
        for route in payload.get("failure_routes") or []
        if isinstance(route, dict)
    ]
    request = RepairRequest(
        str(payload.get("evidence") or ""),
        [str(label) for label in payload.get("labels") or []],
        decomposition_helpers=[
            str(item) for item in payload.get("decomposition_helpers") or []
        ],
        section_labels=[
            str(label) for label in payload.get("section_labels") or []
        ],
        context_labels=[
            str(label) for label in payload.get("context_labels") or []
        ],
        authorizes_blueprint_repair=True,
        failure_routes=routes,
        plan_revision_required=bool(payload.get("plan_revision_required")),
        required_dependencies={
            str(label): {str(dep) for dep in dependencies}
            for label, dependencies in (
                payload.get("required_dependencies") or {}
            ).items()
        },
        model_repair_labels=[
            str(label) for label in payload.get("model_repair_labels") or []
        ],
        evidence_by_label={
            str(label): str(evidence)
            for label, evidence in (
                payload.get("evidence_by_label") or {}
            ).items()
        },
        evidence_identities_by_label={
            str(label): copy.deepcopy(identity)
            for label, identity in (
                payload.get("evidence_identities_by_label") or {}
            ).items()
            if isinstance(identity, dict)
        },
    )
    request.queue_id = str(payload.get("request_id") or "")
    return request


def _activate_phase2_repair_request(ctx: "Ctx", request_id: str) -> None:
    """Persist the single Phase-2 blueprint writer before it edits anything."""
    if not request_id:
        return
    active = getattr(ctx, "phase2_repair_active", {}) or {}
    active_id = str(active.get("request_id") or "")
    if active_id:
        if active_id != request_id:
            raise RuntimeError(
                "cannot activate a second Phase 2 blueprint repair before the "
                "current repair is verified"
            )
        return
    payload = next(
        (
            item
            for item in getattr(ctx, "phase2_repair_queue", [])
            if str(item.get("request_id") or "") == request_id
        ),
        None,
    )
    if payload is None:
        raise RuntimeError(f"Phase 2 repair queue lost request {request_id}")
    ctx.phase2_repair_active = {
        "request_id": request_id,
        "stage": "repair",
        "labels": [str(label) for label in payload.get("labels") or []],
        "verification_labels": [],
    }
    telemetry = getattr(ctx, "telemetry", None)
    if telemetry is not None:
        _record(
            telemetry,
            "phase2_repair_queue_activated",
            request_id=request_id,
            labels=list(ctx.phase2_repair_active["labels"]),
            queue_size=len(getattr(ctx, "phase2_repair_queue", [])),
        )


def _start_phase2_repair_transaction(
    ctx: "Ctx",
    sections: list["Section"],
    request: RepairRequest,
) -> str:
    """Activate one queued repair and persist its rollback point before edits.

    Phase 2 repair requests can arrive either from the persisted queue at the
    start of an orchestration iteration or directly from the proof frontier
    that diagnosed them. Both paths must cross this single transaction gate
    before any model or deterministic repair mutates the unpublished draft.
    """
    request_id = str(getattr(request, "queue_id", "") or "")
    if not request_id:
        raise RuntimeError(
            "Phase 2 blueprint repair reached the mutation boundary without "
            "a persisted queue identity"
        )
    active_before = getattr(ctx, "phase2_repair_active", {}) or {}
    active_id_before = str(active_before.get("request_id") or "")
    _activate_phase2_repair_request(ctx, request_id)
    _save_ctx_state(ctx, sections)
    # Queue identities are content-derived and may recur after a diagnosis is
    # re-enqueued. A newly activated request must therefore replace any stale
    # directory left by an earlier lifecycle. An already-active transaction,
    # especially one resumed in ``verify``, must retain its original baseline.
    replace_existing = not active_id_before
    if active_id_before and active_id_before != request_id:
        raise RuntimeError(
            "Phase 2 repair activation changed identity before snapshot creation"
        )
    _begin_phase2_repair_transaction(
        ctx, request_id, replace_existing=replace_existing
    )
    snapshot = _phase2_repair_transaction_dir(ctx.name, request_id)
    if not (snapshot / "manifest.json").is_file():
        raise RuntimeError(
            "Phase 2 blueprint repair activated without a durable pre-edit snapshot"
        )
    return request_id


def _start_caught_phase2_repair_transaction(
    ctx: "Ctx", sections: list["Section"], request: RepairRequest
) -> str:
    """Route a caught queued request through the durable snapshot gate."""
    request_id = str(getattr(request, "queue_id", "") or "")
    if not request_id:
        return ""
    return _start_phase2_repair_transaction(ctx, sections, request)


def _mark_phase2_repair_verifying(
    ctx: "Ctx",
    request_id: str,
    labels: Iterable[str],
    *,
    recheck_labels: Iterable[str] = (),
) -> None:
    """Block edits while separating repaired declarations from cache rechecks."""
    if not request_id:
        return
    _activate_phase2_repair_request(ctx, request_id)
    snapshot = _phase2_repair_transaction_dir(ctx.name, request_id)
    if not (snapshot / "manifest.json").is_file():
        raise RuntimeError(
            "cannot verify a Phase 2 blueprint repair without its pre-edit "
            "transaction snapshot"
        )
    active = ctx.phase2_repair_active
    active["stage"] = "verify"
    owned = {
        str(label) for label in labels if str(label) in getattr(ctx, "nodes", {})
    }
    rechecks = {
        str(label)
        for label in recheck_labels
        if str(label) in getattr(ctx, "nodes", {}) and str(label) not in owned
    }
    active["verification_labels"] = sorted(owned | rechecks)
    queue_payload = next(
        (
            payload
            for payload in getattr(ctx, "phase2_repair_queue", [])
            if str(payload.get("request_id") or "") == request_id
        ),
        None,
    )
    if queue_payload is not None:
        # Persist ownership on the queue payload because rollback restores the
        # pre-edit active marker before follow-up evidence is merged.
        queue_payload["verification_owned_labels"] = sorted(owned)
        queue_payload["verification_recheck_labels"] = sorted(rechecks)
    telemetry = getattr(ctx, "telemetry", None)
    if telemetry is not None:
        _record(
            telemetry,
            "phase2_repair_verification_started",
            request_id=request_id,
            labels=list(active["verification_labels"]),
            owned_labels=sorted(owned),
            recheck_labels=sorted(rechecks),
            queue_size=len(getattr(ctx, "phase2_repair_queue", [])),
        )


def _complete_phase2_repair_request(ctx: "Ctx", request_id: str) -> None:
    """Acknowledge a queued repair only after its replacement Lean verifies."""
    before = len(getattr(ctx, "phase2_repair_queue", []))
    ctx.phase2_repair_queue = [
        payload
        for payload in getattr(ctx, "phase2_repair_queue", [])
        if str(payload.get("request_id") or "") != request_id
    ]
    active = getattr(ctx, "phase2_repair_active", {}) or {}
    if str(active.get("request_id") or "") == request_id:
        ctx.phase2_repair_active = {}
    _prune_stale_phase2_repair_queue(ctx)
    if getattr(ctx, "name", ""):
        _discard_phase2_repair_transaction(ctx.name, request_id)
    telemetry = getattr(ctx, "telemetry", None)
    if telemetry is not None and len(ctx.phase2_repair_queue) != before:
        _record(
            telemetry,
            "phase2_repair_queue_completed",
            request_id=request_id,
            queue_size=len(ctx.phase2_repair_queue),
        )


def _complete_verified_phase2_repair(
    ctx: "Ctx", sections: list[Section]
) -> bool:
    """Complete an active repair once every replacement declaration is real."""
    active = getattr(ctx, "phase2_repair_active", {}) or {}
    if str(active.get("stage") or "") != "verify":
        return False
    request_id = str(active.get("request_id") or "")
    labels = {
        str(label)
        for label in active.get("verification_labels") or []
        if str(label) in ctx.nodes
    }
    if not request_id or not labels:
        return False
    frozen = _frozen_labels(sections)
    implemented, body_required = _phase2_body_progress(ctx, sections)
    complete = labels <= frozen and (labels & body_required) <= implemented
    if not complete:
        return False
    _complete_phase2_repair_request(ctx, request_id)
    _record(
        ctx.telemetry,
        "phase2_repair_verified",
        request_id=request_id,
        labels=sorted(labels),
    )
    return True
