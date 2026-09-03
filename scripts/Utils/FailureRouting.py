"""Failure-scope routing policy and RepairRequest aggregation/serialization.

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
# Model call plumbing


@dataclass
class CallResult:
    status: str  # ok | timeout | cancelled | transport_exhausted | error
    text: str = ""
    error: str = ""
    duration_s: float = 0.0
    # Output the backend had already emitted when a timeout killed it. Callers
    # may salvage complete declarations from it instead of discarding the call.
    partial_text: str = ""


def _runner_failure_status(exc: Exception) -> str:
    """Classify backend failure without letting infrastructure become math evidence."""
    if "cancelled" in str(exc).lower():
        return "cancelled"
    if _is_timeout_error(exc):
        return "timeout"
    if is_transient_error(exc):
        return "transport_exhausted"
    return "error"


@dataclass(frozen=True)
class FailureScopeDecision:
    """Provider-neutral retry scope for a Lean-generation failure.

    Classification remains the caller's responsibility: blueprint repair and
    confirmed decomposition never enter this policy. This object only prevents
    Phase 1 and Phase 2 from making different decisions about the size of the
    next Lean-generation unit.
    """

    action: str  # isolate | bisect | singleton | independent
    parts: tuple[tuple[str, ...], ...]
    failed_labels: tuple[str, ...]
    accepted_labels: tuple[str, ...]


def _route_lean_generation_failure(
    labels: Iterable[str], attributable_labels: Iterable[str] | None = None
) -> FailureScopeDecision:
    """Choose the next retry scope without interpreting mathematical evidence.

    A known proper subset is isolated while its siblings remain eligible for
    independent validation. Any unresolved multi-label unit is bisected. Only
    a singleton may proceed to the caller's existing escalation policy.
    """
    ordered = list(dict.fromkeys(labels))
    if not ordered:
        raise ValueError("cannot route an empty Lean-generation failure")
    label_set = set(ordered)
    attributable = (
        {label for label in attributable_labels or [] if label in label_set}
        if attributable_labels is not None
        else set()
    )
    if attributable and attributable < label_set:
        failed = tuple(label for label in ordered if label in attributable)
        accepted = tuple(label for label in ordered if label not in attributable)
        return FailureScopeDecision(
            action="isolate",
            parts=tuple(tuple(part) for part in _parts_around_labels(ordered, list(failed))),
            failed_labels=failed,
            accepted_labels=accepted,
        )
    if len(ordered) > 1:
        mid = len(ordered) // 2
        return FailureScopeDecision(
            action="bisect",
            parts=(tuple(ordered[:mid]), tuple(ordered[mid:])),
            failed_labels=tuple(ordered),
            accepted_labels=(),
        )
    return FailureScopeDecision(
        action="singleton",
        parts=(tuple(ordered),),
        failed_labels=tuple(ordered),
        accepted_labels=(),
    )


def _combine_failure_routes(
    routes: Iterable[FailureScopeDecision],
) -> FailureScopeDecision:
    """Represent independent failure scopes without losing their own parts.

    ``failure_route`` predates parallel Phase-1 transactions and can describe
    only one scope.  The combined value remains useful to old callers and log
    consumers, while ``RepairRequest.failure_routes`` retains each original
    decision so the orchestrator can apply isolate/bisect policy separately.
    """
    ordered_routes = list(routes)
    if not ordered_routes:
        raise ValueError("cannot combine an empty set of failure routes")
    if len(ordered_routes) == 1:
        return ordered_routes[0]

    parts: list[tuple[str, ...]] = []
    failed: list[str] = []
    accepted: list[str] = []
    for route in ordered_routes:
        parts.extend(route.parts)
        failed.extend(route.failed_labels)
        accepted.extend(route.accepted_labels)
    return FailureScopeDecision(
        action="independent",
        parts=tuple(dict.fromkeys(parts)),
        failed_labels=tuple(dict.fromkeys(failed)),
        accepted_labels=tuple(dict.fromkeys(accepted)),
    )


class RepairRequest(Exception):
    """Return bounded failure evidence to the main orchestration loop.

    Phase 1/2 requests may authorize blueprint repair. Initial-declaration
    requests are intercepted as provisional regeneration only.
    """

    def __init__(
        self,
        evidence: str,
        labels: list[str],
        *,
        decomposition_helpers: list[str] | None = None,
        section_labels: list[str] | None = None,
        context_labels: list[str] | None = None,
        frozen_sections: list["Section"] | None = None,
        authorizes_blueprint_repair: bool = True,
        failure_route: FailureScopeDecision | None = None,
        failure_routes: Iterable[FailureScopeDecision] | None = None,
        plan_revision_required: bool = False,
        required_dependencies: dict[str, set[str]] | None = None,
        model_repair_labels: Iterable[str] | None = None,
        evidence_by_label: Mapping[str, str] | None = None,
        evidence_identities_by_label: Mapping[str, Mapping[str, Any]] | None = None,
        implementation_prerequisites: Iterable[str] | None = None,
        scheduling_only: bool = False,
        retry_attempted_tier: str = "",
        provider_contract_labels: Iterable[str] | None = None,
        reschedule_labels: Iterable[str] | None = None,
        repair_components: Iterable[Mapping[str, Any]] | None = None,
    ):
        super().__init__(evidence[:500])
        self.evidence = evidence
        self.labels = labels
        self.decomposition_helpers = decomposition_helpers or []
        self.section_labels = section_labels or list(labels)
        self.context_labels = context_labels or list(self.section_labels)
        # Recursive section routing may freeze an easy prefix before a later
        # singleton proves that the blueprint needs repair. Preserve that work
        # across the exception instead of regenerating it after the repair.
        self.frozen_sections = frozen_sections or []
        self.authorizes_blueprint_repair = authorizes_blueprint_repair
        routes = list(failure_routes or [])
        if not routes and failure_route is not None:
            routes.append(failure_route)
        self.failure_routes = routes
        if failure_route is not None:
            self.failure_route = failure_route
        elif routes:
            self.failure_route = _combine_failure_routes(routes)
        else:
            self.failure_route = None
        self.plan_revision_required = plan_revision_required
        self.required_dependencies = {
            label: set(dependencies)
            for label, dependencies in (required_dependencies or {}).items()
            if dependencies
        }
        self.evidence_by_label = {
            str(label): str(value).strip()[-12000:]
            for label, value in (evidence_by_label or {}).items()
            if str(label) in labels and str(value).strip()
        }
        self.evidence_identities_by_label = {
            str(label): _canonical_failure_identity(dict(value))
            for label, value in (evidence_identities_by_label or {}).items()
            if str(label) in labels and isinstance(value, Mapping) and value
        }
        # A top-down Phase-2 proof can use deferred theorem statements, but it
        # cannot unfold a definition whose body is still ``sorry``. Such a
        # finding changes scheduling only: implement the named dependency body
        # first, then retry the original node without editing the blueprint or
        # consuming a blueprint-repair trial.
        self.implementation_prerequisites = list(
            dict.fromkeys(str(label) for label in implementation_prerequisites or [])
        )
        self.scheduling_only = bool(scheduling_only)
        # Generation workers report the tier that produced a deterministic
        # pre-compilation rejection. The coordinator owns retry transitions so
        # parallel workers never mutate shared plan/lifecycle state.
        self.retry_attempted_tier = (
            retry_attempted_tier
            if retry_attempted_tier in {"base", "escalation"}
            else ""
        )
        # A post-repair boundary audit may prove that the failing consumer is
        # faithfully using an existing dependency whose public contract is too
        # weak.  This is not authority to widen the consumer transaction.  The
        # coordinator rolls that transaction back and starts a separate repair
        # owned by the explicitly named provider.
        self.provider_contract_labels = list(
            dict.fromkeys(str(label) for label in provider_contract_labels or [])
        )
        self.reschedule_labels = list(
            dict.fromkeys(str(label) for label in reschedule_labels or [])
        )
        self.repair_components = [
            {
                "labels": list(
                    dict.fromkeys(
                        str(label) for label in component.get("labels") or []
                    )
                ),
                "evidence": str(component.get("evidence") or "")[-24000:],
            }
            for component in (repair_components or [])
            if component.get("labels")
        ]
        # Some authorized requests can be completed deterministically by adding
        # missing dependency edges; others require the repair model to change or
        # decompose blueprint contracts. Keep those scopes separate so combining
        # concurrent failures cannot silently replace one action with the other.
        if model_repair_labels is None:
            self.model_repair_labels = (
                list(labels)
                if authorizes_blueprint_repair and not self.required_dependencies
                else []
            )
        else:
            self.model_repair_labels = list(dict.fromkeys(model_repair_labels))


def _requires_blueprint_transaction(
    authorizes_blueprint_repair: bool,
    required_dependencies: dict[str, set[str]],
) -> bool:
    """Return whether the outer loop must enter its transactional edit path.

    A semantic critic can classify the remaining declaration problem as Lean
    generation while independently identifying an existing blueprint label
    required by the public statement.  That dependency evidence authorizes
    only the deterministic, cycle-checked ``\\uses`` edge transaction; it does
    not authorize a model rewrite of the blueprint.  Delaying the edge until
    the Lean-generation retry lifecycle is exhausted makes every intervening
    candidate operate against a graph already known to be incomplete.
    """
    return authorizes_blueprint_repair or bool(required_dependencies)


def _aggregate_retry_requests(
    requests: Iterable[RepairRequest],
    *,
    frozen_sections: Iterable["Section"] = (),
) -> RepairRequest:
    """Merge independent non-blueprint failures from one parallel transaction.

    Every candidate has already persisted its own code and evidence.  Returning
    one arbitrary exception would hide the remaining failures until later outer
    iterations.  This aggregate preserves every retry scope and all accepted
    sibling sections while still consuming one outer repair trial.
    """
    ordered = list(requests)
    if not ordered:
        raise ValueError("cannot aggregate an empty set of repair requests")
    if any(request.authorizes_blueprint_repair for request in ordered):
        raise ValueError("blueprint-authorized requests must be handled separately")

    routes = [
        route
        for request in ordered
        for route in (
            request.failure_routes
            or ([request.failure_route] if request.failure_route is not None else [])
        )
    ]
    labels = list(
        dict.fromkeys(label for request in ordered for label in request.labels)
    )
    section_labels = list(
        dict.fromkeys(
            label for request in ordered for label in request.section_labels
        )
    )
    context_labels = list(
        dict.fromkeys(
            label for request in ordered for label in request.context_labels
        )
    )
    sections_by_key: dict[tuple[int, str], Section] = {}
    for section in [
        *frozen_sections,
        *(section for request in ordered for section in request.frozen_sections),
    ]:
        sections_by_key[(section.number, str(section.path))] = section
    dependencies: dict[str, set[str]] = {}
    for request in ordered:
        for label, required in request.required_dependencies.items():
            dependencies.setdefault(label, set()).update(required)
    evidence = "\n\n".join(
        f"== Independent failure {index} ==\n{request.evidence}"
        for index, request in enumerate(ordered, 1)
    )
    evidence_by_label: dict[str, str] = {}
    evidence_identities_by_label: dict[str, dict[str, Any]] = {}
    for request in ordered:
        scoped = request.evidence_by_label or _explicit_generation_evidence_by_label(
            request.labels, request.evidence
        )
        for label, value in scoped.items():
            previous = evidence_by_label.get(label, "")
            evidence_by_label[label] = (
                previous + ("\n\n" if previous else "") + value
            )[-12000:]
        for label, identity in request.evidence_identities_by_label.items():
            evidence_identities_by_label[label] = copy.deepcopy(identity)
    combined_route = _combine_failure_routes(routes) if routes else None
    return RepairRequest(
        evidence,
        labels,
        section_labels=section_labels or labels,
        context_labels=context_labels or section_labels or labels,
        frozen_sections=list(sections_by_key.values()),
        authorizes_blueprint_repair=False,
        failure_route=combined_route,
        failure_routes=routes,
        plan_revision_required=any(
            request.plan_revision_required for request in ordered
        ),
        required_dependencies=dependencies,
        evidence_by_label=evidence_by_label,
        evidence_identities_by_label=evidence_identities_by_label,
    )


def _aggregate_authorized_repair_requests(
    requests: Iterable[RepairRequest],
    *,
    frozen_sections: Iterable["Section"] = (),
) -> RepairRequest:
    """Merge authorized repairs where the caller owns one shared transaction.

    Phase 1 uses this for a dependency-closed generation component. Phase 2
    complete-node workers deliberately do not call it: their failures are
    independent queue items with separate edit authority.
    """
    ordered = list(requests)
    if not ordered:
        raise ValueError("cannot aggregate an empty set of repair requests")
    if any(not request.authorizes_blueprint_repair for request in ordered):
        raise ValueError("only blueprint-authorized requests can be aggregated")

    labels = list(
        dict.fromkeys(label for request in ordered for label in request.labels)
    )
    model_labels = list(
        dict.fromkeys(
            label
            for request in ordered
            for label in request.model_repair_labels
        )
    )
    helpers = list(
        dict.fromkeys(
            helper
            for request in ordered
            for helper in request.decomposition_helpers
        )
    )
    dependencies: dict[str, set[str]] = {}
    for request in ordered:
        for label, required in request.required_dependencies.items():
            dependencies.setdefault(label, set()).update(required)
    sections_by_key: dict[tuple[int, str], Section] = {}
    for section in [
        *frozen_sections,
        *(section for request in ordered for section in request.frozen_sections),
    ]:
        sections_by_key[(section.number, str(section.path))] = section
    section_labels = list(
        dict.fromkeys(
            label for request in ordered for label in request.section_labels
        )
    )
    context_labels = list(
        dict.fromkeys(
            label for request in ordered for label in request.context_labels
        )
    )
    evidence = "\n\n".join(
        f"== Authorized repair {index} ==\n{request.evidence}"
        for index, request in enumerate(ordered, 1)
    )
    evidence_by_label: dict[str, str] = {}
    evidence_identities_by_label: dict[str, dict[str, Any]] = {}
    repair_components: list[dict[str, Any]] = []
    for request in ordered:
        scoped = request.evidence_by_label or _explicit_generation_evidence_by_label(
            request.labels, request.evidence
        )
        evidence_by_label.update(scoped)
        evidence_identities_by_label.update(
            copy.deepcopy(request.evidence_identities_by_label)
        )
        existing_components = list(getattr(request, "repair_components", []) or [])
        if existing_components:
            repair_components.extend(existing_components)
            continue
        component_labels = list(
            dict.fromkeys(request.model_repair_labels or request.labels)
        )
        if component_labels:
            repair_components.append(
                {
                    "labels": component_labels,
                    "evidence": request.evidence,
                }
            )
    return RepairRequest(
        evidence,
        labels,
        decomposition_helpers=helpers,
        section_labels=section_labels or labels,
        context_labels=context_labels or section_labels or labels,
        frozen_sections=list(sections_by_key.values()),
        authorizes_blueprint_repair=True,
        required_dependencies=dependencies,
        model_repair_labels=model_labels,
        evidence_by_label=evidence_by_label,
        evidence_identities_by_label=evidence_identities_by_label,
        repair_components=repair_components,
    )


def _combine_deferred_phase1_requests(
    requests: Iterable[RepairRequest],
) -> RepairRequest:
    """Select the next safe outer action after draining independent branches.

    Model-authored blueprint edits remain serialized. Exact generation and
    deterministic dependency-edge failures can be aggregated because their
    candidates and evidence are already persisted per label. If one request
    authorizes a model edit, unrelated non-editing failures stay persisted and
    resume after that scoped transaction instead of being widened into it.
    """
    ordered = list(requests)
    if not ordered:
        raise ValueError("cannot combine an empty Phase-1 request list")
    model_repairs = [
        request for request in ordered if request.authorizes_blueprint_repair
    ]
    if model_repairs:
        if len(model_repairs) == 1:
            return model_repairs[0]
        return _aggregate_authorized_repair_requests(model_repairs)
    if len(ordered) == 1:
        return ordered[0]
    return _aggregate_retry_requests(ordered)


def _failure_route_to_payload(route: FailureScopeDecision) -> dict[str, Any]:
    return {
        "action": route.action,
        "parts": [list(part) for part in route.parts],
        "failed_labels": list(route.failed_labels),
        "accepted_labels": list(route.accepted_labels),
    }


def _failure_route_from_payload(payload: Mapping[str, Any]) -> FailureScopeDecision:
    return FailureScopeDecision(
        action=str(payload.get("action") or "singleton"),
        parts=tuple(
            tuple(str(label) for label in part)
            for part in payload.get("parts") or []
        ),
        failed_labels=tuple(
            str(label) for label in payload.get("failed_labels") or []
        ),
        accepted_labels=tuple(
            str(label) for label in payload.get("accepted_labels") or []
        ),
    )


def _phase2_repair_request_payload(
    ctx: "Ctx", request: RepairRequest
) -> dict[str, Any]:
    """Serialize one independently authorized Phase-2 repair transaction."""
    labels = list(dict.fromkeys(str(label) for label in request.labels))
    statement_fps = {
        label: str(getattr(ctx, "stmt_fps", {}).get(label) or "")
        for label in labels
    }
    scoped_evidence = request.evidence_by_label or {
        label: request.evidence for label in labels
    }
    evidence_signatures = {
        label: _diagnostic_failure_signature(
            kind="semantic",
            text=str(scoped_evidence.get(label) or request.evidence),
            identity=request.evidence_identities_by_label.get(label),
        )
        for label in labels
    }
    identity = {
        "labels": labels,
        "statement_fps": statement_fps,
        "context_fp": _phase2_repair_context_fingerprint(ctx, labels),
        "model_repair_labels": list(request.model_repair_labels),
        "required_dependencies": {
            label: sorted(dependencies)
            for label, dependencies in request.required_dependencies.items()
        },
        "decomposition_helpers": list(request.decomposition_helpers),
        "evidence_signatures": evidence_signatures,
    }
    request_id = hashlib.sha256(
        json.dumps(identity, sort_keys=True).encode("utf-8")
    ).hexdigest()
    return {
        "request_id": request_id,
        "labels": labels,
        "statement_fps": statement_fps,
        "context_fp": identity["context_fp"],
        "evidence": request.evidence[-24000:],
        "decomposition_helpers": list(request.decomposition_helpers),
        "section_labels": list(request.section_labels),
        "context_labels": list(request.context_labels),
        "authorizes_blueprint_repair": True,
        "failure_routes": [
            _failure_route_to_payload(route)
            for route in request.failure_routes
        ],
        "plan_revision_required": bool(request.plan_revision_required),
        "required_dependencies": {
            label: sorted(dependencies)
            for label, dependencies in request.required_dependencies.items()
        },
        "model_repair_labels": list(request.model_repair_labels),
        "evidence_by_label": dict(request.evidence_by_label),
        "evidence_identities_by_label": copy.deepcopy(
            request.evidence_identities_by_label
        ),
    }
