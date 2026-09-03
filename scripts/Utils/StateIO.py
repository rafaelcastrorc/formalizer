"""Run-state persistence: _save_state/_save_ctx_state/_load_state and artifact pruning.

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


def _save_state(
    name: str,
    sections: list[Section],
    stmt_fps: dict[str, str],
    contract_fps: dict[str, str],
    *,
    quarantined_labels: set[str] | None = None,
    quarantine: dict[str, dict[str, str]] | None = None,
    local_group_partitions: dict[str, dict[str, Any]] | None = None,
    generation_feedback: dict[str, dict[str, str]] | None = None,
    diagnostic_evidence: dict[str, dict[str, Any]] | None = None,
    phase1_dependency_observations: dict[str, dict[str, Any]] | None = None,
    generation_candidates: dict[str, dict[str, Any]] | None = None,
    phase2_node_candidates: dict[str, dict[str, Any]] | None = None,
    phase1_exchange_history: dict[str, dict[str, Any]] | None = None,
    model_resume_sessions: dict[str, dict[str, Any]] | None = None,
    retry_lifecycle: dict[str, dict[str, Any]] | None = None,
    design_plan_entries: dict[str, dict[str, Any]] | None = None,
    semantic_plan_entries: dict[str, dict[str, Any]] | None = None,
    design_plan_alternates: dict[str, dict[str, Any]] | None = None,
    blueprint_direct_generation: dict[str, dict[str, Any]] | None = None,
    repair_boundary_pending: dict[str, Any] | None = None,
    phase2_repair_queue: list[dict[str, Any]] | None = None,
    phase2_repair_active: dict[str, Any] | None = None,
    phase2_prerequisite_labels: set[str] | None = None,
    phase2_started: bool = False,
    phase1_baseline_labels: set[str] | None = None,
    effective_section_size: int = 0,
    refinement_order: str = PHASE1_STATEMENT_ORDER,
    conjecture_policy: str = "attempt",
) -> None:
    entries = []
    for sec in sections:
        try:
            sha = _section_exact_source_fingerprint(sec.path)
        except OSError:
            continue
        entries.append(
            {
                "number": sec.number,
                "file": sec.file_name,
                "module": sec.module,
                "labels": sec.labels,
                "import_modules": sec.import_modules,
                "sha256": sha,
                "statement_fps": {label: stmt_fps.get(label, "") for label in sec.labels},
                "contract_fps": {label: contract_fps.get(label, "") for label in sec.labels},
                "deferred": sec.deferred,
                "refined_labels": (
                    None
                    if sec.refined_labels is None
                    else sorted(sec.refined_labels)
                ),
                "provisional_environment": sec.provisional_environment,
                "generation_tier": sec.generation_tier,
                "compile_fingerprint": sec.compile_fingerprint,
            }
        )
    # Direct callers may still provide only labels. Persist them with the
    # statement fingerprints available to this save so even that compatibility
    # path cannot create label-only quarantine state.
    quarantine_payload = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "failure_class": str(entry.get("failure_class") or "unknown"),
        }
        for label, entry in (quarantine or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
    }
    for label in quarantined_labels or set():
        if label in stmt_fps and label not in quarantine_payload:
            quarantine_payload[label] = {
                "statement_fp": stmt_fps[label],
                "failure_class": "unspecified",
            }

    local_partition_payload = {
        str(label): {
            "partition_id": str(entry.get("partition_id") or ""),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "statement_fps": {
                str(item): str(fp)
                for item, fp in (entry.get("statement_fps") or {}).items()
                if str(item) in stmt_fps and str(fp) == stmt_fps.get(str(item))
            },
            "group": [
                str(item)
                for item in entry.get("group") or []
                if str(item) in stmt_fps
            ],
        }
        for label, entry in (local_group_partitions or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and str(entry.get("partition_id") or "")
        and entry.get("group")
    }

    feedback_payload = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "source": str(entry.get("source") or "unknown"),
        }
        for label, entry in (generation_feedback or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and str(entry.get("evidence") or "").strip()
    }
    diagnostic_evidence_payload: dict[str, dict[str, Any]] = {}
    for entry in (diagnostic_evidence or {}).values():
        if not isinstance(entry, dict):
            continue
        label = str(entry.get("label") or "")
        lifetime = str(entry.get("lifetime") or "statement")
        if (
            label not in stmt_fps
            or str(entry.get("statement_fp") or "") != stmt_fps.get(label)
            or lifetime not in EVIDENCE_LIFETIMES
            or bool(entry.get("consumed"))
        ):
            continue
        normalized = {
            "schema_version": DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION,
            "label": label,
            "statement_fp": stmt_fps[label],
            "kind": str(entry.get("kind") or "operational")[:80],
            "lifetime": lifetime,
            "plan_fp": str(entry.get("plan_fp") or "")[:200],
            "candidate_fp": str(entry.get("candidate_fp") or "")[:200],
            "text": str(entry.get("text") or "")[-12000:],
            "data": copy.deepcopy(
                entry.get("data") if isinstance(entry.get("data"), dict) else {}
            ),
            "failure_identity": _canonical_failure_identity(
                entry.get("failure_identity")
                if isinstance(entry.get("failure_identity"), dict)
                else {}
            ),
            "failure_signature": str(entry.get("failure_signature") or ""),
            "sources": [
                str(source)[:200]
                for source in (entry.get("sources") or [])[-8:]
                if str(source)
            ],
            "consumed": False,
        }
        if not normalized["text"] and not normalized["data"]:
            continue
        diagnostic_evidence_payload[_diagnostic_evidence_id(normalized)] = normalized

    # Version-28 callers know only the flattened compatibility stores. Convert
    # them at the persistence boundary so their next resume uses the same
    # explicit lifecycle rules as a new run.
    if diagnostic_evidence is None:
        for label, entry in feedback_payload.items():
            source = str(entry.get("source") or "unknown")
            kind, lifetime = _diagnostic_evidence_policy(source)
            candidate_fp = ""
            if lifetime == "candidate":
                candidate_entry = (generation_candidates or {}).get(label) or {}
                working = candidate_entry.get("working_candidate")
                if isinstance(working, dict):
                    candidate_fp = str(working.get("candidate_hash") or "")
                if not candidate_fp:
                    candidate_fp = str(candidate_entry.get("candidate_hash") or "")
                if not candidate_fp and str(candidate_entry.get("code") or "").strip():
                    candidate_fp = _candidate_hash(str(candidate_entry["code"]))
                if not candidate_fp:
                    # A candidate diagnostic without its candidate cannot be
                    # safely replayed. Do not widen it into statement evidence.
                    continue
            normalized = {
                "schema_version": DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION,
                "label": label,
                "statement_fp": stmt_fps[label],
                "kind": kind,
                "lifetime": lifetime,
                "plan_fp": (
                    _design_plan_entry_fingerprint(
                        (design_plan_entries or {}).get(label) or {}
                    )
                    if lifetime == "plan"
                    else ""
                ),
                "candidate_fp": candidate_fp,
                "text": str(entry.get("evidence") or "")[-12000:],
                "data": {},
                "sources": [f"legacy:{source}"],
                "consumed": False,
            }
            diagnostic_evidence_payload[
                _diagnostic_evidence_id(normalized)
            ] = normalized
    dependency_observation_payload = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "dependencies": sorted(
                {
                    str(dependency)
                    for dependency in entry.get("dependencies") or []
                    if str(dependency) in stmt_fps
                }
            ),
            "candidate_hashes": [
                str(item)
                for item in (entry.get("candidate_hashes") or [])[-8:]
                if str(item)
            ],
        }
        for label, entry in (phase1_dependency_observations or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and entry.get("dependencies")
    }
    if diagnostic_evidence is None:
        for label, entry in dependency_observation_payload.items():
            normalized = {
                "schema_version": DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION,
                "label": label,
                "statement_fp": stmt_fps[label],
                "kind": "dependency_reference",
                "lifetime": "statement",
                "plan_fp": "",
                "candidate_fp": "",
                "text": "",
                "data": {
                    "dependencies": list(entry.get("dependencies") or []),
                    "candidate_hashes": list(entry.get("candidate_hashes") or []),
                },
                "sources": ["legacy:phase1_dependency_observations"],
                "consumed": False,
            }
            diagnostic_evidence_payload[
                _diagnostic_evidence_id(normalized)
            ] = normalized
    exchange_payload = {
        str(key): {
            "labels": [str(label) for label in entry.get("labels") or []],
            "statement_fps": {
                str(label): str(fp)
                for label, fp in (entry.get("statement_fps") or {}).items()
            },
            "plan_fps": {
                str(label): str(fp)
                for label, fp in (entry.get("plan_fps") or {}).items()
            },
            "candidate_sha256": str(entry.get("candidate_sha256") or ""),
            "purpose": str(entry.get("purpose") or "")[:100],
            "tier": str(entry.get("tier") or "base")[:40],
            "runner_spec": str(entry.get("runner_spec") or "")[:200],
            "prompt_sha256": str(entry.get("prompt_sha256") or ""),
            "launches": max(1, int(entry.get("launches") or 1)),
            "response_sha256s": [
                str(item) for item in (entry.get("response_sha256s") or [])[-3:]
            ],
            "statuses": [
                str(item)[:40] for item in (entry.get("statuses") or [])[-4:]
            ],
        }
        for key, entry in list((phase1_exchange_history or {}).items())[-512:]
        if isinstance(entry, dict)
        and entry.get("labels")
        and all(
            str(label) in stmt_fps
            and str((entry.get("statement_fps") or {}).get(str(label)) or "")
            == stmt_fps.get(str(label))
            for label in entry.get("labels") or []
        )
    }
    resume_payload = {
        str(key): {
            "runner_spec": str(entry.get("runner_spec") or "")[:200],
            "session_id": str(entry.get("session_id") or "")[:500],
            "labels": [str(label) for label in entry.get("labels") or []],
            "statement_fps": {
                str(label): str(fp)
                for label, fp in (entry.get("statement_fps") or {}).items()
            },
            "plan_fps": {
                str(label): str(fp)
                for label, fp in (entry.get("plan_fps") or {}).items()
            },
            "prompt_sha256": str(entry.get("prompt_sha256") or ""),
        }
        for key, entry in list((model_resume_sessions or {}).items())[-256:]
        if isinstance(entry, dict)
        and str(entry.get("session_id") or "")
        and entry.get("labels")
        and all(
            str(label) in stmt_fps
            and str((entry.get("statement_fps") or {}).get(str(label)) or "")
            == stmt_fps.get(str(label))
            for label in entry.get("labels") or []
        )
    }
    candidate_payload = {
        str(label): {
            "candidate_state_version": int(
                entry.get("candidate_state_version") or 0
            ),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "plan_fp": str(entry.get("plan_fp") or ""),
            "code": str(entry.get("code") or "")[:45000],
            "source": str(entry.get("source") or "unknown"),
            "reusable_uncompiled": _candidate_is_reusable_uncompiled(entry),
            "generation_tier": str(entry.get("generation_tier") or "base"),
            "repair_stage": str(entry.get("repair_stage") or "generated"),
            "imports": [str(item) for item in entry.get("imports") or []],
            "preamble": [str(item) for item in entry.get("preamble") or []],
            "component_labels": [
                str(item) for item in entry.get("component_labels") or [label]
            ],
            "required_dependencies": [
                str(item) for item in entry.get("required_dependencies") or []
            ],
            "candidate_hash": str(
                entry.get("candidate_hash")
                or _candidate_hash(str(entry.get("code") or ""))
            ),
            "deterministic_obligations": [
                str(item) for item in entry.get("deterministic_obligations") or []
            ],
            "satisfied_obligations": [
                str(item) for item in entry.get("satisfied_obligations") or []
            ],
            "deterministic_violations": [
                str(item) for item in entry.get("deterministic_violations") or []
            ],
            "deterministic_findings": [
                str(item)[-4000:]
                for item in entry.get("deterministic_findings") or []
            ],
            "lean_status": str(entry.get("lean_status") or "unknown"),
            "lean_output": str(entry.get("lean_output") or "")[-12000:],
            "lean_output_sha256": str(
                entry.get("lean_output_sha256") or ""
            ),
            "lean_error_count": int(entry.get("lean_error_count") or 0),
            "semantic_status": str(
                entry.get("semantic_status") or "unknown"
            ),
            "semantic_evidence": str(
                entry.get("semantic_evidence") or ""
            )[-12000:],
            "semantic_evidence_sha256": str(
                entry.get("semantic_evidence_sha256") or ""
            ),
            "base_attempted": bool(entry.get("base_attempted")),
            "escalation_attempted": bool(entry.get("escalation_attempted")),
            "revision": int(entry.get("revision") or 1),
            "rejected_transitions": [
                {
                    "candidate_hash": str(item.get("candidate_hash") or ""),
                    "source": str(item.get("source") or "unknown"),
                    "reason": str(item.get("reason") or "unknown"),
                    "regressed": [str(value) for value in item.get("regressed") or []],
                    "improved": [str(value) for value in item.get("improved") or []],
                    "lean_status": str(item.get("lean_status") or "unknown"),
                    "lean_output_sha256": str(
                        item.get("lean_output_sha256") or ""
                    ),
                    "semantic_status": str(
                        item.get("semantic_status") or "unknown"
                    ),
                    "semantic_evidence_sha256": str(
                        item.get("semantic_evidence_sha256") or ""
                    ),
                }
                for item in (entry.get("rejected_transitions") or [])[-12:]
                if isinstance(item, dict)
            ],
            "working_candidate": (
                _working_candidate_payload(entry["working_candidate"])
                if isinstance(entry.get("working_candidate"), dict)
                and str(entry["working_candidate"].get("code") or "").strip()
                else {}
            ),
        }
        for label, entry in (generation_candidates or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and str(entry.get("code") or "").strip()
    }
    phase2_candidate_payload = {
        str(label): {
            "epoch": str(entry.get("epoch") or ""),
            "code": str(entry.get("code") or "")[:60000],
            "candidate_hash": str(entry.get("candidate_hash") or ""),
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "failure_kind": str(entry.get("failure_kind") or "unknown"),
            "failure_hash": str(entry.get("failure_hash") or ""),
            "failure_identity": _canonical_failure_identity(
                entry.get("failure_identity")
                if isinstance(entry.get("failure_identity"), dict)
                else {}
            ),
            "tier": str(entry.get("tier") or "base"),
            "source": str(entry.get("source") or "unknown"),
            "revision": int(entry.get("revision") or 1),
            "seen_states": [
                str(item) for item in (entry.get("seen_states") or [])[-24:]
            ],
            "attempted_corrections": [
                str(item)
                for item in (entry.get("attempted_corrections") or [])[-24:]
            ],
            "repeated_state": bool(entry.get("repeated_state")),
        }
        for label, entry in (phase2_node_candidates or {}).items()
        if label in stmt_fps
        and str(entry.get("epoch") or "")
        and str(entry.get("code") or "").strip()
    }
    lifecycle_payload = {
        str(key): {
            "label": str(entry.get("label") or ""),
            "stage": str(entry.get("stage") or ""),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "state": str(entry.get("state") or "base"),
            "last_tier": str(entry.get("last_tier") or "base"),
            "failures": int(entry.get("failures") or 0),
            "source": str(entry.get("source") or "unknown"),
            "evidence_sha256": str(entry.get("evidence_sha256") or ""),
        }
        for key, entry in (retry_lifecycle or {}).items()
        if str(entry.get("label") or "") in stmt_fps
        and str(entry.get("statement_fp") or "")
        == stmt_fps.get(str(entry.get("label") or ""))
    }
    plan_payload = {}
    for label, entry in (design_plan_entries or {}).items():
        if (
            label not in stmt_fps
            or str(entry.get("statement_fp") or "") != stmt_fps.get(label)
            or int(entry.get("schema_version") or 0) != DESIGN_PLAN_SCHEMA_VERSION
            or not str(entry.get("target_signature") or "").strip()
        ):
            continue
        plan_payload[str(label)] = {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "target_signature": str(entry.get("target_signature") or "")[:12000],
            "helpers": [
                {
                    "name": str(helper.get("name") or "")[:500],
                    "kind": str(helper.get("kind") or "")[:40],
                    "declaration": str(helper.get("declaration") or "")[:12000],
                    "members": [
                        {
                            "name": str(member.get("name") or "")[:500],
                            "type": str(member.get("type") or "")[:4000],
                        }
                        for member in helper.get("members") or []
                        if isinstance(member, dict)
                        and str(member.get("name") or "").strip()
                        and str(member.get("type") or "").strip()
                    ],
                    "required_members": [
                        str(item)[:500]
                        for item in helper.get("required_members") or []
                    ],
                    "purpose": str(helper.get("purpose") or "")[:2000],
                }
                for helper in entry.get("helpers") or []
                if isinstance(helper, dict)
                and str(helper.get("name") or "").strip()
                and str(helper.get("kind") or "").strip()
            ],
            "decisions": [
                str(item)[:4000]
                for item in entry.get("decisions") or []
                if str(item).strip()
            ],
            "audit_fp": str(entry.get("audit_fp") or ""),
            "rejected_audit_fp": str(entry.get("rejected_audit_fp") or ""),
            "rejected_kind": str(entry.get("rejected_kind") or ""),
            "rejected_reason": str(entry.get("rejected_reason") or "")[-12000:],
            "rejected_helpers": [
                str(item)[:2000] for item in entry.get("rejected_helpers") or []
            ],
            "correction_base_fp": str(entry.get("correction_base_fp") or ""),
            "correction_escalation_fp": str(
                entry.get("correction_escalation_fp") or ""
            ),
            "semantic_revision_count": int(
                entry.get("semantic_revision_count") or 0
            ),
            "closure_fp": str(entry.get("closure_fp") or ""),
            "closure_wave_id": str(entry.get("closure_wave_id") or ""),
            "origin": str(entry.get("origin") or ""),
        }
    semantic_plan_payload = {
        str(label): {
            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "representation": str(entry.get("representation") or "")[:600],
            "vocabulary": copy.deepcopy(entry.get("vocabulary") or [])[:8],
            "obligations": [
                str(item)[:320] for item in entry.get("obligations") or []
            ][:6],
            "provider_requirements": copy.deepcopy(
                entry.get("provider_requirements") or []
            ),
            "readiness": str(entry.get("readiness") or "ready"),
            "gap": str(entry.get("gap") or "")[:500],
            "readiness_confirmation": str(
                entry.get("readiness_confirmation") or "not_needed"
            ),
            "readiness_confirmation_reason": str(
                entry.get("readiness_confirmation_reason") or ""
            )[:1000],
            "fallback": bool(entry.get("fallback")),
        }
        for label, entry in (semantic_plan_entries or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and int(entry.get("schema_version") or 0)
        == SEMANTIC_PLAN_SCHEMA_VERSION
    }
    alternate_plan_payload = {
        str(label): {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "target_signature": str(entry.get("target_signature") or "")[:12000],
            "helpers": copy.deepcopy(entry.get("helpers") or []),
            "decisions": [
                str(item)[:4000]
                for item in entry.get("decisions") or []
                if str(item).strip()
            ],
        }
        for label, entry in (design_plan_alternates or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
        and int(entry.get("schema_version") or 0) == DESIGN_PLAN_SCHEMA_VERSION
        and str(entry.get("target_signature") or "").strip()
    }
    direct_generation_payload = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "source": str(entry.get("source") or "unknown")[:200],
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "activations": max(1, int(entry.get("activations") or 1)),
            "previous_interface_fp": str(
                entry.get("previous_interface_fp") or ""
            ),
            "accepted_interface_fp": str(
                entry.get("accepted_interface_fp") or ""
            ),
        }
        for label, entry in (blueprint_direct_generation or {}).items()
        if label in stmt_fps
        and str(entry.get("statement_fp") or "") == stmt_fps.get(label)
    }
    boundary = repair_boundary_pending or {}
    boundary_labels = [
        str(label)
        for label in boundary.get("labels") or []
        if str(label) in stmt_fps
        and str((boundary.get("statement_fps") or {}).get(str(label)) or "")
        == stmt_fps.get(str(label))
    ]
    boundary_payload = (
        {
            "mode": str(boundary.get("mode") or "audit"),
            "labels": boundary_labels,
            "statement_fps": {
                label: stmt_fps[label] for label in boundary_labels
            },
            "previous_statements": {
                label: str((boundary.get("previous_statements") or {}).get(label) or "")[:6000]
                for label in boundary_labels
            },
            "evidence": str(boundary.get("evidence") or "")[-12000:],
            "repair_roots": [
                str(label)
                for label in boundary.get("repair_roots") or []
                if str(label) in stmt_fps
            ],
            "component_changed_labels": [
                str(label)
                for label in boundary.get("component_changed_labels") or []
                if str(label) in stmt_fps
            ],
            "component_added_labels": [
                str(label)
                for label in boundary.get("component_added_labels") or []
                if str(label) in stmt_fps
            ],
            "require_component_closure": bool(
                boundary.get("require_component_closure")
            ),
            "repair_labels": [
                str(label)
                for label in boundary.get("repair_labels") or []
                if str(label) in stmt_fps
            ],
            "required_dependencies": {
                str(label): [
                    str(dep)
                    for dep in dependencies
                    if str(dep) in stmt_fps and str(dep) != str(label)
                ]
                for label, dependencies in (
                    boundary.get("required_dependencies") or {}
                ).items()
                if str(label) in stmt_fps
            },
            "decomposition_helpers": [
                str(item)[:2000]
                for item in boundary.get("decomposition_helpers") or []
                if str(item).strip()
            ],
        }
        if boundary_labels
        else {}
    )
    active_repair = copy.deepcopy(phase2_repair_active or {})
    active_repair_id = str(active_repair.get("request_id") or "")
    phase2_queue_payload = [
        copy.deepcopy(payload)
        for payload in (phase2_repair_queue or [])
        if isinstance(payload, dict)
        and payload.get("request_id")
        and payload.get("labels")
        and (
            str(payload.get("request_id") or "") == active_repair_id
            or all(
                str(label) in stmt_fps
                and (
                    not str(
                        (payload.get("statement_fps") or {}).get(str(label)) or ""
                    )
                    or str(
                        (payload.get("statement_fps") or {}).get(str(label)) or ""
                    )
                    == stmt_fps.get(str(label))
                )
                for label in payload.get("labels") or []
            )
        )
    ]
    persisted_queue_ids = {
        str(payload.get("request_id") or "") for payload in phase2_queue_payload
    }
    active_repair_payload = (
        {
            "request_id": active_repair_id,
            "stage": (
                "verify"
                if str(active_repair.get("stage") or "repair") == "verify"
                else "repair"
            ),
            "labels": [
                str(label)
                for label in active_repair.get("labels") or []
                if str(label) in stmt_fps
            ],
            "verification_labels": [
                str(label)
                for label in active_repair.get("verification_labels") or []
                if str(label) in stmt_fps
            ],
        }
        if active_repair_id in persisted_queue_ids
        else {}
    )

    path = _state_path(name)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(
            {
                "version": 29,
                "refinement_order": refinement_order,
                "conjecture_policy": conjecture_policy,
                "sections": entries,
                "scheduler": {
                    "quarantine": {
                        label: quarantine_payload[label]
                        for label in sorted(quarantine_payload)
                    },
                    "local_group_partitions": {
                        label: local_partition_payload[label]
                        for label in sorted(local_partition_payload)
                    },
                    "effective_section_size": effective_section_size,
                    "generation_feedback": {
                        label: feedback_payload[label]
                        for label in sorted(feedback_payload)
                    },
                    "diagnostic_evidence": {
                        evidence_id: diagnostic_evidence_payload[evidence_id]
                        for evidence_id in sorted(diagnostic_evidence_payload)
                    },
                    "phase1_dependency_observations": {
                        label: dependency_observation_payload[label]
                        for label in sorted(dependency_observation_payload)
                    },
                    "generation_candidates": {
                        label: candidate_payload[label]
                        for label in sorted(candidate_payload)
                    },
                    "phase2_node_candidates": {
                        label: phase2_candidate_payload[label]
                        for label in sorted(phase2_candidate_payload)
                    },
                    "phase1_exchange_history": {
                        key: exchange_payload[key]
                        for key in sorted(exchange_payload)
                    },
                    "model_resume_sessions": {
                        key: resume_payload[key] for key in sorted(resume_payload)
                    },
                    "retry_lifecycle": {
                        key: lifecycle_payload[key]
                        for key in sorted(lifecycle_payload)
                    },
                    "design_plan_entries": {
                        label: plan_payload[label]
                        for label in sorted(plan_payload)
                    },
                    "semantic_plan_entries": {
                        label: semantic_plan_payload[label]
                        for label in sorted(semantic_plan_payload)
                    },
                    "design_plan_alternates": {
                        label: alternate_plan_payload[label]
                        for label in sorted(alternate_plan_payload)
                    },
                    "blueprint_direct_generation": {
                        label: direct_generation_payload[label]
                        for label in sorted(direct_generation_payload)
                    },
                    "repair_boundary_pending": boundary_payload,
                    "phase2_repair_queue": phase2_queue_payload,
                    "phase2_repair_active": active_repair_payload,
                    "workflow": {
                        "phase2_started": bool(phase2_started),
                        "phase1_baseline_labels": sorted(
                            phase1_baseline_labels or set()
                        ),
                        "phase2_prerequisite_labels": sorted(
                            label
                            for label in phase2_prerequisite_labels or set()
                            if label in stmt_fps
                        ),
                    },
                },
            },
            indent=2,
        )
        + "\n",
        encoding="utf-8",
    )


def _save_ctx_state(ctx: Ctx, sections: list[Section]) -> None:
    # A UI stop or outer retry may save while Phase 1 workers are completing.
    # Persist one coherent scheduler snapshot rather than references to mutable
    # dictionaries that can change while JSON payloads are being assembled.
    with _STATE_LOCK:
        _prune_stale_diagnostic_evidence(ctx)
        generation_feedback = copy.deepcopy(
            getattr(ctx, "generation_feedback", {})
        )
        diagnostic_evidence = copy.deepcopy(
            getattr(ctx, "diagnostic_evidence", {})
        )
        phase1_dependency_observations = copy.deepcopy(
            getattr(ctx, "phase1_dependency_observations", {})
        )
        generation_candidates = copy.deepcopy(
            getattr(ctx, "generation_candidates", {})
        )
        phase2_node_candidates = copy.deepcopy(
            getattr(ctx, "phase2_node_candidates", {})
        )
        phase1_exchange_history = copy.deepcopy(
            getattr(ctx, "phase1_exchange_history", {})
        )
        model_resume_sessions = copy.deepcopy(
            getattr(ctx, "model_resume_sessions", {})
        )
    _save_state(
        ctx.name,
        sections,
        ctx.stmt_fps,
        ctx.contract_fps,
        quarantined_labels=ctx.quarantined_labels,
        quarantine=ctx.quarantine,
        local_group_partitions=getattr(ctx, "local_group_partitions", {}),
        generation_feedback=generation_feedback,
        diagnostic_evidence=diagnostic_evidence,
        phase1_dependency_observations=phase1_dependency_observations,
        generation_candidates=generation_candidates,
        phase2_node_candidates=phase2_node_candidates,
        phase1_exchange_history=phase1_exchange_history,
        model_resume_sessions=model_resume_sessions,
        retry_lifecycle=getattr(ctx, "retry_lifecycle", {}),
        design_plan_entries=getattr(ctx, "design_plan_entries", {}),
        semantic_plan_entries=getattr(ctx, "semantic_plan_entries", {}),
        design_plan_alternates=getattr(ctx, "design_plan_alternates", {}),
        blueprint_direct_generation=getattr(
            ctx, "blueprint_direct_generation", {}
        ),
        repair_boundary_pending=getattr(ctx, "repair_boundary_pending", {}),
        phase2_repair_queue=getattr(ctx, "phase2_repair_queue", []),
        phase2_repair_active=getattr(ctx, "phase2_repair_active", {}),
        phase2_prerequisite_labels=set(
            getattr(ctx, "phase2_prerequisite_labels", set())
        ),
        phase2_started=bool(getattr(ctx, "phase2_started", False)),
        phase1_baseline_labels=set(
            getattr(ctx, "phase1_baseline_labels", set())
        ),
        effective_section_size=ctx.effective_section_size,
        refinement_order=ctx.refinement_order,
        conjecture_policy=getattr(ctx, "conjecture_policy", "attempt"),
    )


def _load_state(ctx: Ctx, lean_command: list[str]) -> list[Section]:
    """Resume: keep sections whose file and blueprint contracts are unchanged.

    A section importing a stale module is loaded as deferred when all of its
    own full contracts still match. It cannot count as frozen until imports are
    rebound and Lean recompiles it against regenerated dependencies.
    """
    try:
        payload = json.loads(_state_path(ctx.name).read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return []
    saved_order = str(payload.get("refinement_order") or "top-down")
    if saved_order != ctx.refinement_order:
        _log(
            "resume: discarded generated state because refinement order changed "
            f"from {saved_order} to {ctx.refinement_order}"
        )
        _record(
            ctx.telemetry,
            "resume_state_rejected",
            reason="refinement_order_changed",
            saved_order=saved_order,
            requested_order=ctx.refinement_order,
        )
        return []
    saved_conjecture_policy = str(
        payload.get("conjecture_policy") or "attempt"
    )
    requested_conjecture_policy = getattr(ctx, "conjecture_policy", "attempt")
    if saved_conjecture_policy != requested_conjecture_policy:
        _log(
            "resume: discarded generated state because conjecture policy changed "
            f"from {saved_conjecture_policy} to {requested_conjecture_policy}"
        )
        _record(
            ctx.telemetry,
            "resume_state_rejected",
            reason="conjecture_policy_changed",
            saved_policy=saved_conjecture_policy,
            requested_policy=requested_conjecture_policy,
        )
        return []
    entries = payload.get("sections") or []
    scheduler = payload.get("scheduler") or {}
    workflow = scheduler.get("workflow") or {}
    ctx.phase2_started = bool(workflow.get("phase2_started", False))
    ctx.phase1_baseline_labels = {
        str(label)
        for label in workflow.get("phase1_baseline_labels") or []
    }
    ctx.phase2_prerequisite_labels = {
        str(label)
        for label in workflow.get("phase2_prerequisite_labels") or []
        if str(label) in ctx.nodes
    }
    raw_quarantine = scheduler.get("quarantine") or {}
    ctx.quarantine = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "failure_class": str(entry.get("failure_class") or "unknown"),
        }
        for label, entry in raw_quarantine.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
    }
    ctx.quarantined_labels = set(ctx.quarantine)
    raw_local_partitions = scheduler.get("local_group_partitions") or {}
    ctx.local_group_partitions = {
        str(label): {
            "partition_id": str(entry.get("partition_id") or ""),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "statement_fps": {
                str(item): str(fp)
                for item, fp in (entry.get("statement_fps") or {}).items()
            },
            "group": [str(item) for item in entry.get("group") or []],
        }
        for label, entry in raw_local_partitions.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and all(
            ctx.stmt_fps.get(str(item)) == str(fp)
            for item, fp in (entry.get("statement_fps") or {}).items()
        )
    }
    raw_feedback = scheduler.get("generation_feedback") or {}
    ctx.generation_feedback = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "source": str(entry.get("source") or "unknown"),
        }
        for label, entry in raw_feedback.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and str(entry.get("evidence") or "").strip()
    }
    raw_diagnostic_evidence = scheduler.get("diagnostic_evidence") or {}
    ctx.diagnostic_evidence = {}
    for entry in raw_diagnostic_evidence.values():
        if not isinstance(entry, dict):
            continue
        label = str(entry.get("label") or "")
        lifetime = str(entry.get("lifetime") or "statement")
        normalized = {
            "schema_version": DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION,
            "label": label,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "kind": str(entry.get("kind") or "operational")[:80],
            "lifetime": lifetime,
            "plan_fp": str(entry.get("plan_fp") or "")[:200],
            "candidate_fp": str(entry.get("candidate_fp") or "")[:200],
            "text": str(entry.get("text") or "")[-12000:],
            "data": copy.deepcopy(
                entry.get("data") if isinstance(entry.get("data"), dict) else {}
            ),
            "failure_identity": _canonical_failure_identity(
                entry.get("failure_identity")
                if isinstance(entry.get("failure_identity"), dict)
                else {}
            ),
            "failure_signature": str(entry.get("failure_signature") or ""),
            "sources": [
                str(source)[:200]
                for source in (entry.get("sources") or [])[-8:]
                if str(source)
            ],
            "consumed": False,
        }
        if (
            int(entry.get("schema_version") or 0)
            != DIAGNOSTIC_EVIDENCE_SCHEMA_VERSION
            or label not in ctx.nodes
            or normalized["statement_fp"] != ctx.stmt_fps.get(label)
            or lifetime not in EVIDENCE_LIFETIMES
            or bool(entry.get("consumed"))
            or (not normalized["text"] and not normalized["data"])
        ):
            continue
        ctx.diagnostic_evidence[_diagnostic_evidence_id(normalized)] = normalized
    raw_dependency_observations = (
        scheduler.get("phase1_dependency_observations") or {}
    )
    ctx.phase1_dependency_observations = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "dependencies": sorted(
                {
                    str(dependency)
                    for dependency in entry.get("dependencies") or []
                    if str(dependency) in ctx.nodes
                }
            ),
            "candidate_hashes": [
                str(item)
                for item in (entry.get("candidate_hashes") or [])[-8:]
                if str(item)
            ],
        }
        for label, entry in raw_dependency_observations.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and entry.get("dependencies")
    }
    raw_candidates = scheduler.get("generation_candidates") or {}
    ctx.generation_candidates = {
        str(label): {
            "candidate_state_version": int(
                entry.get("candidate_state_version") or 0
            ),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "plan_fp": str(entry.get("plan_fp") or ""),
            "code": str(entry.get("code") or "")[:45000],
            "source": str(entry.get("source") or "unknown"),
            "reusable_uncompiled": _candidate_is_reusable_uncompiled(entry),
            "generation_tier": str(entry.get("generation_tier") or "base"),
            "repair_stage": str(entry.get("repair_stage") or "generated"),
            "imports": [str(item) for item in entry.get("imports") or []],
            "preamble": [str(item) for item in entry.get("preamble") or []],
            "component_labels": [
                str(item) for item in entry.get("component_labels") or [label]
            ],
            "required_dependencies": [
                str(item) for item in entry.get("required_dependencies") or []
            ],
            "candidate_hash": str(entry.get("candidate_hash") or ""),
            "deterministic_obligations": [
                str(item) for item in entry.get("deterministic_obligations") or []
            ],
            "satisfied_obligations": [
                str(item) for item in entry.get("satisfied_obligations") or []
            ],
            "deterministic_violations": [
                str(item) for item in entry.get("deterministic_violations") or []
            ],
            "deterministic_findings": [
                str(item)[-4000:]
                for item in entry.get("deterministic_findings") or []
            ],
            "lean_status": str(entry.get("lean_status") or "unknown"),
            "lean_output": str(entry.get("lean_output") or "")[-12000:],
            "lean_output_sha256": str(
                entry.get("lean_output_sha256") or ""
            ),
            "lean_error_count": int(entry.get("lean_error_count") or 0),
            "semantic_status": str(
                entry.get("semantic_status") or "unknown"
            ),
            "semantic_evidence": str(
                entry.get("semantic_evidence") or ""
            )[-12000:],
            "semantic_evidence_sha256": str(
                entry.get("semantic_evidence_sha256") or ""
            ),
            "base_attempted": bool(entry.get("base_attempted")),
            "escalation_attempted": bool(entry.get("escalation_attempted")),
            "revision": int(entry.get("revision") or 1),
            "rejected_transitions": [
                dict(item)
                for item in (entry.get("rejected_transitions") or [])[-12:]
                if isinstance(item, dict)
            ],
            "working_candidate": (
                _working_candidate_payload(entry["working_candidate"])
                if isinstance(entry.get("working_candidate"), dict)
                and str(entry["working_candidate"].get("code") or "").strip()
                else {}
            ),
        }
        for label, entry in raw_candidates.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and str(entry.get("code") or "").strip()
    }
    raw_phase2_candidates = scheduler.get("phase2_node_candidates") or {}
    ctx.phase2_node_candidates = {
        str(label): {
            "epoch": str(entry.get("epoch") or ""),
            "code": str(entry.get("code") or "")[:60000],
            "candidate_hash": str(entry.get("candidate_hash") or ""),
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "failure_kind": str(entry.get("failure_kind") or "unknown"),
            "failure_hash": str(entry.get("failure_hash") or ""),
            "failure_identity": _canonical_failure_identity(
                entry.get("failure_identity")
                if isinstance(entry.get("failure_identity"), dict)
                else {}
            ),
            "tier": str(entry.get("tier") or "base"),
            "source": str(entry.get("source") or "unknown"),
            "revision": int(entry.get("revision") or 1),
            "seen_states": [
                str(item) for item in (entry.get("seen_states") or [])[-24:]
            ],
            "attempted_corrections": [
                str(item)
                for item in (entry.get("attempted_corrections") or [])[-24:]
            ],
            "repeated_state": bool(entry.get("repeated_state")),
        }
        for label, entry in raw_phase2_candidates.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("epoch") or "")
        == _phase2_node_candidate_epoch(ctx, str(label))
        and str(entry.get("code") or "").strip()
    }
    raw_lifecycle = scheduler.get("retry_lifecycle") or {}
    ctx.retry_lifecycle = {
        str(key): {
            "label": str(entry.get("label") or ""),
            "stage": str(entry.get("stage") or ""),
            "statement_fp": str(entry.get("statement_fp") or ""),
            "state": str(entry.get("state") or "base"),
            "last_tier": str(entry.get("last_tier") or "base"),
            "failures": int(entry.get("failures") or 0),
            "source": str(entry.get("source") or "unknown"),
            "evidence_sha256": str(entry.get("evidence_sha256") or ""),
        }
        for key, entry in raw_lifecycle.items()
        if isinstance(entry, dict)
        and str(entry.get("label") or "") in ctx.nodes
        and str(entry.get("statement_fp") or "")
        == ctx.stmt_fps.get(str(entry.get("label") or ""))
    }
    raw_boundary = scheduler.get("repair_boundary_pending") or {}
    boundary_labels = [
        str(label)
        for label in raw_boundary.get("labels") or []
        if str(label) in ctx.nodes
        and str((raw_boundary.get("statement_fps") or {}).get(str(label)) or "")
        == ctx.stmt_fps.get(str(label))
    ]
    ctx.repair_boundary_pending = (
        {
            "mode": str(raw_boundary.get("mode") or "audit"),
            "labels": boundary_labels,
            "statement_fps": {
                label: ctx.stmt_fps[label] for label in boundary_labels
            },
            "previous_statements": {
                label: str((raw_boundary.get("previous_statements") or {}).get(label) or "")[:6000]
                for label in boundary_labels
            },
            "evidence": str(raw_boundary.get("evidence") or "")[-12000:],
            "repair_roots": [
                str(label)
                for label in raw_boundary.get("repair_roots") or []
                if str(label) in ctx.nodes
            ],
            "component_changed_labels": [
                str(label)
                for label in raw_boundary.get("component_changed_labels") or []
                if str(label) in ctx.nodes
            ],
            "component_added_labels": [
                str(label)
                for label in raw_boundary.get("component_added_labels") or []
                if str(label) in ctx.nodes
            ],
            "require_component_closure": bool(
                raw_boundary.get("require_component_closure")
            ),
            "repair_labels": [
                str(label)
                for label in raw_boundary.get("repair_labels") or []
                if str(label) in ctx.nodes
            ],
            "required_dependencies": {
                str(label): {
                    str(dep)
                    for dep in dependencies
                    if str(dep) in ctx.nodes and str(dep) != str(label)
                }
                for label, dependencies in (
                    raw_boundary.get("required_dependencies") or {}
                ).items()
                if str(label) in ctx.nodes
            },
            "decomposition_helpers": [
                str(item)[:2000]
                for item in raw_boundary.get("decomposition_helpers") or []
                if str(item).strip()
            ],
        }
        if boundary_labels
        else {}
    )
    raw_phase2_queue = scheduler.get("phase2_repair_queue") or []
    ctx.phase2_repair_queue = [
        copy.deepcopy(payload)
        for payload in raw_phase2_queue
        if isinstance(payload, dict)
    ]
    raw_phase2_active = scheduler.get("phase2_repair_active") or {}
    active_id = str(raw_phase2_active.get("request_id") or "")
    queued_ids = {
        str(payload.get("request_id") or "")
        for payload in ctx.phase2_repair_queue
    }
    ctx.phase2_repair_active = (
        {
            "request_id": active_id,
            "stage": (
                "verify"
                if str(raw_phase2_active.get("stage") or "repair") == "verify"
                else "repair"
            ),
            "labels": [
                str(label)
                for label in raw_phase2_active.get("labels") or []
                if str(label) in ctx.nodes
            ],
            "verification_labels": [
                str(label)
                for label in raw_phase2_active.get("verification_labels") or []
                if str(label) in ctx.nodes
            ],
        }
        if active_id and active_id in queued_ids
        else {}
    )
    _prune_stale_phase2_repair_queue(ctx)
    raw_plan = scheduler.get("design_plan_entries") or {}
    ctx.design_plan_entries = {
        str(label): {
            "schema_version": DESIGN_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "target_signature": str(entry.get("target_signature") or "")[:12000],
            "helpers": [
                {
                    "name": str(helper.get("name") or "")[:500],
                    "kind": str(helper.get("kind") or "")[:40],
                    "declaration": str(helper.get("declaration") or "")[:12000],
                    "members": [
                        {
                            "name": str(member.get("name") or "")[:500],
                            "type": str(member.get("type") or "")[:4000],
                        }
                        for member in helper.get("members") or []
                        if isinstance(member, dict)
                        and str(member.get("name") or "").strip()
                        and str(member.get("type") or "").strip()
                    ],
                    "required_members": [
                        str(item)[:500]
                        for item in helper.get("required_members") or []
                    ],
                    "purpose": str(helper.get("purpose") or "")[:2000],
                }
                for helper in entry.get("helpers") or []
                if isinstance(helper, dict)
                and str(helper.get("name") or "").strip()
                and str(helper.get("kind") or "").strip()
            ],
            "decisions": [
                str(item)[:4000]
                for item in entry.get("decisions") or []
                if str(item).strip()
            ],
            "audit_fp": str(entry.get("audit_fp") or ""),
            "rejected_audit_fp": str(entry.get("rejected_audit_fp") or ""),
            "rejected_kind": str(entry.get("rejected_kind") or ""),
            "rejected_reason": str(entry.get("rejected_reason") or "")[-12000:],
            "rejected_helpers": [
                str(item)[:2000] for item in entry.get("rejected_helpers") or []
            ],
            "correction_base_fp": str(entry.get("correction_base_fp") or ""),
            "correction_escalation_fp": str(
                entry.get("correction_escalation_fp") or ""
            ),
            "semantic_revision_count": int(
                entry.get("semantic_revision_count") or 0
            ),
            "closure_fp": str(entry.get("closure_fp") or ""),
            "closure_wave_id": str(entry.get("closure_wave_id") or ""),
            "origin": str(entry.get("origin") or ""),
        }
        for label, entry in raw_plan.items()
        if isinstance(entry, dict)
        and int(entry.get("schema_version") or 0) == DESIGN_PLAN_SCHEMA_VERSION
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "") == ctx.stmt_fps.get(str(label))
        and str(entry.get("target_signature") or "").strip()
    }
    raw_semantic_plan = scheduler.get("semantic_plan_entries") or {}
    ctx.semantic_plan_entries = {
        str(label): {
            "schema_version": SEMANTIC_PLAN_SCHEMA_VERSION,
            "statement_fp": str(entry.get("statement_fp") or ""),
            "representation": str(entry.get("representation") or "")[:600],
            "vocabulary": [
                {
                    "name": str(item.get("name") or "")[:500],
                    "purpose": str(item.get("purpose") or "")[:240],
                }
                for item in entry.get("vocabulary") or []
                if isinstance(item, dict)
                and str(item.get("name") or "").strip()
            ][:8],
            "obligations": [
                str(item)[:320]
                for item in entry.get("obligations") or []
                if str(item).strip()
            ][:6],
            "provider_requirements": [
                {
                    "provider": str(item.get("provider") or ""),
                    "capabilities": [
                        str(value)[:240]
                        for value in item.get("capabilities") or []
                        if str(value).strip()
                    ][:8],
                }
                for item in entry.get("provider_requirements") or []
                if isinstance(item, dict)
                and str(item.get("provider") or "")
                in _statement_uses(ctx.nodes[str(label)])
            ],
            "readiness": (
                str(entry.get("readiness") or "ready")
                if str(entry.get("readiness") or "ready")
                in SEMANTIC_READINESS_VALUES
                else "ready"
            ),
            "gap": str(entry.get("gap") or "")[:500],
            "readiness_confirmation": str(
                entry.get("readiness_confirmation") or "not_needed"
            ),
            "readiness_confirmation_reason": str(
                entry.get("readiness_confirmation_reason") or ""
            )[:1000],
            "fallback": bool(entry.get("fallback")),
        }
        for label, entry in raw_semantic_plan.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and int(entry.get("schema_version") or 0)
        == SEMANTIC_PLAN_SCHEMA_VERSION
        and str(entry.get("statement_fp") or "")
        == ctx.stmt_fps.get(str(label))
    }
    raw_alternates = scheduler.get("design_plan_alternates") or {}
    ctx.design_plan_alternates = _parse_design_plan_entries(
        ctx,
        raw_alternates,
        json.dumps(
            {
                "contracts": [
                    {
                        "label": str(label),
                        "target_signature": str(entry.get("target_signature") or ""),
                        "helpers": entry.get("helpers") or [],
                        "decisions": entry.get("decisions") or [],
                    }
                    for label, entry in raw_alternates.items()
                    if isinstance(entry, dict)
                    and int(entry.get("schema_version") or 0)
                    == DESIGN_PLAN_SCHEMA_VERSION
                    and str(entry.get("statement_fp") or "")
                    == ctx.stmt_fps.get(str(label))
                ]
            }
        ),
    )
    raw_direct_generation = scheduler.get("blueprint_direct_generation") or {}
    ctx.blueprint_direct_generation = {
        str(label): {
            "statement_fp": str(entry.get("statement_fp") or ""),
            "source": str(entry.get("source") or "unknown")[:200],
            "evidence": str(entry.get("evidence") or "")[-12000:],
            "activations": max(1, int(entry.get("activations") or 1)),
            "previous_interface_fp": str(
                entry.get("previous_interface_fp") or ""
            ),
            "accepted_interface_fp": str(
                entry.get("accepted_interface_fp") or ""
            ),
        }
        for label, entry in raw_direct_generation.items()
        if isinstance(entry, dict)
        and str(label) in ctx.nodes
        and str(entry.get("statement_fp") or "")
        == ctx.stmt_fps.get(str(label))
    }
    _sync_design_plan(ctx)
    # Candidate and plan lifetimes can only be checked after all scheduler
    # objects are restored. Migrate version-28 compatibility stores here, then
    # make the typed ledger authoritative for prompt feedback.
    _migrate_legacy_generation_feedback(ctx)
    for label, entry in ctx.phase1_dependency_observations.items():
        _record_diagnostic_evidence(
            ctx,
            label,
            "",
            source="legacy:phase1_dependency_observations",
            kind="dependency_reference",
            lifetime="statement",
            data={
                "dependencies": list(entry.get("dependencies") or []),
                "candidate_hashes": list(entry.get("candidate_hashes") or []),
            },
        )
    _prune_stale_diagnostic_evidence(ctx)
    _sync_generation_feedback_projection(ctx)
    raw_exchange_history = scheduler.get("phase1_exchange_history") or {}
    ctx.phase1_exchange_history = {
        str(key): {
            "labels": [str(label) for label in entry.get("labels") or []],
            "statement_fps": {
                str(label): str(fp)
                for label, fp in (entry.get("statement_fps") or {}).items()
            },
            "plan_fps": {
                str(label): str(fp)
                for label, fp in (entry.get("plan_fps") or {}).items()
            },
            "candidate_sha256": str(entry.get("candidate_sha256") or ""),
            "purpose": str(entry.get("purpose") or ""),
            "tier": str(entry.get("tier") or "base"),
            "runner_spec": str(entry.get("runner_spec") or ""),
            "prompt_sha256": str(entry.get("prompt_sha256") or ""),
            "launches": max(1, int(entry.get("launches") or 1)),
            "response_sha256s": [
                str(item) for item in (entry.get("response_sha256s") or [])[-3:]
            ],
            "statuses": [
                str(item) for item in (entry.get("statuses") or [])[-4:]
            ],
        }
        for key, entry in raw_exchange_history.items()
        if isinstance(entry, dict)
        and entry.get("labels")
    }
    _prune_stale_phase1_exchange_history(ctx)
    raw_resume_sessions = scheduler.get("model_resume_sessions") or {}
    ctx.model_resume_sessions = {
        str(key): {
            "runner_spec": str(entry.get("runner_spec") or ""),
            "session_id": str(entry.get("session_id") or ""),
            "labels": [str(label) for label in entry.get("labels") or []],
            "statement_fps": {
                str(label): str(fp)
                for label, fp in (entry.get("statement_fps") or {}).items()
            },
            "plan_fps": {
                str(label): str(fp)
                for label, fp in (entry.get("plan_fps") or {}).items()
            },
            "prompt_sha256": str(entry.get("prompt_sha256") or ""),
        }
        for key, entry in raw_resume_sessions.items()
        if isinstance(entry, dict)
        and str(entry.get("session_id") or "")
        and entry.get("labels")
    }
    _prune_stale_model_resume_sessions(ctx)
    legacy_quarantine = {
        str(label)
        for label in scheduler.get("quarantined_labels") or []
        if str(label) in ctx.nodes
    }
    if legacy_quarantine:
        # Version-2 state did not identify which statement version failed.
        # Reusing it after blueprint repairs is precisely what caused resumed
        # runs to degrade into one model call per node, so migrate by dropping
        # it rather than guessing.
        telemetry = getattr(ctx, "telemetry", None)
        if telemetry is not None:
            _record(
                telemetry,
                "skeleton_quarantine_released",
                labels=sorted(legacy_quarantine),
                reason="legacy_state_missing_statement_fingerprint",
            )
    saved_size = int(scheduler.get("effective_section_size") or 0)
    if saved_size > 0:
        ctx.effective_section_size = min(ctx.section_size, saved_size)
    generated_dir = _generated_module_dir(ctx.name)

    kept: list[Section] = []
    dropped_labels: set[str] = set()
    dropped_modules: set[str] = set()
    duplicate_sections: list[dict[str, Any]] = []
    for entry in entries:
        path = generated_dir / str(entry.get("file") or "")
        labels = [str(label) for label in entry.get("labels") or []]
        entry_deferred = bool(entry.get("deferred", False))
        entry_provisional = bool(entry.get("provisional_environment", False))
        # A pre-v36 Phase-2 prerequisite bug could publish a frozen definition
        # again in a later section. Each canonical blueprint label has exactly
        # one active owner; retaining both modules makes every downstream import
        # fail with ``environment already contains``. Keep the earliest valid
        # owner and discard the whole later transaction. Any non-duplicate
        # labels that happened to share that transaction become pending again,
        # while importers are deferred below through ``dropped_modules``.
        active_owners = {
            label: section
            for section in kept
            if not section.provisional_environment
            for label in section.labels
        }
        duplicate_labels = (
            set(labels) & set(active_owners)
            if not entry_provisional
            else set()
        )
        if duplicate_labels:
            unique_labels = set(labels) - duplicate_labels
            dropped_labels.update(unique_labels)
            dropped_module = str(entry.get("module") or "")
            if dropped_module:
                dropped_modules.add(dropped_module)
            _discard_section_artifacts(path)
            migration = {
                "file": path.name,
                "module": dropped_module,
                "duplicate_labels": sorted(duplicate_labels),
                "rescheduled_labels": sorted(unique_labels),
                "retained_owners": {
                    label: active_owners[label].file_name
                    for label in sorted(duplicate_labels)
                },
            }
            duplicate_sections.append(migration)
            _record(
                ctx.telemetry,
                "resume_duplicate_section_discarded",
                **migration,
            )
            continue
        stmt_fps = entry.get("statement_fps") or {}
        contract_fps = entry.get("contract_fps") or {}
        own_contracts_ok = (
            path.is_file()
            and labels
            and all(
                label in ctx.nodes
                and ctx.stmt_fps.get(label) == stmt_fps.get(label)
                and ctx.contract_fps.get(label) == contract_fps.get(label)
                for label in labels
            )
        )
        dependency_stale = any(
            dep in dropped_modules for dep in entry.get("import_modules") or []
        )
        if own_contracts_ok and dropped_labels:
            invalidated = (
                _dependency_descendants(ctx.nodes, dropped_labels) - dropped_labels
            )
            dependency_stale = dependency_stale or bool(set(labels) & invalidated)
        if own_contracts_ok and dependency_stale:
            # This section's own contract is still current. Preserve its source
            # as deferred cache even though an imported dependency was dropped.
            entry_deferred = True
        ok = own_contracts_ok
        if (
            ok
            and entry_deferred
            and _section_exact_source_fingerprint(path) != entry.get("sha256")
        ):
            # Deferred code is not accepted and cannot be semantically audited
            # from state alone. A modified cache candidate is regenerated.
            ok = False
        if (
            ok
            and not entry_deferred
            and _section_exact_source_fingerprint(path) != entry.get("sha256")
        ):
            # The file changed after the last state save (e.g. proofs were
            # spliced right before a crash). The full blueprint contracts still
            # match, so salvage instead of discarding: all labels must still
            # have declarations and the module must recompile.
            code = path.read_text(encoding="utf-8")
            decls = _lean_declarations(code)
            ok = all(_lean_name(label) in decls for label in labels)
            if ok and not entry_provisional:
                ok, _output = _check_lean(path, lean_command)
            if ok:
                detail = (
                    "name-complete provisional boilerplate"
                    if entry_provisional
                    else "recompiled clean"
                )
                _log(f"resume: salvaged modified section {path.name} ({detail})")
        if not ok:
            dropped_labels.update(labels)
            dropped_modules.add(str(entry.get("module") or ""))
            _discard_section_artifacts(path)
            continue
        sec = Section(
            number=int(entry.get("number") or 0),
            labels=labels,
            path=path,
            module=str(entry.get("module") or ""),
            import_modules=[str(m) for m in entry.get("import_modules") or []],
            deferred=entry_deferred,
            refined_labels=(
                {str(label) for label in entry.get("refined_labels") or []}
                if "refined_labels" in entry
                and entry.get("refined_labels") is not None
                else None
            ),
            provisional_environment=entry_provisional,
            generation_tier=str(entry.get("generation_tier") or "unknown"),
            compile_fingerprint=str(entry.get("compile_fingerprint") or ""),
        )
        if sec.deferred:
            _discard_section_objects(path)
        elif (
            not sec.provisional_environment
            and (
                not path.with_suffix(".olean").is_file()
                or not _lake_olean_path(path).is_file()
            )
        ):
            attempt = _compile_section_olean(sec, lean_command, kept)
            if not attempt.ok:
                dropped_labels.update(labels)
                dropped_modules.add(sec.module)
                _discard_section_artifacts(path)
                continue
        elif not sec.provisional_environment and not sec.compile_fingerprint:
            _mark_section_compiled(sec, lean_command, kept)
        kept.append(sec)
    migrated_fingerprints = _migrate_section_compile_fingerprints(
        kept, lean_command
    )
    if migrated_fingerprints:
        _log(
            "resume: migrated "
            f"{migrated_fingerprints} object fingerprint(s) without rebuilding"
        )
        _record(
            ctx.telemetry,
            "section_object_fingerprint_migration",
            migrated_modules=migrated_fingerprints,
            rebuilt_modules=0,
        )
    if dropped_labels:
        _log(f"resume: dropped {len(dropped_labels)} stale label(s); kept {len(kept)} section(s)")
    if duplicate_sections:
        _log(
            "resume: removed "
            f"{len(duplicate_sections)} duplicate declaration section(s); "
            "retained each label's original owning section"
        )
    if not workflow and kept:
        implemented, _required = _phase2_body_progress(ctx, kept)
        if implemented:
            # State written before version 23 had no explicit workflow phase.
            # A completed body proves that Phase 2 had already started; infer
            # the one-way milestone rather than reopening Phase 1 on resume.
            ctx.phase2_started = True
            ctx.phase1_baseline_labels = {
                label for label, node in ctx.nodes.items() if not node.mathlibok
            }
    if duplicate_sections:
        # Persist the migration immediately. A second interrupted --continue
        # must not rediscover state entries whose generated files were removed.
        _save_ctx_state(ctx, kept)
    return kept


def _prune_stale_generated(ctx: Ctx, kept: list[Section]) -> None:
    """Remove generated Lean artifacts not owned by a kept section.

    Fresh runs rmtree the generated dir; this is the ``--continue`` analog.
    Stale files are actively harmful, not just clutter: agent runners glob the
    generated dir and mine old implementations (e.g. legacy ChunkNN modules
    from the per-chunk pipeline) whose statements predate blueprint repairs —
    burning call budget on exploration and risking stale formulations being
    copied into new sections. Only the pipeline's own artifact patterns are
    touched; anything else in the directory is left alone.
    """
    generated_dir = _generated_module_dir(ctx.name)
    owned = {sec.path.resolve() for sec in kept}
    owned |= {sec.path.with_suffix(".olean").resolve() for sec in kept}
    owned_lake = {_lake_olean_path(sec.path).resolve() for sec in kept}
    removed: list[str] = []
    if generated_dir.is_dir():
        for pattern in ("Chunk*.lean", "Chunk*.olean", "Skeleton*.lean", "Skeleton*.olean"):
            for artifact in sorted(generated_dir.glob(pattern)):
                if artifact.resolve() in owned:
                    continue
                if artifact.suffix == ".lean":
                    _discard_section_artifacts(artifact)
                else:
                    with contextlib.suppress(FileNotFoundError, OSError):
                        artifact.unlink()
                removed.append(artifact.name)
    lake_dir = _generated_lake_module_dir(ctx.name)
    if lake_dir.is_dir():
        for pattern in ("Chunk*.olean", "Skeleton*.olean"):
            for artifact in sorted(lake_dir.glob(pattern)):
                if artifact.resolve() in owned_lake:
                    continue
                with contextlib.suppress(FileNotFoundError, OSError):
                    artifact.unlink()
                    removed.append(f"lake-build/{artifact.name}")
    if removed:
        _log(
            f"pruned {len(removed)} stale generated artifact(s): "
            + ", ".join(removed[:8])
            + ("..." if len(removed) > 8 else "")
        )
        _record(
            ctx.telemetry,
            "stale_artifacts_pruned",
            count=len(removed),
            files=removed,
        )
