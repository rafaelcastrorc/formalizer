"""Append-only telemetry for later classifier training.

Telemetry is intentionally raw-observation oriented: it records what the
pipeline knew, what it tried, and what happened. It does not assign guessed
"confidence" labels during collection. Dataset builders can derive labels later
from these events.

All data is stored locally under ``.auto-blueprint/telemetry/`` and ignored by
Git. If ``AUTO_BLUEPRINT_TELEMETRY_URL`` is set, events/artifacts are also
queued for best-effort upload to a shared collector. Upload failure never fails
the refinement run.
"""
from __future__ import annotations

import base64
import hashlib
import json
import os
import re
import subprocess
import time
import uuid
import urllib.error
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _json_default(value: object) -> object:
    if isinstance(value, Path):
        return str(value)
    if isinstance(value, set):
        return sorted(value)
    return str(value)


def _safe_name(value: str) -> str:
    return "".join(ch if ch.isalnum() or ch in "._-" else "-" for ch in value)[:120]


def _git_commit(repo_root: Path) -> str:
    try:
        proc = subprocess.run(
            ["git", "rev-parse", "HEAD"],
            cwd=str(repo_root),
            capture_output=True,
            text=True,
            timeout=5,
        )
    except Exception:  # noqa: BLE001 - telemetry must never block execution
        return ""
    return proc.stdout.strip() if proc.returncode == 0 else ""


@dataclass
class StoredArtifact:
    kind: str
    sha256: str
    path: Path
    chars: int

    def to_event(self, repo_root: Path) -> dict[str, Any]:
        try:
            rel = self.path.relative_to(repo_root)
        except ValueError:
            rel = self.path
        return {
            "kind": self.kind,
            "sha256": self.sha256,
            "path": str(rel),
            "chars": self.chars,
        }


class TelemetryRun:
    """One append-only telemetry stream for a refinement run."""

    def __init__(
        self,
        repo_root: Path,
        *,
        blueprint: str,
        command: list[str],
        enabled: bool = True,
    ):
        self.repo_root = repo_root
        self.enabled = enabled and os.environ.get("AUTO_BLUEPRINT_TELEMETRY", "1") != "0"
        self.blueprint = blueprint
        stamp = time.strftime("%Y%m%d-%H%M%S")
        self.run_id = f"{stamp}-{uuid.uuid4().hex[:8]}"
        self.project = os.environ.get("AUTO_BLUEPRINT_TELEMETRY_PROJECT", "auto-blueprint")
        self.root = repo_root / ".auto-blueprint" / "telemetry"
        self.runs_dir = self.root / "runs"
        self.artifacts_dir = self.root / "artifacts"
        self.queue_dir = self.root / "upload_queue" / self.run_id
        self.run_path = self.runs_dir / f"{self.run_id}.jsonl"
        self.upload_url = os.environ.get("AUTO_BLUEPRINT_TELEMETRY_URL", "").strip()
        self.upload_token = os.environ.get("AUTO_BLUEPRINT_TELEMETRY_TOKEN", "").strip()
        self.seq = 0

        if self.enabled:
            try:
                self.runs_dir.mkdir(parents=True, exist_ok=True)
                self.artifacts_dir.mkdir(parents=True, exist_ok=True)
            except OSError:
                self.enabled = False
                return
            self.record(
                "run_start",
                blueprint=blueprint,
                command=command,
                git_commit=_git_commit(repo_root),
                upload_configured=bool(self.upload_url),
            )

    def _queue(self, envelope: dict[str, Any]) -> None:
        if not self.upload_url:
            return
        try:
            self.queue_dir.mkdir(parents=True, exist_ok=True)
            queue_path = self.queue_dir / f"{self.seq:08d}-{uuid.uuid4().hex}.json"
            queue_path.write_text(
                json.dumps(envelope, ensure_ascii=False, default=_json_default) + "\n",
                encoding="utf-8",
            )
        except OSError:
            return

    def record(self, event: str, **fields: Any) -> dict[str, Any]:
        if not self.enabled:
            return {}
        self.seq += 1
        payload: dict[str, Any] = {
            "event": event,
            "run_id": self.run_id,
            "seq": self.seq,
            "project": self.project,
            "blueprint": self.blueprint,
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            **fields,
        }
        line = json.dumps(payload, ensure_ascii=False, default=_json_default)
        try:
            with self.run_path.open("a", encoding="utf-8") as fh:
                fh.write(line + "\n")
        except OSError:
            return payload
        self._queue({"kind": "event", "payload": payload})
        if event in {
            "model_call",
            "lean_attempt",
            "statement_audit",
            "blueprint_repair_applied",
            "blueprint_repair_noop",
            "run_end",
        }:
            self.flush_upload_queue(max_items=50, timeout=2.0)
        return payload

    def store_text(self, kind: str, text: str, *, ext: str = "txt") -> StoredArtifact:
        digest = sha256_text(text)
        safe_kind = _safe_name(kind)
        path = self.artifacts_dir / safe_kind / f"{digest}.{ext.lstrip('.')}"
        if self.enabled:
            try:
                path.parent.mkdir(parents=True, exist_ok=True)
                if not path.exists():
                    path.write_text(text, encoding="utf-8")
                self._queue(
                    {
                        "kind": "artifact",
                        "project": self.project,
                        "run_id": self.run_id,
                        "artifact_kind": safe_kind,
                        "sha256": digest,
                        "chars": len(text),
                        "encoding": "utf-8",
                        "content_b64": base64.b64encode(text.encode("utf-8")).decode("ascii"),
                    }
                )
            except OSError:
                pass
        return StoredArtifact(kind=safe_kind, sha256=digest, path=path, chars=len(text))

    def flush_upload_queue(self, *, max_items: int = 200, timeout: float = 3.0) -> None:
        """Best-effort upload. Never raises and never deletes local telemetry."""
        if not self.enabled or not self.upload_url or not self.queue_dir.is_dir():
            return
        headers = {"Content-Type": "application/json"}
        if self.upload_token:
            headers["Authorization"] = f"Bearer {self.upload_token}"
        for path in sorted(self.queue_dir.glob("*.json"))[:max_items]:
            try:
                data = path.read_bytes()
                req = urllib.request.Request(
                    self.upload_url,
                    data=data,
                    headers=headers,
                    method="POST",
                )
                with urllib.request.urlopen(req, timeout=timeout):
                    pass
                uploaded = path.with_suffix(".uploaded")
                path.rename(uploaded)
            except (OSError, urllib.error.URLError, TimeoutError):
                return


def node_structural_features(label: str, kind: str, text: str, uses_count: int) -> dict[str, Any]:
    """Generic text/graph features available before a routing decision."""
    proof_match = re.search(r"\\begin\{proof\}(.*?)\\end\{proof\}", text, flags=re.DOTALL)
    proof_text = proof_match.group(1) if proof_match else ""
    lowered = text.lower()
    return {
        "label": label,
        "kind": kind,
        "text_sha256": sha256_text(text),
        "text_chars": len(text),
        "proof_chars": len(proof_text),
        "uses_count": uses_count,
        "display_math_count": text.count(r"\[") + text.count("$$"),
        "equation_like_count": text.count("=") + text.count(r"\le") + text.count(r"\ge"),
        "ref_count": text.count(r"\ref{"),
        "paragraph_count": len([p for p in text.split("\n\n") if p.strip()]),
        "item_count": text.count(r"\item"),
        "lean_name_mentions": text.count("`"),
        "sum_token_count": text.count(r"\sum") + text.count("∑"),
        "product_token_count": text.count(r"\prod") + text.count("∏"),
        "forall_token_count": text.count(r"\forall") + text.count("∀"),
        "exists_token_count": text.count(r"\exists") + text.count("∃"),
        "inequality_token_count": (
            text.count(r"\le")
            + text.count(r"\ge")
            + text.count(r"<")
            + text.count(r">")
            + text.count("≤")
            + text.count("≥")
        ),
        "matrix_token_count": lowered.count("matrix") + text.count(r"\mat"),
        "continuity_token_count": lowered.count("continuous") + lowered.count("continuity"),
        "reindex_token_count": lowered.count("reindex") + lowered.count("bijection"),
        "induction_token_count": lowered.count("induction") + lowered.count("base case"),
        "construction_token_count": lowered.count("construct") + lowered.count("define"),
        "asymptotic_token_count": (
            lowered.count("runtime")
            + lowered.count("time")
            + lowered.count("complexity")
            + text.count(r"\bigO")
            + text.count(r"O(")
        ),
    }
