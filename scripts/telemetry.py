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
import argparse
import hashlib
import json
import os
import re
import subprocess
import time
import uuid
import urllib.error
import urllib.parse
import urllib.request
from dataclasses import dataclass
from pathlib import Path
from typing import Any


# Keep client payloads comfortably below the Worker limit. The Worker stores raw
# JSON envelopes in R2, so the client owns keeping every envelope uploadable.
MAX_UPLOAD_BODY_BYTES = 8 * 1024 * 1024
ARTIFACT_CHUNK_BYTES = 512 * 1024


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
                upload_target=_upload_target_fingerprint(self.upload_url, self.upload_token),
            )

    def _queue(self, envelope: dict[str, Any]) -> None:
        if not self.upload_url:
            return
        try:
            self.queue_dir.mkdir(parents=True, exist_ok=True)
            _write_queue_envelope(self.queue_dir, self.seq, envelope)
        except OSError:
            return

    def record(self, event: str, **fields: Any) -> dict[str, Any]:
        if not self.enabled:
            return {}
        self.seq += 1
        reserved = {"event", "run_id", "seq", "project", "blueprint", "timestamp"}
        safe_fields = {
            (f"{key}_data" if key in reserved else key): value
            for key, value in fields.items()
        }
        payload: dict[str, Any] = {
            "event": event,
            "run_id": self.run_id,
            "seq": self.seq,
            "project": self.project,
            "blueprint": self.blueprint,
            "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            **safe_fields,
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
            "blueprint_repair_result",
            "repair_invalidation",
            "proof_frontier_result",
            "pipeline_progress",
            "skeleton_audit_patch",
            "adaptive_section_size",
            "skeleton_refusal_isolated",
            "skeleton_refusal_rejected",
            "skeleton_compile_stagnation",
            "skeleton_semantic_stagnation",
            "duplicate_model_exchange",
            "singleton_compile_escalation",
            "partial_sections_preserved",
            "blueprint_repair_scope",
            "deferred_section_recheck",
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
                self._queue_artifact(safe_kind, digest, text)
            except OSError:
                pass
        return StoredArtifact(kind=safe_kind, sha256=digest, path=path, chars=len(text))

    def _queue_artifact(self, safe_kind: str, digest: str, text: str) -> None:
        if not self.upload_url:
            return
        raw = text.encode("utf-8")
        chunks = [
            raw[i : i + ARTIFACT_CHUNK_BYTES]
            for i in range(0, len(raw), ARTIFACT_CHUNK_BYTES)
        ] or [b""]
        for index, chunk in enumerate(chunks):
            self._queue(
                {
                    "kind": "artifact",
                    "project": self.project,
                    "blueprint": self.blueprint,
                    "run_id": self.run_id,
                    "artifact_kind": safe_kind,
                    "sha256": digest,
                    "chars": len(text),
                    "encoding": "utf-8",
                    "chunked": len(chunks) > 1,
                    "chunk_index": index,
                    "chunk_count": len(chunks),
                    "content_b64": base64.b64encode(chunk).decode("ascii"),
                }
            )

    def flush_upload_queue(self, *, max_items: int = 200, timeout: float = 3.0) -> None:
        """Best-effort upload. Never raises and never deletes local telemetry.

        Uploads are transport-retryable. A schema/payload problem should be a
        code bug, not an unuploadable data class, so payloads are bounded before
        queueing and HTTP failures are logged while the original JSON stays
        pending for a later fixed client/collector.
        """
        if not self.enabled or not self.upload_url:
            return
        flush_upload_queues(
            self.root,
            upload_url=self.upload_url,
            upload_token=self.upload_token,
            max_items=max_items,
            timeout=timeout,
        )


def _upload_target_fingerprint(upload_url: str, upload_token: str) -> dict[str, str | bool]:
    if not upload_url:
        target = ""
    else:
        try:
            parsed = urllib.parse.urlparse(upload_url)
            target = f"{parsed.scheme}://{parsed.netloc}{parsed.path}"
        except Exception:  # noqa: BLE001 - telemetry should not fail run startup
            target = upload_url
    return {
        "url": target,
        "token_set": bool(upload_token),
        "token_sha256_prefix": hashlib.sha256(upload_token.encode("utf-8")).hexdigest()[:12]
        if upload_token
        else "",
    }


def _envelope_bytes(envelope: dict[str, Any]) -> bytes:
    return (json.dumps(envelope, ensure_ascii=False, default=_json_default) + "\n").encode("utf-8")


def _write_queue_envelope(queue_dir: Path, seq: int, envelope: dict[str, Any]) -> Path:
    data = _envelope_bytes(envelope)
    if len(data) > MAX_UPLOAD_BODY_BYTES:
        raise OSError(
            f"telemetry envelope is {len(data)} bytes after chunking; "
            f"limit is {MAX_UPLOAD_BODY_BYTES}"
        )
    queue_path = queue_dir / f"{seq:08d}-{uuid.uuid4().hex}.json"
    queue_path.write_bytes(data)
    return queue_path


def _append_upload_error(root: Path, path: Path, error: str) -> None:
    error_path = root / "upload_errors.jsonl"
    payload = {
        "timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "path": str(path),
        "error": error,
    }
    try:
        with error_path.open("a", encoding="utf-8") as fh:
            fh.write(json.dumps(payload, ensure_ascii=False) + "\n")
    except OSError:
        pass


def _uploaded_path(path: Path) -> Path:
    return path.with_suffix(".uploaded")


def _reuploaded_path(path: Path) -> Path:
    return path.with_suffix(".reuploaded")


def _blueprints_by_run_id(telemetry_root: Path) -> dict[str, str]:
    """Recover blueprint names for old queued artifact envelopes.

    Early artifact upload envelopes did not include ``blueprint`` at the top
    level even though the corresponding run JSONL did. Before uploading older
    queues, backfill that field from the run_start/refine_config events so all
    records land under the real blueprint prefix in shared storage.
    """
    mapping: dict[str, str] = {}
    for run_path in (telemetry_root / "runs").glob("*.jsonl"):
        try:
            with run_path.open(encoding="utf-8") as fh:
                for line in fh:
                    try:
                        payload = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    run_id = payload.get("run_id")
                    blueprint = payload.get("blueprint")
                    if isinstance(run_id, str) and isinstance(blueprint, str) and blueprint:
                        mapping[run_id] = blueprint
                        break
        except OSError:
            continue
    return mapping


def _normalized_upload_bytes(envelope: dict[str, Any], blueprints_by_run: dict[str, str]) -> bytes:
    if envelope.get("kind") == "event":
        payload = envelope.get("payload")
        if isinstance(payload, dict):
            run_id = payload.get("run_id")
            blueprint = payload.get("blueprint")
            if isinstance(run_id, str) and not (isinstance(blueprint, str) and blueprint):
                recovered = blueprints_by_run.get(run_id)
                if recovered:
                    envelope = {**envelope, "payload": {**payload, "blueprint": recovered}}
    if envelope.get("kind") == "artifact" and not envelope.get("blueprint"):
        run_id = envelope.get("run_id")
        if isinstance(run_id, str):
            blueprint = blueprints_by_run.get(run_id)
            if blueprint:
                envelope = {**envelope, "blueprint": blueprint}
    return _envelope_bytes(envelope)


def _upload_headers(upload_token: str) -> dict[str, str]:
    headers = {
        "Content-Type": "application/json",
        "Accept": "application/json",
        # Cloudflare can reject Python's default urllib User-Agent at the edge
        # before the request reaches our Worker. Use a stable application UA so
        # telemetry POSTs look like the managed client they are.
        "User-Agent": "Auto-Blueprint-Telemetry/1.0",
    }
    if upload_token:
        headers["Authorization"] = f"Bearer {upload_token}"
    return headers


def _read_normalized_queue_bytes(
    telemetry_root: Path,
    path: Path,
    blueprints_by_run: dict[str, str],
) -> bytes | None:
    try:
        envelope = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, UnicodeDecodeError) as exc:
        _append_upload_error(telemetry_root, path, f"invalid queued envelope: {exc}")
        return None
    if not isinstance(envelope, dict):
        _append_upload_error(telemetry_root, path, "invalid queued envelope: not a JSON object")
        return None
    data = _normalized_upload_bytes(envelope, blueprints_by_run)
    if len(data) > MAX_UPLOAD_BODY_BYTES:
        # This should not happen with the chunked producer. Keep it pending and
        # log loudly so the producer/collector schema can be fixed without
        # losing data.
        _append_upload_error(
            telemetry_root,
            path,
            f"local envelope exceeds upload limit: {len(data)} bytes",
        )
        return None
    return data


def _post_upload(
    upload_url: str,
    headers: dict[str, str],
    data: bytes,
    *,
    timeout: float,
) -> None:
    req = urllib.request.Request(
        upload_url,
        data=data,
        headers=headers,
        method="POST",
    )
    with urllib.request.urlopen(req, timeout=timeout):
        pass


def flush_upload_queues(
    telemetry_root: Path,
    *,
    upload_url: str,
    upload_token: str = "",
    max_items: int = 200,
    timeout: float = 3.0,
) -> tuple[int, int]:
    """Upload pending telemetry from every run queue.

    Returns ``(uploaded, remaining)``. The original ``.json`` files remain the
    source of truth until the collector acknowledges them.
    """
    queue_root = telemetry_root / "upload_queue"
    if not upload_url or not queue_root.is_dir():
        return 0, 0
    headers = _upload_headers(upload_token)
    uploaded = 0
    paths = sorted(queue_root.glob("*/*.json"))[:max_items]
    blueprints_by_run = _blueprints_by_run_id(telemetry_root)
    edge_rejections = 0
    for path in paths:
        try:
            data = _read_normalized_queue_bytes(telemetry_root, path, blueprints_by_run)
            if data is None:
                continue
            _post_upload(upload_url, headers, data, timeout=timeout)
            path.rename(_uploaded_path(path))
            uploaded += 1
        except urllib.error.HTTPError as exc:
            body = ""
            try:
                body = exc.read().decode("utf-8", errors="replace")[:1000]
            except Exception:  # noqa: BLE001 - diagnostic only
                pass
            if exc.code == 403 and "error code: 1010" in body.lower():
                edge_rejections += 1
            _append_upload_error(
                telemetry_root,
                path,
                f"HTTP {exc.code}: {body}",
            )
            if edge_rejections >= 3:
                # This is a Cloudflare edge/WAF rejection, not a per-payload
                # schema failure. Stop quickly so a bad edge rule does not
                # burn minutes walking the whole queue.
                break
            continue
        except TimeoutError as exc:
            _append_upload_error(telemetry_root, path, f"timeout: {exc}")
            break
        except urllib.error.URLError as exc:
            _append_upload_error(telemetry_root, path, f"url error: {exc}")
            break
        except OSError as exc:
            _append_upload_error(telemetry_root, path, f"os error: {exc}")
            continue
    remaining = len(list(queue_root.glob("*/*.json")))
    return uploaded, remaining


def reupload_uploaded_queues(
    telemetry_root: Path,
    *,
    upload_url: str,
    upload_token: str = "",
    max_items: int = 200,
    timeout: float = 3.0,
    force: bool = False,
) -> tuple[int, int, int]:
    """Replay already-uploaded local envelopes through the current normalizer.

    This repairs historical bad R2 prefixes such as ``unknown-blueprint`` and
    ``object-Object`` by sending clean copies from the local append-only queue.
    Successful replays get a sibling ``.reuploaded`` marker so the command is
    resumable and does not duplicate records on every run.
    """
    queue_root = telemetry_root / "upload_queue"
    if not upload_url or not queue_root.is_dir():
        return 0, 0, 0
    headers = _upload_headers(upload_token)
    candidates = sorted(queue_root.glob("*/*.uploaded"))
    if not force:
        candidates = [path for path in candidates if not _reuploaded_path(path).exists()]
    paths = candidates[:max_items]
    blueprints_by_run = _blueprints_by_run_id(telemetry_root)
    reuploaded = 0
    skipped = 0
    edge_rejections = 0
    for path in paths:
        try:
            data = _read_normalized_queue_bytes(telemetry_root, path, blueprints_by_run)
            if data is None:
                skipped += 1
                continue
            _post_upload(upload_url, headers, data, timeout=timeout)
            _reuploaded_path(path).write_text(
                json.dumps(
                    {"timestamp": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())},
                    ensure_ascii=False,
                )
                + "\n",
                encoding="utf-8",
            )
            reuploaded += 1
        except urllib.error.HTTPError as exc:
            body = ""
            try:
                body = exc.read().decode("utf-8", errors="replace")[:1000]
            except Exception:  # noqa: BLE001 - diagnostic only
                pass
            if exc.code == 403 and "error code: 1010" in body.lower():
                edge_rejections += 1
            _append_upload_error(telemetry_root, path, f"HTTP {exc.code}: {body}")
            if edge_rejections >= 3:
                break
            continue
        except TimeoutError as exc:
            _append_upload_error(telemetry_root, path, f"timeout: {exc}")
            break
        except urllib.error.URLError as exc:
            _append_upload_error(telemetry_root, path, f"url error: {exc}")
            break
        except OSError as exc:
            _append_upload_error(telemetry_root, path, f"os error: {exc}")
            continue
    remaining = len(
        [
            path
            for path in queue_root.glob("*/*.uploaded")
            if force or not _reuploaded_path(path).exists()
        ]
    )
    return reuploaded, skipped, remaining


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


def _telemetry_root(repo_root: Path) -> Path:
    return repo_root / ".auto-blueprint" / "telemetry"


def _pending_count(root: Path) -> int:
    return len(list((root / "upload_queue").glob("*/*.json")))


def _uploaded_count(root: Path) -> int:
    return len(list((root / "upload_queue").glob("*/*.uploaded")))


def _reuploaded_count(root: Path) -> int:
    return len(list((root / "upload_queue").glob("*/*.reuploaded")))


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root containing .auto-blueprint/telemetry.",
    )
    sub = parser.add_subparsers(dest="command", required=True)
    doctor = sub.add_parser("doctor", help="Print local telemetry/upload configuration.")
    doctor.add_argument("--show-target", action="store_true", help="Show non-secret upload target.")
    flush = sub.add_parser("flush", help="Upload pending telemetry queue files.")
    flush.add_argument("--max-items", type=int, default=500, help="Maximum queued files to upload.")
    flush.add_argument("--timeout", type=float, default=5.0, help="Per-request upload timeout.")
    reupload = sub.add_parser(
        "reupload",
        help="Replay already-uploaded queue files through the current normalizer.",
    )
    reupload.add_argument(
        "--include-uploaded",
        action="store_true",
        help="Required safety acknowledgement: replay .uploaded queue files.",
    )
    reupload.add_argument("--max-items", type=int, default=500, help="Maximum uploaded files to replay.")
    reupload.add_argument("--timeout", type=float, default=5.0, help="Per-request upload timeout.")
    reupload.add_argument(
        "--force",
        action="store_true",
        help="Replay files even if they already have a .reuploaded marker.",
    )
    args = parser.parse_args(argv)

    root = _telemetry_root(args.repo_root)
    upload_url = os.environ.get("AUTO_BLUEPRINT_TELEMETRY_URL", "").strip()
    upload_token = os.environ.get("AUTO_BLUEPRINT_TELEMETRY_TOKEN", "").strip()

    if args.command == "doctor":
        print(f"telemetry root: {root}")
        print(f"pending uploads: {_pending_count(root)}")
        print(f"uploaded markers: {_uploaded_count(root)}")
        print(f"reuploaded markers: {_reuploaded_count(root)}")
        print(f"upload configured: {bool(upload_url)}")
        print(f"token set: {bool(upload_token)}")
        if args.show_target:
            print(
                "target: "
                + json.dumps(_upload_target_fingerprint(upload_url, upload_token), ensure_ascii=False)
            )
        return 0

    if args.command == "flush":
        if not upload_url:
            raise SystemExit("AUTO_BLUEPRINT_TELEMETRY_URL is not set")
        uploaded, remaining = flush_upload_queues(
            root,
            upload_url=upload_url,
            upload_token=upload_token,
            max_items=args.max_items,
            timeout=args.timeout,
        )
        print(f"uploaded: {uploaded}")
        print(f"remaining: {remaining}")
        errors = root / "upload_errors.jsonl"
        if errors.is_file():
            print(f"upload errors log: {errors}")
        return 0

    if args.command == "reupload":
        if not args.include_uploaded:
            raise SystemExit("pass --include-uploaded to replay already-uploaded telemetry")
        if not upload_url:
            raise SystemExit("AUTO_BLUEPRINT_TELEMETRY_URL is not set")
        reuploaded, skipped, remaining = reupload_uploaded_queues(
            root,
            upload_url=upload_url,
            upload_token=upload_token,
            max_items=args.max_items,
            timeout=args.timeout,
            force=args.force,
        )
        print(f"reuploaded: {reuploaded}")
        print(f"skipped: {skipped}")
        print(f"remaining reupload candidates: {remaining}")
        errors = root / "upload_errors.jsonl"
        if errors.is_file():
            print(f"upload errors log: {errors}")
        return 0

    return 1


if __name__ == "__main__":
    raise SystemExit(main())
