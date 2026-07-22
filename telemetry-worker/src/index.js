const MAX_BODY_BYTES = 10 * 1024 * 1024;

function jsonResponse(body, status = 200) {
  return new Response(JSON.stringify(body), {
    status,
    headers: {
      "content-type": "application/json; charset=utf-8",
    },
  });
}

function stringField(value, fallback) {
  return typeof value === "string" && value.trim() ? value.trim() : fallback;
}

function scalarField(value, fallback) {
  if (typeof value === "string" && value.trim()) return value.trim();
  if (typeof value === "number" || typeof value === "boolean") return String(value);
  return fallback;
}

function safeSegment(value, fallback = "unknown") {
  const raw = scalarField(value, fallback);
  const safe = raw.replace(/[^A-Za-z0-9._-]+/g, "-").replace(/^-+|-+$/g, "");
  return (safe || fallback).slice(0, 120);
}

function payloadProject(payload) {
  return stringField(payload.project, stringField(payload.payload?.project, "auto-blueprint"));
}

function payloadBlueprint(payload) {
  return stringField(payload.blueprint, stringField(payload.payload?.blueprint, ""));
}

function payloadRunId(payload) {
  return stringField(payload.run_id, stringField(payload.payload?.run_id, ""));
}

export default {
  async fetch(request, env) {
    const url = new URL(request.url);

    if (request.method === "OPTIONS") {
      return new Response(null, { status: 204 });
    }

    if (request.method === "GET" && url.pathname === "/health") {
      return jsonResponse({ ok: true });
    }

    if (request.method !== "POST" || url.pathname !== "/telemetry") {
      return jsonResponse({ error: "not_found" }, 404);
    }

    if (!env.TELEMETRY_TOKEN) {
      return jsonResponse({ error: "missing_server_secret" }, 500);
    }

    const expected = `Bearer ${env.TELEMETRY_TOKEN}`;
    if ((request.headers.get("authorization") || "") !== expected) {
      return jsonResponse({ error: "unauthorized" }, 401);
    }

    const contentLength = Number(request.headers.get("content-length") || 0);
    if (contentLength > MAX_BODY_BYTES) {
      return jsonResponse({ error: "payload_too_large" }, 413);
    }

    let payload;
    try {
      payload = await request.json();
    } catch {
      return jsonResponse({ error: "invalid_json" }, 400);
    }

    if (!payload || typeof payload !== "object") {
      return jsonResponse({ error: "invalid_payload" }, 400);
    }

    const kind = safeSegment(payload.kind, "unknown");
    if (kind !== "event" && kind !== "artifact") {
      return jsonResponse({ error: "unsupported_kind" }, 400);
    }

    const now = new Date();
    const date = now.toISOString().slice(0, 10);
    const project = safeSegment(payloadProject(payload));
    const rawBlueprint = payloadBlueprint(payload);
    const rawRunId = payloadRunId(payload);
    if (!rawBlueprint) {
      return jsonResponse({ error: "missing_blueprint" }, 400);
    }
    if (!rawRunId) {
      return jsonResponse({ error: "missing_run_id" }, 400);
    }
    const blueprint = safeSegment(rawBlueprint);
    const runId = safeSegment(rawRunId);
    const seq = safeSegment(payload.payload?.seq ?? payload.sha256 ?? crypto.randomUUID(), "item");
    const key = `raw/${project}/${blueprint}/${date}/${runId}/${seq}-${kind}-${crypto.randomUUID()}.json`;

    const stored = {
      received_at: now.toISOString(),
      cf_ray: request.headers.get("cf-ray") || "",
      remote: request.headers.get("cf-connecting-ip") || "",
      payload,
    };

    await env.TELEMETRY_BUCKET.put(key, JSON.stringify(stored) + "\n", {
      httpMetadata: {
        contentType: "application/json; charset=utf-8",
      },
    });

    return jsonResponse({ ok: true, key });
  },
};
