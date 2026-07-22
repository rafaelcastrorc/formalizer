# Auto-Blueprint Telemetry Collector

This Worker receives Auto-Blueprint telemetry uploads and stores the raw JSON
envelopes in Cloudflare R2. It is intentionally dumb storage: validate the
shared token, write append-only objects, and let later dataset jobs decide how
to compact, label, and train from the data.

## Deploy

Run these commands from this directory:

```bash
cd telemetry-worker
npx wrangler r2 bucket create auto-blueprint-telemetry
npx wrangler secret put TELEMETRY_TOKEN
npx wrangler deploy
```

When `wrangler secret put TELEMETRY_TOKEN` prompts for a value, paste a long
shared secret. Do not commit that secret.

The deployed URL will look like:

```text
https://auto-blueprint-telemetry.<your-workers-subdomain>.workers.dev
```

The Auto-Blueprint telemetry URL is:

```text
https://auto-blueprint-telemetry.<your-workers-subdomain>.workers.dev/telemetry
```

## Configure contributors

Each contributor sets these environment variables before starting the Web UI or
CLI:

```bash
export AUTO_BLUEPRINT_TELEMETRY_URL="https://auto-blueprint-telemetry.<your-workers-subdomain>.workers.dev/telemetry"
export AUTO_BLUEPRINT_TELEMETRY_TOKEN="<same shared secret>"
export AUTO_BLUEPRINT_TELEMETRY_PROJECT="auto-blueprint"
```

Then start Auto-Blueprint from that same terminal:

```bash
uv run python scripts/webui.py
```

## Smoke test

```bash
curl -sS -X POST "$AUTO_BLUEPRINT_TELEMETRY_URL" \
  -H "Authorization: Bearer $AUTO_BLUEPRINT_TELEMETRY_TOKEN" \
  -H "Content-Type: application/json" \
  --data '{"kind":"event","payload":{"event":"smoke","project":"auto-blueprint","blueprint":"smoke","run_id":"manual","seq":1}}'
```

The response should be:

```json
{"ok":true,"key":"..."}
```

After that, open the `auto-blueprint-telemetry` R2 bucket in Cloudflare and
check for an object under `raw/auto-blueprint/smoke/...`.
