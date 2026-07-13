---
name: fkst-monitor
description: Snapshot, diagnose, and keep current the fkst autonomous-development engine deployed on this repo (supervise liveness, log errors, delivery throughput, durable/DLQ state, issue/PR processing, and fkst-packages platform-pin freshness against dev). Use when checking whether the fkst devloop is running/healthy, why it stalled, whether newer platform packages are on dev, or when the user mentions fkst status, the supervise loop, the autonomous dev engine, ~/.fkst, or the github-devloop pipeline.
---

# fkst-monitor

Monitors and maintains the fkst autonomous-development engine (standard github-devloop platform packages composed on this repo, launched via `.fkst/scripts/run.sh supervise`, operational state under `~/.fkst/trureturing/`).

## Quick start

Run the read-only health snapshot:

```sh
bash .claude/skills/fkst-monitor/scripts/status.sh
```

It prints, in one pass: liveness (pid/uptime), fatal-error and WARN/ERROR counts, delivery throughput (acks/min), durable-delivery state (queue depth, DLQ, subscriber status) via `fkst-framework observe`, recent issue/PR activity, and a one-line verdict (`HEALTHY` / `DEGRADED` / `DOWN`).

Watch continuously (emits only on trouble — quiet when healthy):

```sh
bash .claude/skills/fkst-monitor/scripts/status.sh --watch
```

## What to check, and what it means

- **Liveness** — `run.sh status` + pid uptime. DOWN → the supervise process exited; restart with `bash .fkst/scripts/run.sh supervise` and read the tail of the newest `~/.fkst/trureturing/logs/supervise-*.log` for the exit cause.
- **Fatal / WARN·ERROR** — `panic`, `FATAL`, `startup error`, `thread 'main' panicked` are real. `schema validation warning` for `test_*`/`*_probe` produced-only queues is **benign** (platform test departments with no consumer in this composition).
- **Throughput** — steady `MSG=delivery acked` growth = flowing. Zero acks over several minutes on a non-idle repo → stalled consumers.
- **Durable / DLQ** — `fkst-framework observe --durable-root ~/.fkst/trureturing/durable --json`: rising DLQ depth means deliveries are exhausting retries (a stage keeps failing — inspect the failing dept's `error_class`). `subscriber_status:absent` on a reliable queue means a consumer never started.
- **Issue/PR processing** — `github_entity_changed` → `intake.admission` / `observe_issue` / `observe_pr` acks show the devloop is picking up and driving GitHub work. `error_class=codex-failed` with `No such file` means the `codex` binary is not on the supervise child PATH (fix in `host.env`, not source).

## Keep the platform current (fkst-packages dev)

The deployment pins the fkst-packages platform at `.fkst/fkst.workspace.toml` `external_sources.rev`. fkst-packages `dev` moves (bug fixes, new packages); the pin should follow it so the engine runs the latest platform. **Fixes to the devloop merge/rollup, review, or intake often land on dev** — a stalled or looping pipeline is frequently resolved by syncing.

Check whether newer platform packages are on dev (read-only):

```sh
bash .claude/skills/fkst-monitor/scripts/platform_sync.sh check
```

Reports `CURRENT` or `BEHIND by N commit(s)` with the new commit list. To apply — stop supervise → fast-forward the platform checkout to `origin/dev` → re-pin `fkst.workspace.toml` → regenerate `fkst.lock` → restart supervise → sync the engine checkout:

```sh
bash .claude/skills/fkst-monitor/scripts/platform_sync.sh sync
```

After `sync`, **commit the pin bump** (`.fkst/fkst.workspace.toml` + `.fkst/fkst.lock`) so the repo records the platform revision.

## Diagnosing a stall

1. Snapshot: `scripts/status.sh`.
2. If DOWN → restart + read newest supervise log tail for the exit cause.
3. If DEGRADED (DLQ climbing / a dept repeatedly failing) → find the failing department's child log under `~/.fkst/trureturing/runtime/logs/framework-child/<dept>-*.log`, read its `error_class` and stderr, and fix the root cause (config in `host.env`, or a real defect). Non-terminal failures retry+DLQ; the engine stays up.
4. Never treat `pgrep`/empty log as proof of health — use the delivery/observe evidence.

Write posture and paths are host-local operational facts in `~/.fkst/trureturing/host.env` (gitignored); this skill only reads.
