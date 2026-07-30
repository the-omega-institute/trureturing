---
name: fkst-monitor
description: Snapshot, diagnose, and maintain the fkst autonomous-development engine deployed on this repo (supervise liveness, log errors, delivery throughput, durable/DLQ state, issue/PR processing, platform-pin freshness, checkout freshness, restart deferral, and conservative garbage collection). Use when checking whether the fkst devloop is running/healthy, why it stalled, whether deployed code is current, or when the user mentions fkst status, the supervise loop, the autonomous dev engine, ~/.fkst, or the github-devloop pipeline.
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

## Run the maintenance cycle

The repository-owned operational entrypoint is the Make target:

```console
make hourly-maintenance HOST_CONFIG="$HOME/.fkst/trureturing/host.env"
```

The tracked entrypoint parses that file as data against `.fkst/host-contract.schema`; it does not source it. The target delegates to the single tracked implementation, which synchronizes the deployed top-level platform pin and lock, fast-forwards only a clean ancestor checkout, defers restart while issues are implementing, and conservatively reclaims eligible worktrees and dead-owner report slots. The tracked launchd template runs this same Make target daily at 09:30; setup and conformance commands are in `docs/devloop/fkst-host-bringup.md`.

## Diagnosing a stall

1. Snapshot: `scripts/status.sh`.
2. If DOWN → restart + read newest supervise log tail for the exit cause.
3. If DEGRADED (DLQ climbing / a dept repeatedly failing) → find the failing department's child log under `~/.fkst/trureturing/runtime/logs/framework-child/<dept>-*.log`, read its `error_class` and stderr, and fix the root cause (config in `host.env`, or a real defect). Non-terminal failures retry+DLQ; the engine stays up.
4. Never treat `pgrep`/empty log as proof of health — use the delivery/observe evidence.

Write posture and paths are host-local operational facts in `~/.fkst/trureturing/host.env` (gitignored); this skill only reads.
