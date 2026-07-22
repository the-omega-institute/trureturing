# theory-selfgrowth

Implements the CLAUDE.md rule 22 open-driven flywheel for D5. The host package periodically
reconciles whether the frontier-generation workflow needs a request; it does not derive or edit
truth-DAG state itself.

## What it does
- `raisers/frontier_poll.lua` emits `theory_selfgrowth_tick` every 30 minutes. This independent
  wakeup prevents strict global-idle detection from starving required frontier work.
- `departments/propose/main.lua` also consumes `idle-detector.system_idle` as a secondary wakeup;
  stale or expired idle hints remain fail-closed.
- Before emitting, the producer searches its own requests. Any open request suppresses another
  emission, so repeated ticks remain bounded to one open request.
- A permitted wakeup emits one `github-proxy.github_issue_create_request` for
  `.fkst/workflows/frontier-generation.json`.
- The downstream workflow derives authoritative Open state with
  `TruthDagConstruction.DeriveState` and deterministically no-ops when no eligible semantic
  frontier demand exists.

The package is composed by `.fkst/fkst.workspace.toml` and launched by `.fkst/scripts/run.sh` as
the `theory-selfgrowth` host package. Its runtime surface is restricted to the publishable
`contract` library and framework-injected `exec_sync`, `json`, `raise`, and `log` globals.
