# theory-selfgrowth (host package) — DRAFT, not yet deployed

Implements CLAUDE.md 第22条 "方向由 open 队列内生" for D5: an **idle-subscribed producer** that turns the running pipeline into a self-growing theory engine, entirely via workflow + system-idle subscription (no external cron, no manual issue filing).

## What it does
- **Subscribes** to `idle-detector.system_idle` (the platform's fanout idle broadcast).
- On idle, **dedups** (skips if a generation request is already open — at most one at a time, never floods).
- Otherwise **emits ONE** `github-proxy.github_issue_create_request` titled *"Generate the next worthy D5 frontier obligation from the current truth-DAG"* → the devloop routes it to the existing `.fkst/workflows/frontier-generation.json` (its POSITIVE FIXTURE), which appends one `X_Frontier` obligation + posts a downstream `Deliver ONE NEW D5 result` issue → `blueprint-then-formalize`.
- The **codex reasoning** over the frozen truth-DAG + live literature dedup happens DOWNSTREAM in those workflows (Observe layer, receipts only; offline admission gate). This producer only fires the idle→generate transaction and never touches a frozen node (conservative extension).

Modeled on `fkst-packages/packages/archaudit` (idle-subscribed issue producer), minus the codex judgment pipeline.

## Remaining steps to deploy (each a protected-branch PR; verify engine stays HEALTHY after each)
1. **Verify against the fkst conformance harness.** The `[VERIFY]` comments in `departments/propose/main.lua` mirror archaudit but must be confirmed: `env.read_env` signature, `github.issue_search(repo,query,fields,limit)`, `make_department(ports)` + global `raise`/`exec_sync`, and `saga.department` act/done contract. Run the platform's package test/conformance (`$BIN test` / `$BIN host lock`) and iterate until green. Add unit tests (dedup-skip, emit-when-empty, replay-idempotent) mirroring archaudit/tests.
2. **Enable `idle-detector`** in `.fkst/fkst.workspace.toml` `packages = [...]` (brings the 30m `idle_tick` → `system_idle` broadcast). Regenerate `.fkst/fkst.lock` (`$BIN host lock --project-root .fkst`).
3. **Wire the host package into launch.** `.fkst/scripts/run.sh` must pass `--host-packages "theory-selfgrowth" --local-packages .fkst/local-packages` to the platform supervise (see `fkst-packages/scripts/host_run.sh` `--host-packages`/`--local-packages`). Currently trureturing's run.sh passes neither.
4. **P0 shadow first (optional, per META_JUDGE):** land with emit disabled (log-only) for one idle cycle to confirm firing + dedup, then enable emit.

## Why not enabled yet
Deploying unverified framework Lua to the live production engine risks breaking supervise (watchdog would then loop-restart a broken config). Per CLAUDE.md 第16条 this is authored in an isolated worktree and stays undeployed until conformance-verified. See memory `autonomous-selfgrowth-goal`.
