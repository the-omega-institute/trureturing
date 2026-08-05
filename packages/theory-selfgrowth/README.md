# theory-selfgrowth (host package) — DRAFT, not yet deployed

Implements CLAUDE.md 第22条 "方向由 open 队列内生" for D5: an **idle-subscribed producer** that turns the running pipeline into a self-growing theory engine, entirely via workflow + system-idle subscription (no external cron, no manual issue filing).

## What it does
- **Subscribes** to `idle-detector.system_idle` (the platform's fanout idle broadcast).
- On idle, **dedups** (skips if a generation request is already open — at most one at a time, never floods).
- Otherwise **emits ONE** `github-proxy.github_issue_create_request` titled *"Generate the next worthy D5 frontier obligation from the current truth-DAG"* → the devloop routes it to the existing `.fkst/workflows/frontier-generation.json` (its POSITIVE FIXTURE), which appends one `X_Frontier` obligation + posts a downstream `Deliver ONE NEW D5 result` issue → `blueprint-then-formalize`.
- The **codex reasoning** over the frozen truth-DAG + live literature dedup happens DOWNSTREAM in those workflows (Observe layer, receipts only; offline admission gate). This producer only fires the idle→generate transaction and never touches a frozen node (conservative extension).

This host-owned idle-subscribed producer uses only the platform's publishable contracts.

## Remaining steps to deploy (each a protected-branch PR; verify engine stays HEALTHY after each)
1. **Verify against the fkst conformance harness.** Confirm the exported `env.read_env`, `github.issue_search`, department, `raise`/`exec_sync`, and saga contracts directly. Run the platform's package test/conformance (`$BIN test` / `$BIN host lock`) and iterate until green. Add unit tests for dedup-skip, emit-when-empty, and replay-idempotent behavior.
2. **Enable `idle-detector`** in `.fkst/fkst.workspace.toml` `packages = [...]` (brings the 30m `idle_tick` → `system_idle` broadcast). Regenerate `.fkst/fkst.lock` (`$BIN host lock --project-root .fkst`).
3. **Wire the host package into launch.** `.fkst/scripts/run.sh` must pass `--host-packages "theory-selfgrowth" --local-packages .fkst/local-packages` to the platform supervise (see `fkst-packages/scripts/host_run.sh` `--host-packages`/`--local-packages`). Currently trureturing's run.sh passes neither.
4. **P0 shadow first (optional, per META_JUDGE):** land with emit disabled (log-only) for one idle cycle to confirm firing + dedup, then enable emit.

## Conformance findings (2026-07-21 — verified against `fkst-framework conformance`)
Real iteration through the framework's conformance CLI produced concrete constraints:
- **Invocation:** `fkst-framework conformance --project-root <repo-with-root-level-fkst.workspace.toml> --package-root <this-pkg> --package-root <platform>/packages/idle-detector --package-root <platform>/packages/github-proxy`. Deps a package consumes/produces MUST be passed as `--package-root`; project-root needs a **root-level** `fkst.workspace.toml` (repo keeps it at `.fkst/` → root symlink needed) + matching `fkst.lock` (`fkst-framework host lock --project-root .fkst`).
- **Workspace declaration (this branch already applies it):** `[workspace] units = ["packages/theory-selfgrowth"]`; `idle-detector` added to `[[external_sources]].packages`; package relocated to `packages/theory-selfgrowth` (units-matched).
- **CRITICAL — host packages have a restricted library surface.** A host package (different source than the platform) is filtered by the *external-publishable gate* to **publishable libraries only** (contract, workflow, testkit). It **CANNOT** use `forge`, `devloop`, or `workflow_internal` — those are platform-internal. Conformance fails: "external source `fkst-packages-platform` does not allow library `forge`/`workflow_internal`".
- **⇒ Platform-internal producer patterns do NOT port to a host package.** Platform packages may use `forge.ports`, `devloop.github_factory`, `workflow_internal.env`, and internal saga APIs. This package must be **redesigned minimal**: consume `idle-detector.system_idle`; build a plain-table `github-proxy.issue-create.v1` payload and `raise("github-proxy.github_issue_create_request", payload)`; rely on github-proxy's own `dedup_key` for idempotency (NO forge/devloop github search). Use only contract/workflow.
- **Open blocker for the redesign:** how a host-package department reads `FKST_GITHUB_REPO` and the exact `pipeline(_)`/spec signature for host producers, using only publishable APIs — `read_env`/`raise` are department-runtime-injected globals, not base globals. See the minimal host department in `fkst-substrate/crates/fkst-framework/tests/host_conformance_cli.rs` (≈L905/L980: `M.spec = {...}; function pipeline(_) end`).

The original `departments/propose/main.lua` used platform-internal forge/saga APIs and was therefore **known-not-conformant**; the host implementation must use the minimal publishable-only form above.

## Why not enabled yet
Deploying unverified framework Lua to the live production engine risks breaking supervise (watchdog would then loop-restart a broken config). Per CLAUDE.md 第16条 this is authored in an isolated worktree and stays undeployed until conformance-verified. See memory `autonomous-selfgrowth-goal`.
