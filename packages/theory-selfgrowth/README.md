# theory-selfgrowth (host package) — DRAFT, not yet deployed

Implements CLAUDE.md 第22条 "方向由 open 队列内生" for D5: an **idle-subscribed producer** that turns the running pipeline into a self-growing theory engine, entirely via workflow + system-idle subscription (no external cron, no manual issue filing).

## What it does
- **Subscribes** to `idle-detector.system_idle` (the platform's fanout idle broadcast).
- On idle, validates the `idle-detector.system-idle.v1` payload (`detected_at`, `expires_at`, and `source_ref`) before any side effect.
- Checks the stable open-request marker with an open-only query, then emits generation-scoped requests: same `detected_at` replays with the same `dedup_key`; the next idle generation receives a new `dedup_key` so a closed prior issue cannot suppress it.
- Otherwise **emits ONE** `github-proxy.github_issue_create_request` titled *"Generate the next worthy D5 frontier obligation from the current truth-DAG"* → the devloop routes it to the existing `.fkst/workflows/frontier-generation.json` (its POSITIVE FIXTURE), which appends one `X_Frontier` obligation + posts a downstream `Deliver ONE NEW D5 result` issue → `blueprint-then-formalize`.
- The **codex reasoning** over the frozen truth-DAG + live literature dedup happens DOWNSTREAM in those workflows (Observe layer, receipts only; offline admission gate). This producer only fires the idle→generate transaction and never touches a frozen node (conservative extension).

Modeled on `fkst-packages/packages/archaudit` (idle-subscribed issue producer), minus the codex judgment pipeline.

## Remaining steps to deploy (each a protected-branch PR; verify engine stays HEALTHY after each)
1. **Verify against the fkst conformance harness.** The `[VERIFY]` comments in `departments/propose/main.lua` mirror archaudit but must be confirmed: `env.read_env` signature, `github.issue_search(repo,query,fields,limit)`, `make_department(ports)` + global `raise`/`exec_sync`, and `saga.department` act/done contract. Run the platform's package test/conformance (`$BIN test` / `$BIN host lock`) and iterate until green. Add unit tests (dedup-skip, emit-when-empty, replay-idempotent) mirroring archaudit/tests.
2. **Enable `idle-detector`** in `.fkst/fkst.workspace.toml` `packages = [...]` (brings the 30m `idle_tick` → `system_idle` broadcast). Regenerate `.fkst/fkst.lock` (`$BIN host lock --project-root .fkst`).
3. **Wire the host package into launch.** `.fkst/scripts/run.sh` must pass `--host-packages "theory-selfgrowth" --local-packages .fkst/local-packages` to the platform supervise (see `fkst-packages/scripts/host_run.sh` `--host-packages`/`--local-packages`). Currently trureturing's run.sh passes neither.
4. **P0 shadow first (optional, per META_JUDGE):** land with emit disabled (log-only) for one idle cycle to confirm firing + dedup, then enable emit.

## Conformance findings (2026-07-21 — verified against `fkst-framework conformance`)
Real iteration through the framework's conformance CLI produced concrete constraints:
- **Invocation:** `fkst-framework conformance --project-root <repo-with-root-level-fkst.workspace.toml> --package-root <this-pkg> --package-root <platform>/packages/idle-detector --package-root <platform>/packages/github-proxy`. Deps a package consumes/produces MUST be passed as `--package-root`; project-root needs a **root-level** `fkst.workspace.toml` (repo keeps it at `.fkst/` → root symlink needed) + matching `fkst.lock` (`fkst-framework host lock --project-root .fkst`).
- **Workspace declaration (this branch already applies it):** `[workspace] units = ["packages/theory-selfgrowth"]`; `idle-detector` added to `[[external_sources]].packages`; package relocated to `packages/theory-selfgrowth` (units-matched).
- **CRITICAL — host packages have a restricted library surface.** A host package (different source than the platform) is filtered by the *external-publishable gate* to **publishable libraries only** (contract, workflow, testkit). It **CANNOT** use `forge`, `devloop`, or `workflow_internal` — those are platform-internal. Conformance fails: "external source `fkst-packages-platform` does not allow library `forge`/`workflow_internal`".
- **⇒ The archaudit pattern does NOT port to a host package.** archaudit is a *platform* package, so it may use `forge.ports`, `devloop.github_factory`, `workflow_internal.env`, `saga`. This package uses the minimal host-package form instead: consume `idle-detector.system_idle`; run the open-only request exclusion through framework-injected `exec_sync`; build a plain-table `github-proxy.issue-create.v1` payload and `raise("github-proxy.github_issue_create_request", payload)`; use only publishable `contract` APIs plus framework-injected globals.

## Why not enabled yet
Deploying unverified framework Lua to the live production engine risks breaking supervise (watchdog would then loop-restart a broken config). Per CLAUDE.md 第16条 this is authored in an isolated worktree and stays undeployed until conformance-verified. See memory `autonomous-selfgrowth-goal`.
