SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
WORKTREE_PATH = $(if $(filter command line,$(origin PATH)),$(PATH),$(abspath ../trureturing-$(NAME)))
export HOST_CONFIG OUTPUT DEPLOYED_LAUNCHER VALIDATE_ONLY

.PHONY: help dotnet test lua-test hourly-maintenance maintenance-launcher-render maintenance-launcher-check supervise-launcher-render supervise-launcher-check launchd-conformance-check lean-cache-ensure lean lean-report build c0-renew clean-lanes emit emit-check ingest echo-residual-summary echo-verify record-golden selftest scratch-sweep gate perf-report deliver-check receipts-stage derived-refresh worktree pr-watch

help:
	@printf '%s\n' 'make help                         Show this target list' 'make dotnet                       Restore and build .NET with warnings as errors' 'make test                         Run the .NET test suite' 'make lua-test                     Run the pinned fkst Lua package gate' 'make hourly-maintenance HOST_CONFIG=f  Run the canonical deployed-engine maintenance cycle' 'make maintenance-launcher-render HOST_CONFIG=f [OUTPUT=p]  Render the host launchd unit' 'make maintenance-launcher-check HOST_CONFIG=f [DEPLOYED_LAUNCHER=p]  Check deployed launchd bytes' 'make supervise-launcher-render HOST_CONFIG=f [OUTPUT=p]  Render the supervise launchd unit' 'make supervise-launcher-check HOST_CONFIG=f [DEPLOYED_LAUNCHER=p]  Check deployed supervise launchd bytes' 'make launchd-conformance-check HOST_CONFIG=f  Check deployed launchd membership and launcher bytes' 'make lean-cache-ensure            Ensure a private Lean build cache is available' 'make lean                         Build the pinned Lean project' 'make lean-report                  Produce the canonical raw Lean report' 'make build                        Run make dotnet and make lean' 'make c0-renew [BASE=origin/dev]   Renew C0 ceremony projections; admission remains separate' 'make clean-lanes [BASE=origin/dev] [FORCE=1]  List reclaimable lanes (dry-run); FORCE=1 removes them' 'make emit                         Emit canonical Scribe documents, catalog, and values' 'make emit-check                   Check canonical Scribe documents, catalog, and values' 'make ingest [BASE=origin/dev]     Consume the raw Lean report and align theory receipts' 'make echo-residual-summary [BASE=origin/dev]  Emit the content-addressed residual projection bytes' 'make echo-verify [FILE=f] [BASE=origin/dev]  Byte-verify the committed residual projection when affected' 'make record-golden                Record Engine diagnostics into golden TOML' 'make selftest                     Run deterministic StrataLint selftest' 'make scratch-sweep                Reclaim leaked ceremony scratch checkouts older than 24h' 'make gate [BASE=origin/dev]       Run the local CI-equivalent admission flow' 'make preflight [BASE=origin/dev]  Pre-verify BOTH required CI checks locally before pushing' 'make perf-report [RECENT=10]      Summarize the external performance ledger' 'make deliver-check [BASE=origin/dev]  Run theorem delivery in canonical freeze-last order' 'make receipts-stage [BASE=origin/dev]  Re-derive staged receipts and reject unsafe absorption' 'make derived-refresh [BASE=origin/dev]  Merge base and refresh all derived artifacts' 'make worktree NAME=x [BASE=origin/dev] [PATH=DIR]  Initialize an isolated worktree; .lake is copied, never symlinked' 'make pr-open HEAD=branch TITLE=t [BODY=file]  Open a PR to dev and arm auto-merge (canonical PR path)' 'make pr-watch [INTERVAL=60] [CYCLES=360]  Poll armed PRs; stale BEHIND and CONFLICTING use persistent-worktree path classification then regen or alert; other BEHIND uses update-branch'

dotnet:
	@/bin/bash Meta/StrataLint/scripts/dotnet-build.sh

test:
	@dotnet test Meta/StrataLint/StrataLint.sln --configuration Release --verbosity normal

lua-test:
	@.fkst/scripts/run.sh test

hourly-maintenance:
	@/bin/bash .fkst/scripts/hourly-maintenance.sh

maintenance-launcher-render:
	@/bin/bash .fkst/scripts/render-maintenance-launcher.sh

maintenance-launcher-check:
	@/bin/bash .fkst/scripts/check-maintenance-launcher.sh

supervise-launcher-render:
	@/bin/bash .fkst/scripts/render-supervise-launcher.sh

supervise-launcher-check:
	@/bin/bash .fkst/scripts/check-supervise-launcher.sh

launchd-conformance-check:
	@/bin/bash .fkst/scripts/check-launchd-conformance.sh

lean-cache-ensure:
	@/bin/bash Meta/StrataLint/scripts/worktree/lean-cache-ensure.sh

lean: lean-cache-ensure
	@lake build

lean-report: lean-cache-ensure
	@/bin/bash Meta/StrataLint/scripts/report/lean-report.sh

build: lean-cache-ensure dotnet lean

c0-renew: scratch-sweep
	@dotnet run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- c0-renew --base "$(BASE)"

clean-lanes:
	@/bin/bash Meta/StrataLint/scripts/clean-lanes.sh --base "$(BASE)" $(if $(filter 1,$(FORCE)),--force,)

emit:
	@/bin/bash Meta/StrataLint/scripts/scribe.sh emit

emit-check: echo-verify
	@/bin/bash Meta/StrataLint/scripts/scribe.sh check

ingest:
	@/bin/bash Meta/StrataLint/scripts/ingest.sh "$(BASE)"

echo-residual-summary:
	@/bin/bash Meta/StrataLint/scripts/report/echo-residual-summary.sh "$(BASE)"

echo-verify:
	@/bin/bash Meta/StrataLint/scripts/report/echo-verify.sh "$(FILE)" "$(BASE)"

record-golden:
	@dotnet run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- golden-record

selftest:
	@/bin/bash Meta/StrataLint/scripts/stratalint-selftest.sh

scratch-sweep:
	@find "$${TMPDIR:-/tmp}" /tmp -maxdepth 1 -type d \( -name 'stratalint-c0-renew-*' -o -name 'stratalint-conservative-*' \) -mtime +0 -exec rm -rf {} + 2>/dev/null || true

gate: scratch-sweep
	@/bin/bash Meta/StrataLint/scripts/local-harness-gate.sh --base "$(BASE)" $(GATE_ARGS)

perf-report:
	@/bin/bash Meta/StrataLint/scripts/perf-report.sh "$(RECENT)" "$(abspath Golden/perf-budgets.toml)"

deliver-check:
	@/bin/bash Meta/StrataLint/scripts/playbook-workflows.sh deliver-check "$(BASE)"

receipts-stage:
	@/bin/bash Meta/StrataLint/scripts/playbook-workflows.sh receipts-stage "$(BASE)"

derived-refresh:
	@/bin/bash Meta/StrataLint/scripts/playbook-workflows.sh derived-refresh "$(BASE)"

preflight: scratch-sweep
	@/bin/bash Meta/StrataLint/scripts/preflight.sh

worktree: scratch-sweep
	@/bin/bash Meta/StrataLint/scripts/worktree-init.sh "$(NAME)" "$(WORKTREE_PATH)" "$(BASE)"

pr-open:
	@/bin/bash Meta/StrataLint/scripts/pr-shepherd.sh open "$(HEAD)" "$(TITLE)" $(BODY)

pr-watch:
	@/bin/bash Meta/StrataLint/scripts/pr-shepherd.sh watch $(INTERVAL) $(CYCLES)
