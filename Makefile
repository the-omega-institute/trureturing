SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
OUT ?= /tmp/stratalint-pr-a-verification.json
WORKTREE_PATH = $(if $(filter command line,$(origin PATH)),$(PATH),$(abspath ../trureturing-$(NAME)))
.PHONY: help dotnet test tools-test lean-cache-ensure lean lean-report build clean-lanes emit ingest echo-residual-summary selftest gate preflight perf-report deliver-check receipts-stage derived-refresh deposit cover show-atom worktree pr-open refactor-p0-0-gate-authority

help:
	@printf '%s\n' 'make help                         Show this target list' 'make dotnet                       Restore and build .NET with warnings as errors' 'make test                         Run the mathematical gate (Lean, admission, Scribe, values)' 'make tools-test                   Run the .NET harness test suite' 'make lean-cache-ensure            Ensure a private Lean build cache is available' 'make lean                         Build the pinned Lean project' 'make lean-report                  Produce the canonical raw Lean report' 'make build                        Run make dotnet and make lean' 'make clean-lanes [BASE=origin/dev] [FORCE=1]  List reclaimable lanes (dry-run); FORCE=1 removes them' 'make emit                         Emit canonical Scribe documents, catalog, and values' 'make ingest [BASE=origin/dev]     Consume the raw Lean report and align theory receipts' 'make echo-residual-summary [BASE=origin/dev]  Emit the content-addressed residual projection bytes' 'make selftest                     Run deterministic StrataLint selftest' 'make gate [BASE=origin/dev]       Run the local CI-equivalent admission flow' 'make preflight [BASE=origin/dev]  Pre-verify BOTH required CI checks locally before pushing' 'make perf-report [RECENT=10]      Summarize the external performance ledger' 'make deliver-check [BASE=origin/dev]  Run theorem delivery in canonical freeze-last order' 'make receipts-stage [BASE=origin/dev]  Re-derive staged receipts and reject unsafe absorption' 'make derived-refresh [BASE=origin/dev]  Merge base and refresh all derived artifacts' 'make deposit ATOM_ID=x GID=g [BASE=origin/dev]  Deposit theorem, freeze, and receipt in two commits' 'make cover ATOM_ID=x GID=g [BASE=origin/dev]  Cover an atom and align its post-cover receipt' 'make show-atom ATOM_ID=x          Print and verify one digestion atom without writing' 'make worktree NAME=x [BASE=origin/dev] [PATH=DIR]  Initialize an isolated worktree; .lake is copied, never symlinked' 'make pr-open HEAD=branch TITLE=t [BODY=file]  Open a PR to dev and arm auto-merge' 'make refactor-p0-0-gate-authority OLD_BUILD=sha OUT=file  Produce base-owned expected gate authority'

dotnet:
	@/bin/bash tools/scripts/dotnet-build.sh

test: lean-cache-ensure
	@/bin/bash tools/scripts/math-gate.sh

tools-test:
	@dotnet test tools/StrataLint.sln --configuration Release --verbosity normal

lean-cache-ensure:
	@/bin/bash tools/scripts/worktree/lean-cache-ensure.sh

lean: lean-cache-ensure
	@lake build

lean-report: lean-cache-ensure
	@/bin/bash tools/scripts/report/lean-report.sh

build: lean-cache-ensure dotnet lean

clean-lanes:
	@/bin/bash tools/scripts/clean-lanes.sh --base "$(BASE)" $(if $(filter 1,$(FORCE)),--force,)

emit:
	@/bin/bash tools/scripts/scribe.sh emit

ingest:
	@/bin/bash tools/scripts/ingest.sh "$(BASE)"

echo-residual-summary:
	@/bin/bash tools/scripts/report/echo-residual-summary.sh "$(BASE)"

selftest:
	@/bin/bash tools/scripts/stratalint-selftest.sh

gate:
	@/bin/bash tools/scripts/local-harness-gate.sh --base "$(BASE)" $(GATE_ARGS)

perf-report:
	@/bin/bash tools/scripts/perf-report.sh "$(RECENT)" "$(abspath Golden/perf-budgets.toml)"

deliver-check:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deliver-check "$(BASE)"

receipts-stage:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh receipts-stage "$(BASE)"

derived-refresh:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh derived-refresh "$(BASE)"

deposit:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deposit "$(BASE)" "$(ATOM_ID)" "$(GID)"

cover:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh cover "$(BASE)" "$(ATOM_ID)" "$(GID)"

show-atom:
	@dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- show-atom --atom-id "$(ATOM_ID)"

preflight:
	@/bin/bash tools/scripts/preflight.sh

refactor-p0-0-gate-authority:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- gate-authority --old-build "$(OLD_BUILD)" --out "$(OUT)"

worktree:
	@/bin/bash tools/scripts/worktree-init.sh "$(NAME)" "$(WORKTREE_PATH)" "$(BASE)"

pr-open:
	@/bin/bash tools/scripts/pr.sh open --head "$(HEAD)" --title "$(TITLE)" $(if $(BODY),--body-file "$(BODY)",)
