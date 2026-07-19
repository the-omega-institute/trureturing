SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
WORKTREE_PATH = $(if $(filter command line,$(origin PATH)),$(PATH),$(abspath ../trureturing-$(NAME)))

.PHONY: help dotnet test lean lean-report build c0-renew clean-lanes emit emit-check ingest record-golden selftest gate perf-report worktree

help:
	@printf '%s\n' 'make help                         Show this target list' 'make dotnet                       Restore and build .NET with warnings as errors' 'make test                         Run the .NET test suite' 'make lean                         Build the pinned Lean project' 'make lean-report                  Produce the canonical raw Lean report' 'make build                        Run make dotnet and make lean' 'make c0-renew [BASE=origin/dev]   Renew C0 ceremony projections; admission remains separate' 'make clean-lanes [BASE=origin/dev] [FORCE=1]  List reclaimable lanes (dry-run); FORCE=1 removes them' 'make emit                         Emit canonical Scribe documents, catalog, and values' 'make emit-check                   Check canonical Scribe documents, catalog, and values' 'make ingest [BASE=origin/dev]     Consume the raw Lean report and align theory receipts' 'make record-golden                Record Engine diagnostics into golden TOML' 'make selftest                     Run deterministic StrataLint selftest' 'make gate [BASE=origin/dev]       Run the local CI-equivalent admission flow' 'make preflight [BASE=origin/dev]  Pre-verify BOTH required CI checks locally before pushing' 'make perf-report [RECENT=10]      Summarize the external performance ledger' 'make worktree NAME=x [BASE=origin/dev] [PATH=DIR]  Initialize an isolated worktree; .lake is copied, never symlinked' 'make pr-open HEAD=branch TITLE=t [BODY=file]  Open a PR to dev and arm auto-merge (canonical PR path)' 'make pr-watch [INTERVAL=60] [CYCLES=360]  Poll armed PRs; BEHIND -> update-branch with local gh identity'

dotnet:
	@/bin/bash Meta/StrataLint/scripts/dotnet-build.sh

test:
	@dotnet test Meta/StrataLint/StrataLint.sln --configuration Release --verbosity normal

lean:
	@lake build

lean-report:
	@/bin/bash Meta/StrataLint/scripts/report/lean-report.sh

build: dotnet lean

c0-renew:
	@dotnet run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- c0-renew --base "$(BASE)"

clean-lanes:
	@/bin/bash Meta/StrataLint/scripts/clean-lanes.sh --base "$(BASE)" $(if $(filter 1,$(FORCE)),--force,)

emit:
	@/bin/bash Meta/StrataLint/scripts/scribe.sh emit

emit-check:
	@/bin/bash Meta/StrataLint/scripts/scribe.sh check

ingest:
	@/bin/bash Meta/StrataLint/scripts/ingest.sh "$(BASE)"

record-golden:
	@dotnet run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- golden-record

selftest:
	@/bin/bash Meta/StrataLint/scripts/stratalint-selftest.sh

gate:
	@/bin/bash Meta/StrataLint/scripts/local-harness-gate.sh --base "$(BASE)" $(GATE_ARGS)

perf-report:
	@/bin/bash Meta/StrataLint/scripts/perf-report.sh "$(RECENT)"

preflight:
	@/bin/bash Meta/StrataLint/scripts/preflight.sh

worktree:
	@/bin/bash Meta/StrataLint/scripts/worktree-init.sh "$(NAME)" "$(WORKTREE_PATH)" "$(BASE)"

pr-open:
	@/bin/bash Meta/StrataLint/scripts/pr-shepherd.sh open "$(HEAD)" "$(TITLE)" $(BODY)

pr-watch:
	@/bin/bash Meta/StrataLint/scripts/pr-shepherd.sh watch $(INTERVAL) $(CYCLES)
