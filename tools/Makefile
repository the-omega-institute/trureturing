SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
OUT ?= /tmp/stratalint-pr-a-verification.json
.PHONY: help dotnet test selftest perf-report clean-lanes refactor-p0-0-gate-authority

help:
	@printf '%s\n' 'make -C tools help                         Show this target list' 'make -C tools dotnet                       Restore and build .NET with warnings as errors' 'make -C tools test                         Run the .NET harness test suite' 'make -C tools selftest                     Run deterministic StrataLint selftest' 'make -C tools perf-report [RECENT=10]      Summarize the external performance ledger' 'make -C tools clean-lanes [BASE=origin/dev] [FORCE=1]  List reclaimable lanes (dry-run); FORCE=1 removes them' 'make -C tools refactor-p0-0-gate-authority OLD_BUILD=sha OUT=file  Produce base-owned expected gate authority'

dotnet:
	@/bin/bash scripts/dotnet-build.sh

test:
	@dotnet test StrataLint.sln --configuration Release --verbosity normal

selftest:
	@/bin/bash scripts/stratalint-selftest.sh

perf-report:
	@/bin/bash scripts/perf-report.sh "$(RECENT)" "$(abspath ../Golden/perf-budgets.toml)"

clean-lanes:
	@/bin/bash scripts/clean-lanes.sh --base "$(BASE)" $(if $(filter 1,$(FORCE)),--force,)

refactor-p0-0-gate-authority:
	@dotnet run --project StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- gate-authority --old-build "$(OLD_BUILD)" --out "$(OUT)"
