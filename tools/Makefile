SHELL := /bin/bash
.DEFAULT_GOAL := help

HERE := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
BASE ?= origin/dev
.PHONY: help dotnet test engineering-tests selftest update-renderer-contract perf-report clean-lanes

help:
	@printf '%s\n' 'make -C tools help                         Show this target list' 'make -C tools dotnet                       Restore and build .NET with warnings as errors' 'make -C tools test                         Run the full .NET harness test suite' 'make -C tools engineering-tests MODE=plan|execute HEAD=sha BASE=sha PLAN_FILE=path  Plan or execute affected tests' 'make -C tools selftest                     Run deterministic StrataLint selftest' 'make -C tools update-renderer-contract     Update the fixed synthetic renderer contract' 'make -C tools perf-report [RECENT=10]      Summarize the external performance ledger' 'make -C tools clean-lanes [BASE=origin/dev] [FORCE=1]  List reclaimable lanes (dry-run); FORCE=1 removes them'

dotnet:
	@/bin/bash $(HERE)/scripts/dotnet-build.sh

test:
	@dotnet test $(HERE)/StrataLint.sln --configuration Release --verbosity normal

engineering-tests:
	@cd $(HERE)/.. && dotnet run --project tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj --configuration Release --no-launch-profile -- --mode "$(MODE)" --repository "$(HERE)/.." --head "$(HEAD)" --base "$(BASE)" --plan-file "$(PLAN_FILE)"

selftest:
	@/bin/bash $(HERE)/scripts/stratalint-selftest.sh

update-renderer-contract:
	@/bin/bash $(HERE)/scripts/update-renderer-contract.sh

perf-report:
	@/bin/bash $(HERE)/scripts/perf-report.sh "$(RECENT)" "$(HERE)/../Golden/perf-budgets.toml"

clean-lanes:
	@/bin/bash $(HERE)/scripts/clean-lanes.sh --base "$(BASE)" $(if $(filter 1,$(FORCE)),--force,)
