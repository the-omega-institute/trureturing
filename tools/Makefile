SHELL := /bin/bash
.DEFAULT_GOAL := help

HERE := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
BASE ?= origin/dev
REPOSITORY ?= $(HERE)/..
CHECK_FAST_FILTER := FullyQualifiedName=StrataLint.ArchitectureTests.CapacityPolicyTests.RepositoryHasNoOversizeArtifactOrOverfullDirectory|FullyQualifiedName~StrataLint.ArchitectureTests.RepositoryIoAccessPolicyTests|FullyQualifiedName~StrataLint.ArchitectureTests.BannedApiCoverageTests|FullyQualifiedName=StrataLint.Tests.MakeWorkflowTests.CheckFastFilterIsNonEmptyAndPinsRequiredRepositoryChecks
.PHONY: help dotnet check-fast test engineering-tests selftest update-renderer-contract clean-lanes

help:
	@printf '%s\n' 'make -C tools help                         Show this target list' 'make -C tools dotnet                       Restore and build .NET with warnings as errors' 'make -C tools check-fast                   Run the required fast repository structure checks' 'make -C tools test                         Run the full .NET harness test suite' 'make -C tools engineering-tests MODE=plan|execute HEAD=sha BASE=sha PLAN_FILE=path  Plan or execute affected tests' 'make -C tools selftest                     Run deterministic StrataLint selftest' 'make -C tools update-renderer-contract     Update the fixed synthetic renderer contract' 'make -C tools clean-lanes [BASE=origin/dev] [FORCE=1]  List reclaimable lanes (dry-run); FORCE=1 removes them'

dotnet:
	@/bin/bash $(HERE)/scripts/dotnet-build.sh

check-fast:
	@/bin/bash $(HERE)/scripts/dotnet-test.sh $(HERE)/StrataLint.sln --filter "$(CHECK_FAST_FILTER)"

test:
	@/bin/bash $(HERE)/scripts/dotnet-test.sh $(HERE)/StrataLint.sln

engineering-tests:
	@cd "$(REPOSITORY)" && dotnet run --project "$(HERE)/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" --configuration Release --no-launch-profile -- --mode "$(MODE)" --repository "$(REPOSITORY)" --head "$(HEAD)" --base "$(BASE)" --plan-file "$(PLAN_FILE)"

selftest:
	@/bin/bash $(HERE)/scripts/stratalint-selftest.sh

update-renderer-contract:
	@/bin/bash $(HERE)/scripts/update-renderer-contract.sh

clean-lanes:
	@/bin/bash $(HERE)/scripts/clean-lanes.sh --base "$(BASE)" $(if $(filter 1,$(FORCE)),--force,)
