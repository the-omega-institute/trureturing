SHELL := /bin/bash
.DEFAULT_GOAL := help

HERE := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
BASE ?= origin/dev
REPOSITORY ?= $(HERE)/..
XI_MODE ?= mps
XI_FIRST ?= 1
XI_LAST ?= 1399999
XI_CHUNK ?= 65536
XI_PRECISION ?= 256
XI_DIGITS ?= 40
XI_STATE ?= /tmp/qgh-xi-quantization-state
XI_REPORT ?= /tmp/qgh-xi-quantization-state/report.md
CHECK_FAST_FILTER := FullyQualifiedName~StrataLint.Tests.CapacityAuditCommandTests|FullyQualifiedName~StrataLint.ArchitectureTests.RepositoryIoAccessPolicyTests|FullyQualifiedName~StrataLint.ArchitectureTests.BannedApiCoverageTests|FullyQualifiedName=StrataLint.Tests.MakeWorkflowTests.CheckFastFilterIsNonEmptyAndPinsRequiredRepositoryChecks
.PHONY: help dotnet check-fast test ci-build engineering engineering-tests selftest capacity-audit update-renderer-contract clean-lanes xi-quantization xi-quantization-test

help:
	@printf '%s\n' 'make -C tools help                         Show this target list' 'make -C tools dotnet                       Restore and build .NET with warnings as errors' 'make -C tools check-fast                   Run the required fast repository structure checks' 'make -C tools test                         Run the full .NET harness test suite' 'make -C tools ci-build                     Prepare and seal this round’s shared build' 'make -C tools engineering                  Restore, build, test every current project, selftest, and prove compile failures' 'make -C tools engineering-tests           Run every current test project once using built outputs' 'make -C tools selftest                     Run deterministic StrataLint selftest' 'make -C tools capacity-audit [REPOSITORY=path]  Audit the current git index against repository capacity limits' 'make -C tools update-renderer-contract     Update the fixed synthetic renderer contract' 'make -C tools clean-lanes [BASE=origin/dev] [FORCE=1]  List reclaimable lanes (dry-run); FORCE=1 removes them' 'make -C tools xi-quantization [XI_MODE=mps|cpu] [XI_REPORT=path]  Certify the fixed xi resolution prefix; default 1..1399999 on MPS' 'make -C tools xi-quantization-test         Run exact scientific behavior tests (no GPU)'

dotnet:
	@/bin/bash $(HERE)/scripts/dotnet-build.sh

xi-quantization:
	@PYTHONDONTWRITEBYTECODE=1 PYTORCH_ENABLE_MPS_FALLBACK=0 uv run --python 3.12 --with torch==2.8.0 --with numpy==2.0.2 --with python-flint==0.8.0 python "$(HERE)/scripts/agent/xi_quantization.py" --mode "$(XI_MODE)" --first "$(XI_FIRST)" --last "$(XI_LAST)" --chunk "$(XI_CHUNK)" --precision "$(XI_PRECISION)" --digits "$(XI_DIGITS)" --state-dir "$(XI_STATE)" --report "$(XI_REPORT)"

xi-quantization-test:
	@python3 -B "$(HERE)/scripts/agent/test_xi_quantization.py"

check-fast:
	@/bin/bash $(HERE)/scripts/dotnet-test.sh $(HERE)/StrataLint.sln --filter "$(CHECK_FAST_FILTER)"

test:
	@/bin/bash $(HERE)/scripts/dotnet-test.sh $(HERE)/StrataLint.sln

ci-build:
	@/bin/bash "$(HERE)/scripts/ci-stage.sh" build

engineering:
	@/bin/bash "$(HERE)/scripts/ci-stage.sh" engineering

engineering-tests:
	@cd "$(REPOSITORY)" && dotnet "$(HERE)/StrataLint.EngineeringScope/bin/Release/net10.0/StrataLint.EngineeringScope.dll" --repository "$(REPOSITORY)" --all

selftest:
	@/bin/bash $(HERE)/scripts/stratalint-selftest.sh

capacity-audit: export CAPACITY_AUDIT_REPOSITORY := $(REPOSITORY)
capacity-audit: export CAPACITY_AUDIT_HERE := $(HERE)
capacity-audit:
	@set -u; result() { printf 'CAPACITY_AUDIT_RESULT exit=%s reason=%s\n' "$$1" "$$2"; exit "$$1"; }; repository="$${CAPACITY_AUDIT_REPOSITORY-}"; project="$${CAPACITY_AUDIT_HERE-}/StrataLint.Cli/StrataLint.Cli.csproj"; test -n "$$repository" || result 2 missing-repository; test -f "$$project" || result 2 missing-cli-project; git -C "$$repository" rev-parse --is-inside-work-tree >/dev/null 2>&1 || result 2 invalid-repository; cd "$$repository" || result 2 repository-unavailable; build_status=0; build_output="$$(dotnet build "$$project" --configuration Release --nologo 2>&1)" || build_status=$$?; if test "$$build_status" -ne 0; then printf '%s\n' "$$build_output"; result 2 build-failed; fi; audit_status=0; audit_output="$$(dotnet run --project "$$project" --configuration Release --no-build --no-restore --no-launch-profile -- capacity-audit 2>&1)" || audit_status=$$?; test -z "$$audit_output" || printf '%s\n' "$$audit_output"; case "$$audit_status" in 0) result 0 clean ;; 1) printf '%s\n' "$$audit_output" | grep -q '^CAPACITY_AUDIT ' && result 1 capacity-violation; result 2 unattributed-policy-exit ;; 2) printf '%s\n' "$$audit_output" | grep -q '^INFRASTRUCTURE_FAILURE capacity-audit:' && result 2 cli-infrastructure-failure; result 2 launcher-failed ;; *) result 2 launcher-failed ;; esac

update-renderer-contract:
	@/bin/bash $(HERE)/scripts/update-renderer-contract.sh

clean-lanes:
	@/bin/bash $(HERE)/scripts/clean-lanes.sh --base "$(BASE)" $(if $(filter 1,$(FORCE)),--force,)
