SHELL := /bin/bash
.DEFAULT_GOAL := help

HERE := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
BASE ?= origin/dev
REPOSITORY ?= $(HERE)/..
.PHONY: help dotnet test engineering-tests selftest capacity-audit update-renderer-contract clean-lanes

help:
	@printf '%s\n' 'make -C tools help                         Show this target list' 'make -C tools dotnet                       Restore and build .NET with warnings as errors' 'make -C tools test                         Run the full .NET harness test suite' 'make -C tools engineering-tests MODE=plan|execute HEAD=sha BASE=sha PLAN_FILE=path  Plan or execute affected tests' 'make -C tools selftest                     Run deterministic StrataLint selftest' 'make -C tools capacity-audit [REPOSITORY=path]  Audit the current git index against repository capacity limits' 'make -C tools update-renderer-contract     Update the fixed synthetic renderer contract' 'make -C tools clean-lanes [BASE=origin/dev] [FORCE=1]  List reclaimable lanes (dry-run); FORCE=1 removes them'

dotnet:
	@/bin/bash $(HERE)/scripts/dotnet-build.sh

test:
	@/bin/bash $(HERE)/scripts/dotnet-test.sh $(HERE)/StrataLint.sln

engineering-tests:
	@cd "$(REPOSITORY)" && dotnet run --project "$(HERE)/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" --configuration Release --no-launch-profile -- --mode "$(MODE)" --repository "$(REPOSITORY)" --head "$(HEAD)" --base "$(BASE)" --plan-file "$(PLAN_FILE)"

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
