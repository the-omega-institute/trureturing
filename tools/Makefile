SHELL := /bin/bash
.DEFAULT_GOAL := help

# Remove Make's leading list separator without collapsing spaces in the source path.
tools_makefile_hash := \#
HERE := $(shell tools_makefile="$(MAKEFILE_LIST)"; cd "$$(dirname "$${tools_makefile$(tools_makefile_hash) }")" && pwd -P)
BASE ?= origin/dev
REPOSITORY ?= $(HERE)/..
CLEAN_MIN_AGE_HOURS ?= 24
CLEAN_CODEX_HOME ?= $(if $(CODEX_HOME),$(CODEX_HOME),$(HOME)/.codex)
CLEAN_SSHX_HOME ?= $(if $(SSHX_HOME),$(SSHX_HOME),$(HOME)/.sshx)
CLEAN_TMP_ROOT ?=
FORCE ?= 0
VERBOSE ?= 0
XI_MODE ?= mps
XI_FIRST ?= 1
XI_LAST ?= 1399999
XI_CHUNK ?= 65536
XI_PRECISION ?= 256
XI_DIGITS ?= 40
XI_STATE ?= /tmp/qgh-xi-quantization-state
XI_REPORT ?= /tmp/qgh-xi-quantization-state/report.md
SLAB_FIRST ?=
SLAB_LAST ?=
SLAB_CHUNK ?= 64
SLAB_MAX_CHUNKS ?= 0
SLAB_PRECISIONS ?= 128,256,512
SLAB_STATE ?= $(HOME)/.local/state/qgh-prime-slab-pilot-0909
EXPERIMENTS_ROOT ?= $(HERE)/../../trureturing-experiments
SLAB_INPUT ?= $(EXPERIMENTS_ROOT)/docs/reports/prime-slab-corner-order-0909.json
SLAB_INPUT_SHA ?= 9d28055d5255580ed58274822359961483d1deecbb7b4e38ce497948a4808672
SLAB_ENV = PYTHONDONTWRITEBYTECODE=1 PYTORCH_ENABLE_MPS_FALLBACK=0 uv run --python 3.12 --with torch==2.8.0 --with numpy==2.0.2 --with python-flint==0.8.0 python
CPU_SLAB_INPUT ?=
CPU_SLAB_SHA ?=
CPU_SLAB_OUTPUT ?=
CPU_SLAB_PHASE ?= pilot
CPU_SLAB_BOXES ?= 64
CPU_SLAB_DEADLINE ?=
TEST_PROJECT ?= $(HERE)/StrataLint.sln
SELECTED_TEST_PROJECT = $(if $(filter tools/%,$(TEST_PROJECT)),$(abspath $(HERE)/../$(TEST_PROJECT)),$(TEST_PROJECT))
TEST_FILTER ?=
FILEMAP_SCOPE ?=
FILEMAP_PRODUCER ?=
SEED_EXPORT ?= automatic
INHERITED_DOTNET_ROOT := $(DOTNET_ROOT)
RESOLVED_DOTNET_ROOT = $(if $(strip $(INHERITED_DOTNET_ROOT)),$(INHERITED_DOTNET_ROOT),$(shell sdk_version="$$(cd "$(REPOSITORY)" && dotnet --version)"; dotnet --list-sdks | awk -v version="$$sdk_version" '$$1 == version { path = $$0; sub(/^[^[]*\[/, "", path); sub(/\]$$/, "", path); sub(/\/sdk$$/, "", path); print path; exit }'))
CHECK_FAST_FILTER := FullyQualifiedName~StrataLint.Tests.CapacityAuditCommandTests|FullyQualifiedName~StrataLint.ArchitectureTests.RepositoryIoAccessPolicyTests|FullyQualifiedName~StrataLint.ArchitectureTests.BannedApiCoverageTests|FullyQualifiedName=StrataLint.WorkflowScript.Tests.MakeWorkflowTests.CheckFastFilterIsNonEmptyAndPinsRequiredRepositoryChecks
.PHONY: auric-fib-universal-test auric-fib-report auric-fib-compiled-test auric-fib-analysis-build auric-fib-analysis auric-fib-analysis-test help settle-batch dotnet check-fast test selftest compile-proof filemap-conform capacity-audit update-renderer-contract clean-lanes clean-all xi-quantization xi-quantization-test prime-slab-search prime-slab-test prime-slab-device-test prime-slab-verify prime-slab-mutation-test prime-slab-cpu prime-slab-cpu-test prime-slab-cpu-mutation-test

help:
	@printf '%s\n' 'make -C tools help                         Show this target list' 'make -C tools auric-fib-analysis-build      Compile the finite consumer and rate boundary check' 'make -C tools auric-fib-analysis <request.json  Exact finite SPEC 9 analysis (add -s for JSON stdout)' 'make -C tools auric-fib-analysis-test       Native execution, exact laws, kernels, layers and boundary tests' 'make -C tools auric-fib-report              Generate FIB readings from compilation artifacts' 'make -C tools auric-fib-compiled-test       Verify compiler artifacts and incremental FIB consumers' 'make -C tools auric-fib-universal-test      Verify source-owned universal contracts through canonical report consumers' 'make -C tools settle-batch REQUESTS=file   Settle strict TOML [[requests]] in order; stop at the first failed record' 'make -C tools filemap-conform [FILEMAP_SCOPE=path | FILEMAP_PRODUCER=name]  Build and run standalone FileMap' 'make -C tools dotnet [DOTNET_PROJECT=tools/path.csproj]  Restore and build the selected project or full solution with warnings as errors' 'make -C tools check-fast                   Run the required fast repository structure checks' 'make -C tools test                         Run the full .NET harness test suite' 'make -C tools compile-proof PROOF=capability-proof|banned-api-proof  Verify one expected compiler rejection' 'make -C tools selftest                     Run deterministic StrataLint selftest' 'make -C tools capacity-audit [REPOSITORY=path]  Audit the current git index against repository capacity limits' 'make -C tools update-renderer-contract     Update the fixed synthetic renderer contract' 'make -C tools clean-lanes [BASE=origin/dev] [FORCE=1]  Preview (dry-run) worktrees inactive for 24h and 300+ commits behind BASE, including eligible worktree-init locks; FORCE=1 executes. Unlocked trees keep the legacy policy and can lose uncommitted/untracked work; initialization-locked trees additionally require complete idle host activity, index/checkout and private/retiring-branch history verification; locks stay in place until native double-force removal; full preview/force defers orphan/temp sweeps while any observed lock remains or a lane attachment/removal is unresolved, including fresh registrations; direct eligible lane cleanup continues, preview does not discharge locks, and JSONL reports extra_sweeps' 'make -C tools clean-all [FORCE=1] [CLEAN_MIN_AGE_HOURS=24] [VERBOSE=1]  Preview Codex, sshx, temporary artifacts and stale worktrees; FORCE=1 deletes; optional CLEAN_CODEX_HOME, CLEAN_SSHX_HOME, CLEAN_TMP_ROOT' 'make -C tools xi-quantization [XI_MODE=mps|cpu] [XI_REPORT=path]  Certify the fixed xi resolution prefix; default 1..1399999 on MPS' 'make -C tools xi-quantization-test         Run exact scientific behavior tests (no GPU)' 'make -C tools prime-slab-search SLAB_FIRST=id SLAB_LAST=id [SLAB_STATE=external-path] [SLAB_CHUNK=64] [SLAB_MAX_CHUNKS=0]  Bounded MPS prime slabs; 0 max-chunks means finish the explicit window' 'make -C tools prime-slab-test              Scientific and durable-state tests (CPU synthetic fixtures)' 'make -C tools prime-slab-device-test       Locked, bounded synthetic Metal correctness probes (no box search)' 'make -C tools prime-slab-verify SLAB_FIRST=id SLAB_LAST=id  Independently revalidate the saved GPU stream (no generation)' 'make -C tools prime-slab-mutation-test      Predict and verify named scientific test failures; receipts under SLAB_STATE' 'make -C tools prime-slab-cpu CPU_SLAB_INPUT=file CPU_SLAB_SHA=sha256 CPU_SLAB_OUTPUT=directory CPU_SLAB_PHASE=pilot|window CPU_SLAB_BOXES=count CPU_SLAB_DEADLINE=UTC  Foreground actual-prime CPU inquiry' 'make -C tools prime-slab-cpu-test          Exact-input, guard, resume and budget tests; no GPU' 'make -C tools prime-slab-cpu-mutation-test  Verify named CPU inquiry test failures with synthetic fixtures'

dotnet:
	@/bin/bash "$(HERE)/scripts/dotnet-build.sh" "$${DOTNET_PROJECT}"
dotnet: export DOTNET_PROJECT := $(value DOTNET_PROJECT)

filemap-conform:
	@set -e; cd "$(REPOSITORY)"; dotnet build "$(HERE)/StrataLint.FileMap/StrataLint.FileMap.csproj" --configuration Release -p:RestoreLockedMode=true -nr:false -nologo --verbosity quiet; args=(); if test -n "$$FILEMAP_SCOPE"; then args+=(--scope "$$FILEMAP_SCOPE"); fi; if test -n "$$FILEMAP_PRODUCER"; then args+=(--producer-write-set "$$FILEMAP_PRODUCER"); fi; dotnet "$(HERE)/StrataLint.FileMap/bin/Release/net10.0/StrataLint.FileMap.dll" "$${args[@]}"
filemap-conform: export FILEMAP_SCOPE := $(value FILEMAP_SCOPE)
filemap-conform: export FILEMAP_PRODUCER := $(value FILEMAP_PRODUCER)

xi-quantization:
	@PYTHONDONTWRITEBYTECODE=1 PYTORCH_ENABLE_MPS_FALLBACK=0 uv run --python 3.12 --with torch==2.8.0 --with numpy==2.0.2 --with python-flint==0.8.0 python "$(HERE)/scripts/agent/xi_quantization.py" --mode "$(XI_MODE)" --first "$(XI_FIRST)" --last "$(XI_LAST)" --chunk "$(XI_CHUNK)" --precision "$(XI_PRECISION)" --digits "$(XI_DIGITS)" --state-dir "$(XI_STATE)" --report "$(XI_REPORT)"

xi-quantization-test:
	@python3 -B "$(HERE)/scripts/agent/test_xi_quantization.py"

prime-slab-test:
	@$(SLAB_ENV) "$(HERE)/scripts/agent/test_prime_slab_search.py"

prime-slab-cpu:
	@$(SLAB_ENV) "$(HERE)/scripts/agent/prime_slab_cpu.py" --input "$${CPU_SLAB_INPUT}" --input-sha256 "$${CPU_SLAB_SHA}" --output "$${CPU_SLAB_OUTPUT}" --phase "$${CPU_SLAB_PHASE}" --max-boxes "$${CPU_SLAB_BOXES}" --deadline "$${CPU_SLAB_DEADLINE}"
prime-slab-cpu: export CPU_SLAB_INPUT := $(value CPU_SLAB_INPUT)
prime-slab-cpu: export CPU_SLAB_SHA := $(value CPU_SLAB_SHA)
prime-slab-cpu: export CPU_SLAB_OUTPUT := $(value CPU_SLAB_OUTPUT)
prime-slab-cpu: export CPU_SLAB_PHASE := $(value CPU_SLAB_PHASE)
prime-slab-cpu: export CPU_SLAB_BOXES := $(value CPU_SLAB_BOXES)
prime-slab-cpu: export CPU_SLAB_DEADLINE := $(value CPU_SLAB_DEADLINE)

prime-slab-cpu-test:
	@$(SLAB_ENV) "$(HERE)/scripts/agent/prime_slabs/test_cpu.py"

prime-slab-cpu-mutation-test:
	@$(SLAB_ENV) "$(HERE)/scripts/agent/prime_slabs/test_cpu.py" --mutation-check

prime-slab-mutation-test:
	@$(SLAB_ENV) "$(HERE)/scripts/agent/test_prime_slab_search.py" --mutation-dir "$(SLAB_STATE)"

prime-slab-search:
	@$(SLAB_ENV) "$(HERE)/scripts/agent/prime_slab_search.py" search --first-box "$(SLAB_FIRST)" --last-box "$(SLAB_LAST)" --chunk-boxes "$(SLAB_CHUNK)" --max-chunks "$(SLAB_MAX_CHUNKS)" --precisions "$(SLAB_PRECISIONS)" --state-dir "$(SLAB_STATE)" --input "$(SLAB_INPUT)" --input-sha256 "$(SLAB_INPUT_SHA)"

prime-slab-verify:
	@$(SLAB_ENV) "$(HERE)/scripts/agent/prime_slab_search.py" verify --first-box "$(SLAB_FIRST)" --last-box "$(SLAB_LAST)" --chunk-boxes "$(SLAB_CHUNK)" --max-chunks "$(SLAB_MAX_CHUNKS)" --precisions "$(SLAB_PRECISIONS)" --state-dir "$(SLAB_STATE)" --input "$(SLAB_INPUT)" --input-sha256 "$(SLAB_INPUT_SHA)"

prime-slab-device-test:
	@$(SLAB_ENV) "$(HERE)/scripts/agent/prime_slab_search.py" device-test --state-dir "$(SLAB_STATE)" --input "$(SLAB_INPUT)" --input-sha256 "$(SLAB_INPUT_SHA)"

check-fast:
	@/bin/bash $(HERE)/scripts/dotnet-test.sh $(HERE)/StrataLint.sln --filter "$(CHECK_FAST_FILTER)"

test:
	@/bin/bash $(HERE)/scripts/dotnet-test.sh "$(SELECTED_TEST_PROJECT)" $(if $(TEST_FILTER),--filter "$(TEST_FILTER)",)
test: export DOTNET_ROOT := $(RESOLVED_DOTNET_ROOT)

compile-proof:
	@test "$(PROOF)" = capability-proof -o "$(PROOF)" = banned-api-proof || { echo "PROOF must be capability-proof or banned-api-proof" >&2; exit 2; }; cd "$(REPOSITORY)" && dotnet build "$(HERE)/StrataLint.TestEvidence/StrataLint.TestEvidence.csproj" --configuration Release -p:RestoreLockedMode=true -nr:false -nologo --verbosity quiet && dotnet "$(HERE)/StrataLint.TestEvidence/bin/Release/net10.0/StrataLint.TestEvidence.dll" compile-proof "$(PROOF)"

selftest:
	@/bin/bash $(HERE)/scripts/stratalint-selftest.sh

capacity-audit: export CAPACITY_AUDIT_REPOSITORY := $(REPOSITORY)
capacity-audit: export CAPACITY_AUDIT_HERE := $(HERE)
capacity-audit:
	@set -u; result() { printf 'CAPACITY_AUDIT_RESULT exit=%s reason=%s\n' "$$1" "$$2"; exit "$$1"; }; repository="$${CAPACITY_AUDIT_REPOSITORY-}"; project="$${CAPACITY_AUDIT_HERE-}/StrataLint.Cli/StrataLint.Cli.csproj"; test -n "$$repository" || result 2 missing-repository; test -f "$$project" || result 2 missing-cli-project; git -C "$$repository" rev-parse --is-inside-work-tree >/dev/null 2>&1 || result 2 invalid-repository; cd "$$repository" || result 2 repository-unavailable; build_status=0; build_output="$$(dotnet build "$$project" --configuration Release --nologo 2>&1)" || build_status=$$?; if test "$$build_status" -ne 0; then printf '%s\n' "$$build_output"; result 2 build-failed; fi; audit_status=0; audit_output="$$(dotnet run --project "$$project" --configuration Release --no-build --no-restore --no-launch-profile -- capacity-audit 2>&1)" || audit_status=$$?; test -z "$$audit_output" || printf '%s\n' "$$audit_output"; case "$$audit_status" in 0) result 0 clean ;; 1) printf '%s\n' "$$audit_output" | grep -q '^CAPACITY_AUDIT ' && result 1 capacity-violation; result 2 unattributed-policy-exit ;; 2) printf '%s\n' "$$audit_output" | grep -q '^INFRASTRUCTURE_FAILURE capacity-audit:' && result 2 cli-infrastructure-failure; result 2 launcher-failed ;; *) result 2 launcher-failed ;; esac

update-renderer-contract:
	@/bin/bash $(HERE)/scripts/update-renderer-contract.sh

clean-lanes:
	@/bin/bash "$(HERE)/scripts/clean-lanes.sh" --base "$(BASE)" $(if $(filter 1,$(FORCE)),--force,)

clean-all:
	@args=(clean --repository "$$HOST_CLEAN_REPOSITORY" --base "$$HOST_CLEAN_BASE" --min-age-hours "$$HOST_CLEAN_MIN_AGE_HOURS" --codex-home "$$HOST_CLEAN_CODEX_HOME" --sshx-home "$$HOST_CLEAN_SSHX_HOME"); case "$$HOST_CLEAN_FORCE" in 0) ;; 1) args+=(--delete);; *) echo 'FORCE must be 0 or 1' >&2; exit 64;; esac; case "$$HOST_CLEAN_VERBOSE" in 0) ;; 1) args+=(--verbose);; *) echo 'VERBOSE must be 0 or 1' >&2; exit 64;; esac; if test -n "$$HOST_CLEAN_TMP_ROOT"; then args+=(--tmp-root "$$HOST_CLEAN_TMP_ROOT"); fi; exec python3 -B "$(HERE)/scripts/host-cleanup.py" "$${args[@]}"
clean-all: export HOST_CLEAN_REPOSITORY := $(REPOSITORY)
clean-all: export HOST_CLEAN_BASE := $(value BASE)
clean-all: export HOST_CLEAN_MIN_AGE_HOURS := $(value CLEAN_MIN_AGE_HOURS)
clean-all: export HOST_CLEAN_CODEX_HOME := $(CLEAN_CODEX_HOME)
clean-all: export HOST_CLEAN_SSHX_HOME := $(CLEAN_SSHX_HOME)
clean-all: export HOST_CLEAN_TMP_ROOT := $(value CLEAN_TMP_ROOT)
clean-all: export HOST_CLEAN_FORCE := $(value FORCE)
clean-all: export HOST_CLEAN_VERBOSE := $(value VERBOSE)

settle-batch:
	@test -n "$${SETTLE_BATCH_REQUESTS}" || { printf '%s\n' 'SETTLE_BATCH_INPUT_INVALID REQUESTS is required' >&2; exit 2; }; cd "$(REPOSITORY)" && dotnet run --project "$(HERE)/StrataLint.Cli/StrataLint.Cli.csproj" --configuration Release -- settle-batch --requests "$${SETTLE_BATCH_REQUESTS}"
settle-batch: export SETTLE_BATCH_REQUESTS := $(value REQUESTS)
unexport REQUESTS

auric-fib-analysis-build:
	@$(MAKE) --no-print-directory -C "$(REPOSITORY)" lean LEAN_TARGETS="LeanInformationAuditRegAnalysis.AuricFib.Main LeanInformationAuditRegTests.AuricFib.RateBoundary" >&2

auric-fib-analysis: auric-fib-analysis-build
	@/bin/bash "$(HERE)/scripts/auric-fib-analysis.sh"

auric-fib-analysis-test: auric-fib-analysis-build
	@/bin/bash "$(HERE)/scripts/auric-fib-analysis.sh" --test

auric-fib-report:
	@$(MAKE) --no-print-directory -C "$(REPOSITORY)" lean-report >&2 && python3 -B "$(HERE)/lean-inspector/fib_analysis.py" "$(REPOSITORY)/.lake/build/stratalint/raw-lean-report.json"

# These are compiler-to-consumer production contract fixtures.
auric-fib-compiled-test:
	@$(MAKE) --no-print-directory -C "$(REPOSITORY)" lean LEAN_TARGETS="leanInspector/reportInspector leanInspector/inputDiscovery LeanInformationAuditRegAnalysis.AuricFib.Main Reg.D5.S3.Arith.FibonacciAtomic.NativeContinuation.NullReplyFiber" >&2 && $(MAKE) --no-print-directory test TEST_PROJECT=tools/tests/StrataLint.Lean.Tests/StrataLint.Lean.Tests.csproj TEST_FILTER=FullyQualifiedName~CompiledFibIntegrationTests

# Source-owned generic clients use the same report facets and custody consumer.
auric-fib-universal-test:
	@$(MAKE) --no-print-directory -C "$(REPOSITORY)" lean LEAN_TARGETS="leanInspector/reportInspector LeanInformationAuditRegAnalysis.AuricFib.Main LeanInformationAuditRegTests.AuricFib.UniversalFixture" >&2
	@cd "$(REPOSITORY)" && python3 -B tools/lean-inspector/tests/test_auric_fib_universal.py -v
