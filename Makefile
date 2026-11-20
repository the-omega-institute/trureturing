SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
AUTO_MERGE ?= 1
DRAFT ?= 0
ALLOW_LOW_DISK ?= 0
WORKTREE_DEST = $(if $(DEST),$(DEST),../trureturing-$(NAME))
LEAN_REPORT ?= .lake/build/stratalint/raw-lean-report.json
LEAN_REPORT_CACHE_MISS_POLICY ?= reuse-or-build
REBUILD_REPORT_CACHE ?= 0
REGENERATE_REPORT_ARTIFACTS ?= 0
REFRESH_STALE ?= 0
export FULL_BUILD ?= 0
export LEAN_SKIP_LOCK ?= 0
# .NET processes started from these targets create no diagnostic pipes or sockets.
export DOTNET_EnableDiagnostics ?= 0
.PHONY: help test lean-cache-ensure lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib warm-donor lean lean-report lean-report-scoped lean-report-prepare check-lean-report build emit dag filemap filemap-conform scribe-release scribe-release-publish scribe-release-fetch mathlib-reanchor truth-export deliver-check deposit deposit-uncovered worktree worktree-clean worktree-remove worktree-pending worktree-checkpoint worktree-publish worktree-finalize worktree-return worktree-stale pr pr-open pr-watch gate gate-plan ci-unit compiled-judge-test compiled-fib-test require-full-build

require-full-build:
	@test "$(FULL_BUILD)" = 1 || { echo 'full build requires explicit FULL_BUILD=1; use scoped targets instead' >&2; exit 2; }

help:
	@printf '%s\n' 'make pr HEAD=branch MESSAGE=file [AUTO_MERGE=0] [DRAFT=1]  Open a PR and wait for checks; this is no merge certificate; after MERGED and first dev push verification continue in the same worktree from fresh dev per CLAUDE.md 6.1; use worktree-stale when finished; auto-merge defaults on; drafts return without watching CI' 'make pr-open HEAD=branch MESSAGE=file  Same options as make pr' 'make pr-watch PR=number HEAD_SHA=sha  Wait for required CI on the exact commit; this is no merge certificate' 'make lean-cache-ensure FULL_BUILD=1 [RESTORE_DEPENDENCIES=1]  Prepare the cache for a full build' 'make lean LEAN_TARGETS="..." | make lean FULL_BUILD=1 [LEAN_SKIP_LOCK=1]  Build Lean; set LEAN_SKIP_LOCK=1 to skip the shared build lock' 'make test [BASE=origin/dev]  Check current using affected Lean inputs' 'make test FULL_BUILD=1  Run check-lean-report and check-current' 'make worktree KIND=x NAME=y [BASE=origin/dev] [DEST=DIR] [ALLOW_LOW_DISK=1]  Reuse compatible clean trees; notify background maintenance without waiting for cleanup' 'make gate [BASE=origin/dev] [PURPOSE=pull-request|push]  Run all applicable shared CI checks' 'make gate-plan [BASE=origin/dev] [PURPOSE=pull-request|push]  Show identities and applicable checks without execution' 'make ci-unit UNIT=id  Run one declared CI unit with its canonical preparation and evidence' 'make lean-report-scoped LEAN_TARGETS="D5.Module [Reg.Module ...]"  Inspect prebuilt targets, named utility inputs and imports' 'make lean-report-prepare LEAN_TARGETS="..." | make lean-report-prepare FULL_BUILD=1  Build the report tools and inputs' 'make check-lean-report FULL_BUILD=1  Compile, analyze and run required FIB regressions' 'make lean-report FULL_BUILD=1 [REBUILD_REPORT_CACHE=1 | REGENERATE_REPORT_ARTIFACTS=1]  Inspect prebuilt Lean artifacts; regenerate discards generated reports' 'make emit [BASE=origin/dev] [PATHS=FILE] [EMIT_FULL_REPORT=FILE]  Emit from selected scoped Lean inputs or an existing validated full report bundle' 'make dag DIGEST=HEX64 [PREFIX=scribe-resources]  Fetch a published full Scribe pack and render the DAG' 'make filemap  Render FILEMAP on demand from Meta/FILEMAP.toml' 'make filemap-conform [FILEMAP_SCOPE=path | FILEMAP_PRODUCER=name]  Build and run standalone conformance' 'make scribe-release  Rebuild and verify local Scribe release assets' 'make scribe-release-publish TARGET=COMMIT [PREFIX=scribe-resources]  Publish or verify the exact Scribe resource release' 'make scribe-release-fetch DIGEST=HEX64 [PREFIX=scribe-resources]  Fetch and verify the exact Scribe resource pack' 'make worktree-pending  Show the current-agent advisory pending view' \
		'make worktree-checkpoint MESSAGE=FILE  Commit the ordinary whole working snapshot' 'make worktree-publish HEAD=BRANCH [COMMIT=HEAD]  Non-force publication with fresh remote ancestry confirmation' 'make worktree-finalize HEAD=BRANCH WRITERS_JOINED=1  Publish after host joins this task writers' 'make worktree-stale [WORKTREE_PATH=DIR]  Mark the current branch stale' 'make worktree-return [WORKTREE_PATH=DIR]  Same native stale marker' 'make worktree-remove NAMES="DIR [DIR ...]" [FORCE=1]  Remove named worktrees; explicit FORCE=1 disables the 1800-second removal timeout' 'make mathlib-reanchor BASE=REV [OLD_REPORT=PATH]  Reanchor Frozen using the candidate report and optional historical content witness'

ifeq ($(FULL_BUILD),1)
test: require-full-build
	@set -e; paths="$$(mktemp)"; trap 'rm -f "$$paths"' EXIT; git diff --name-only -z "$(BASE)" -- > "$$paths"; git ls-files --others --exclude-standard -z >> "$$paths"; make check-lean-report; dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo; dotnet tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll check-current --candidate-lean-report "$(LEAN_REPORT)" --scribe-paths-from "$$paths"

else
test: export CHECK_BASE := $(value BASE)
test:
	@$(MAKE) -C tools dotnet DOTNET_PROJECT=tools/StrataLint.Cli/StrataLint.Cli.csproj
	@set -e; paths="$$(mktemp)"; trap 'rm -f "$$paths"' EXIT; \
		python3 tools/scripts/workflow/ci_contract.py --base "$$CHECK_BASE" --output "$$paths"; \
		python3 tools/scripts/workflow/ci_pr_lean.py "$$paths"
endif

lean-cache-ensure: require-full-build
	@/bin/bash tools/scripts/worktree/lean-cache-ensure.sh
ifneq ($(origin FULL_BUILD),command line)
lean-cache-ensure: override FULL_BUILD := 0
endif
lean-cache-ensure: export LEAN_CACHE_RESTORE_DEPENDENCIES := $(if $(filter command line,$(origin RESTORE_DEPENDENCIES)),$(value RESTORE_DEPENDENCIES),0)

# Optional integration verification is explicit and validated by the producer.
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_MODE ?= production
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_SOURCE_REF ?=
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_SOURCE_COMMIT ?=
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_REPOSITORY ?= .
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_TAG ?=
lean-cache-to-github-without-mathlib: export LEAN_CACHE_PUBLISH_ONLY ?= 0
lean-cache-from-github-without-mathlib: export LEAN_CACHE_APPROVED_TAG ?=
lean-cache-from-github-without-mathlib: export LEAN_CACHE_APPROVED_PRODUCER ?=
lean-cache-from-github-without-mathlib: export LEAN_CACHE_LOCAL_ASSETS ?=

lean-cache-to-github-without-mathlib: $(if $(filter 1,$(LEAN_CACHE_PUBLISH_ONLY)),,require-full-build)
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh publish --repository "$$LEAN_CACHE_REPOSITORY" --mode "$$LEAN_CACHE_MODE" --source-ref "$$LEAN_CACHE_SOURCE_REF" --source-commit "$$LEAN_CACHE_SOURCE_COMMIT" $(if $(filter 1,$(LEAN_CACHE_PUBLISH_ONLY)),--no-build)

lean-cache-from-github-without-mathlib:
	@args=(); \
	if [[ -n "$$LEAN_CACHE_APPROVED_TAG" ]]; then args+=(--approved-tag "$$LEAN_CACHE_APPROVED_TAG"); fi; \
	if [[ -n "$$LEAN_CACHE_APPROVED_PRODUCER" ]]; then args+=(--approved-producer "$$LEAN_CACHE_APPROVED_PRODUCER"); fi; \
	if [[ -n "$$LEAN_CACHE_LOCAL_ASSETS" ]]; then args+=(--local-assets "$$LEAN_CACHE_LOCAL_ASSETS"); fi; \
	/bin/bash tools/scripts/worktree/lean-cache-publish.sh fetch --repository "$$LEAN_CACHE_REPOSITORY" --mode "$$LEAN_CACHE_MODE" --source-ref "$$LEAN_CACHE_SOURCE_REF" --source-commit "$$LEAN_CACHE_SOURCE_COMMIT" --tag "$$LEAN_CACHE_TAG" $(if $(filter 1,$(REFRESH_STALE)),--refresh-stale) "$${args[@]}"

warm-donor: require-full-build
	@/bin/bash tools/scripts/worktree/warm-donor.sh

lean: $(if $(strip $(LEAN_TARGETS)),,require-full-build)
	@/bin/bash tools/scripts/worktree/lean-cache-run.sh --build $(LEAN_TARGETS)

lean-report: require-full-build
	@/bin/bash tools/scripts/report/lean-report.sh --cache-miss-policy "$(LEAN_REPORT_CACHE_MISS_POLICY)" --rebuild-report-cache "$(REBUILD_REPORT_CACHE)" --regenerate-report-artifacts "$(REGENERATE_REPORT_ARTIFACTS)"

lean-report-scoped:
	@/bin/bash tools/scripts/report/lean-report-scoped.sh --targets "$(LEAN_TARGETS)"

lean-report-prepare: $(if $(strip $(LEAN_TARGETS)),,require-full-build)
	@python3 -B tools/lean-inspector/build_inputs.py prepare --targets "$(LEAN_TARGETS)"

check-lean-report: require-full-build
	@python3 -B tools/lean-inspector/build_inputs.py check --output "$(LEAN_REPORT)"

build: lean

emit:
	@/bin/bash tools/scripts/scribe.sh emit

emit: export BASE ?= origin/dev
emit: export PATHS ?=
emit: export EMIT_FULL_REPORT := $(value EMIT_FULL_REPORT)

PREFIX ?= scribe-resources
DIGEST ?=
SCRIBE_PACK = Generated/$(PREFIX)/$(DIGEST)/scribe-resources.zip

dag:
	@test -n "$(DIGEST)" || { echo 'make dag: DIGEST is required' >&2; exit 2; }; make scribe-release-fetch DIGEST="$(DIGEST)" PREFIX="$(PREFIX)" && dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- dag-render --scribe-pack "$(SCRIBE_PACK)" --scribe-pack-digest "$(DIGEST)"

filemap:
	@dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- filemap

filemap-conform:
	@python3 .github/scripts/filemap-release.py
filemap-conform: export FILEMAP_SCOPE := $(value FILEMAP_SCOPE)
filemap-conform: export FILEMAP_PRODUCER := $(value FILEMAP_PRODUCER)

scribe-release:
	@/bin/bash tools/scripts/scribe-release.sh

scribe-release-publish:
	@/bin/bash tools/scripts/scribe-release.sh publish --prefix "$$PREFIX" --target "$$TARGET"

scribe-release-fetch:
	@/bin/bash tools/scripts/scribe-release.sh fetch "$$DIGEST" --prefix "$$PREFIX"

scribe-release-publish scribe-release-fetch: export PREFIX ?= scribe-resources
scribe-release-publish: export TARGET ?=
scribe-release-fetch: export DIGEST ?=

mathlib-reanchor:
	@/bin/bash tools/scripts/mathlib-reanchor.sh "$(BASE)" "$$REANCHOR_OLD_REPORT"
mathlib-reanchor: export REANCHOR_OLD_REPORT := $(value OLD_REPORT)

truth-export:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- truth-export --out "$(OUT)" --candidate-lean-report "$(LEAN_REPORT)"


deliver-check:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deliver-check "$(BASE)"

deposit:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deposit "$(BASE)" "$(GID)"

deposit-uncovered:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deposit-uncovered "$(BASE)" "$(GID)"

worktree:
	@/bin/bash tools/scripts/worktree-init.sh "$(KIND)" "$(NAME)" "$(WORKTREE_DEST)" "$(BASE)" "$${WORKTREE_ALLOW_LOW_DISK}"
worktree: export WORKTREE_REUSE_ANY := $(if $(DEST),0,1)
worktree: export WORKTREE_ALLOW_LOW_DISK := $(if $(filter command line,$(origin ALLOW_LOW_DISK)),$(value ALLOW_LOW_DISK),0)

worktree-checkpoint:
	@python3 -B tools/scripts/worktree/worktree_protocol.py checkpoint --path . --message-file "$$CHECKPOINT_MESSAGE"
worktree-checkpoint: export CHECKPOINT_MESSAGE := $(value MESSAGE)

worktree-pending:
	@python3 -B tools/scripts/worktree/worktree_protocol.py pending

worktree-publish:
	@python3 -B tools/scripts/worktree/worktree_protocol.py publish --path . --branch "$$PUBLICATION_BRANCH" --commit "$$PUBLICATION_COMMIT"
worktree-publish: export PUBLICATION_BRANCH := $(value HEAD)
worktree-publish: export PUBLICATION_COMMIT := $(if $(COMMIT),$(value COMMIT),HEAD)

worktree-finalize:
	@test "$$FINALIZATION_JOINED" = 1 || { echo 'Host must join this task writers before finalization' >&2; exit 64; }; python3 -B tools/scripts/worktree/worktree_protocol.py finalize --path . --branch "$$PUBLICATION_BRANCH" --writers-joined
worktree-finalize: export PUBLICATION_BRANCH := $(value HEAD)
worktree-finalize: export FINALIZATION_JOINED := $(value WRITERS_JOINED)

worktree-return:
	args=(worktree stale); if test -n "$$RETURN_PATH"; then args+=(--path "$$RETURN_PATH"); fi; dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- "$${args[@]}"
worktree-return: export RETURN_PATH := $(value WORKTREE_PATH)

worktree-stale:
	args=(worktree stale); if test -n "$$STALE_PATH"; then args+=(--path "$$STALE_PATH"); fi; dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- "$${args[@]}"
worktree-stale: export STALE_PATH := $(value WORKTREE_PATH)

worktree-clean:
	@/bin/bash tools/scripts/clean-lanes.sh --base "$(BASE)" --lanes-only --force

worktree-remove:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- worktree remove --names "$${WORKTREE_REMOVE_NAMES}" $(if $(filter command line,$(origin FORCE)),$(if $(filter 1,$(value FORCE)),$(if $(word 2,$(value FORCE)),,--force),))
# Make also exports command-line variables; never expand the original NAMES on that path.
unexport NAMES
worktree-remove: override WORKTREE_REMOVE_NAMES := $(value NAMES)
export WORKTREE_REMOVE_NAMES

pr: pr-open

pr-open:
	@/bin/bash tools/scripts/pr.sh open --head "$(HEAD)" --message-file "$(MESSAGE)" $(if $(filter 1,$(DRAFT)),--draft,$(if $(filter 1,$(AUTO_MERGE)),--auto-merge,)) $(if $(WATCH_TIMEOUT_SECONDS),--timeout-seconds "$(WATCH_TIMEOUT_SECONDS)",) $(if $(WATCH_INTERVAL_SECONDS),--interval-seconds "$(WATCH_INTERVAL_SECONDS)",)

pr-watch:
	@/bin/bash tools/scripts/pr.sh watch --pr "$(PR)" --head-sha "$(HEAD_SHA)" $(if $(WATCH_TIMEOUT_SECONDS),--timeout-seconds "$(WATCH_TIMEOUT_SECONDS)",) $(if $(WATCH_INTERVAL_SECONDS),--interval-seconds "$(WATCH_INTERVAL_SECONDS)",)

gate:
	@/bin/bash tools/scripts/local-harness-gate.sh --base "$$GATE_BASE" --purpose "$$GATE_PURPOSE"
gate: export GATE_BASE := $(value BASE)
gate: export GATE_PURPOSE := $(if $(PURPOSE),$(value PURPOSE),pull-request)

gate-plan:
	@/bin/bash tools/scripts/local-harness-gate.sh --base "$$GATE_BASE" --purpose "$$GATE_PURPOSE" --plan
gate-plan: export GATE_BASE := $(value BASE)
gate-plan: export GATE_PURPOSE := $(if $(PURPOSE),$(value PURPOSE),pull-request)

ci-unit:
	@python3 tools/scripts/workflow/ci_checks.py local-unit "$$CI_UNIT"
ci-unit: export CI_UNIT := $(value UNIT)

compiled-judge-test:
	@/bin/bash tools/scripts/compiled-judge-test.sh

compiled-fib-test:
	@/bin/bash tools/scripts/compiled-fib-test.sh
