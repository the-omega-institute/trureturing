SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
AUTO_MERGE ?= 1
DRAFT ?= 0
ALLOW_LOW_DISK ?= 0
WORKTREE_DEST = $(if $(DEST),$(DEST),../trureturing-$(NAME))
LEAN_REPORT ?= .lake/build/stratalint/raw-lean-report.json
LEAN_REPORT_CACHE_MISS_POLICY ?= fetch-or-fail
REBUILD_REPORT_CACHE ?= 0
REGENERATE_REPORT_ARTIFACTS ?= 0
REFRESH_STALE ?= 0
export LEAN_SKIP_LOCK ?= 0
# .NET processes started from these targets create no diagnostic pipes or sockets.
export DOTNET_EnableDiagnostics ?= 0
.PHONY: help test lean-cache-ensure lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib warm-donor lean lean-report lean-report-scoped build emit dag filemap filemap-conform scribe-release scribe-release-publish scribe-release-fetch ingest mathlib-reanchor source-dispatch search-atoms show-atom atom-context truth-export deliver-check deposit deposit-uncovered cover cover-batch decompose settle settle-clear worktree worktree-clean worktree-remove worktree-checkpoint worktree-publish worktree-finalize pr pr-open pr-watch gate gate-plan ci-unit compiled-judge-test compiled-fib-test search-reduction search-reduction-run search-reduction-test search-reduction-replay-test search-reduction-replay-calibration search-reduction-replay-faults search-reduction-replay-real-negative search-reduction-replay-vocabulary

help:
	@printf '%s\n' 'make pr HEAD=branch MESSAGE=file [AUTO_MERGE=0] [DRAFT=1]  Open a PR; auto-merge defaults on; drafts return without merging or watching CI' 'make pr-open HEAD=branch MESSAGE=file  Same options as make pr' 'make pr-watch PR=number HEAD_SHA=sha  Wait for required CI on the exact commit' 'make lean [LEAN_TARGETS="..."] [LEAN_SKIP_LOCK=1]  Build Lean; set LEAN_SKIP_LOCK=1 to skip the shared build lock' 'make test  Run lean-report and check-current' 'make worktree KIND=x NAME=y [BASE=origin/dev] [DEST=DIR] [ALLOW_LOW_DISK=1]  Create or validate reuse of a worktree; refuse below 5% available disk unless explicitly overridden' 'make gate [BASE=origin/dev] [PURPOSE=pull-request|push]  Run all applicable shared CI checks' 'make gate-plan [BASE=origin/dev] [PURPOSE=pull-request|push]  Show identities and applicable checks without execution' 'make ci-unit UNIT=id  Run one declared CI unit with its canonical preparation and evidence' 'make lean-report-scoped LEAN_TARGETS="D5.Module [Reg.Module ...]"  Build and inspect explicit targets, named utility inputs and imports; requires no full report' 'make lean-report [REBUILD_REPORT_CACHE=1 | REGENERATE_REPORT_ARTIFACTS=1]  Full report; regenerate explicitly discards generated reports while retaining compiled Lean' 'make emit [BASE=origin/dev] [PATHS=FILE] [EMIT_FULL_REPORT=FILE]  Emit from selected scoped Lean inputs or an existing validated full report bundle' 'make dag DIGEST=HEX64 [PREFIX=scribe-resources]  Fetch a published full Scribe pack and render the DAG' 'make filemap  Render FILEMAP on demand from Meta/FILEMAP.toml' 'make filemap-conform [FILEMAP_SCOPE=path | FILEMAP_PRODUCER=name]  Build and run standalone conformance' 'make scribe-release  Rebuild and verify local Scribe release assets' 'make scribe-release-publish TARGET=COMMIT [PREFIX=scribe-resources]  Publish or verify the exact Scribe resource release' 'make scribe-release-fetch DIGEST=HEX64 [PREFIX=scribe-resources]  Fetch and verify the exact Scribe resource pack' 'make worktree-checkpoint MESSAGE=FILE  Commit the ordinary whole working snapshot' 'make worktree-publish HEAD=BRANCH [COMMIT=HEAD]  Non-force publication with fresh remote ancestry confirmation' 'make worktree-finalize HEAD=BRANCH WRITERS_JOINED=1  Publish after host joins this task writers' 'make worktree-remove NAMES="DIR [DIR ...]" [FORCE=1]  Remove named worktrees; explicit FORCE=1 disables the 300-second removal timeout' 'make source-dispatch SOURCES="id id ..." [DEFAULT=excluded|eligible]  Read or update source default dispatch' 'make mathlib-reanchor BASE=REV [OLD_REPORT=PATH]  Reanchor Frozen using the candidate report and optional historical content witness' 'make search-atoms SOURCE=id [SELECTION=default-dispatch]  Search stored paths or default candidates'

test:
	@set -e; paths="$$(mktemp)"; trap 'rm -f "$$paths"' EXIT; git diff --name-only -z "$(BASE)" -- > "$$paths"; git ls-files --others --exclude-standard -z >> "$$paths"; make lean-report; dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo; dotnet tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll check-current --candidate-lean-report "$(LEAN_REPORT)" --scribe-paths-from "$$paths"

lean-cache-ensure:
	@/bin/bash tools/scripts/worktree/lean-cache-ensure.sh

# Optional integration verification is explicit and validated by the producer.
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_MODE ?= production
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_SOURCE_REF ?=
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_SOURCE_COMMIT ?=
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_REPOSITORY ?= .
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_TAG ?=
lean-cache-to-github-without-mathlib: export LEAN_CACHE_PUBLISH_ONLY ?= 0

lean-cache-to-github-without-mathlib:
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh publish --repository "$$LEAN_CACHE_REPOSITORY" --mode "$$LEAN_CACHE_MODE" --source-ref "$$LEAN_CACHE_SOURCE_REF" --source-commit "$$LEAN_CACHE_SOURCE_COMMIT" $(if $(filter 1,$(LEAN_CACHE_PUBLISH_ONLY)),--no-build)

lean-cache-from-github-without-mathlib:
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh fetch --repository "$$LEAN_CACHE_REPOSITORY" --mode "$$LEAN_CACHE_MODE" --source-ref "$$LEAN_CACHE_SOURCE_REF" --source-commit "$$LEAN_CACHE_SOURCE_COMMIT" --tag "$$LEAN_CACHE_TAG" $(if $(filter 1,$(REFRESH_STALE)),--refresh-stale)

warm-donor:
	@/bin/bash tools/scripts/worktree/warm-donor.sh

lean:
	@/bin/bash tools/scripts/worktree/lean-cache-run.sh --build $(LEAN_TARGETS)

lean-report:
	@/bin/bash tools/scripts/report/lean-report.sh --cache-miss-policy "$(LEAN_REPORT_CACHE_MISS_POLICY)" --rebuild-report-cache "$(REBUILD_REPORT_CACHE)" --regenerate-report-artifacts "$(REGENERATE_REPORT_ARTIFACTS)"

lean-report-scoped:
	@/bin/bash tools/scripts/report/lean-report-scoped.sh --targets "$(LEAN_TARGETS)"

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
	@$(MAKE) -C tools filemap-conform

scribe-release:
	@/bin/bash tools/scripts/scribe-release.sh

scribe-release-publish:
	@/bin/bash tools/scripts/scribe-release.sh publish --prefix "$$PREFIX" --target "$$TARGET"

scribe-release-fetch:
	@/bin/bash tools/scripts/scribe-release.sh fetch "$$DIGEST" --prefix "$$PREFIX"

scribe-release-publish scribe-release-fetch: export PREFIX ?= scribe-resources
scribe-release-publish: export TARGET ?=
scribe-release-fetch: export DIGEST ?=

ingest:
	@/bin/bash tools/scripts/ingest.sh ingest "$(SOURCE)"

mathlib-reanchor:
	@/bin/bash tools/scripts/ingest.sh mathlib-reanchor "$(BASE)" "$$REANCHOR_OLD_REPORT"
mathlib-reanchor: export REANCHOR_OLD_REPORT := $(value OLD_REPORT)

source-dispatch:
	@args=(); for source in $$DISPATCH_SOURCES; do args+=(--source "$$source"); done; test -z "$$DISPATCH_DEFAULT" || args+=(--default "$$DISPATCH_DEFAULT"); dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- source-dispatch "$${args[@]}"
source-dispatch: export DISPATCH_SOURCES := $(value SOURCES)
source-dispatch: export DISPATCH_DEFAULT := $(value DEFAULT)
unexport SOURCES DEFAULT

search-atoms:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- search-atoms --source "$(SOURCE)" $(if $(SELECTION),--selection "$(SELECTION)",) $(if $(TEXT),--text "$(TEXT)",) $(if $(STATE),--state "$(STATE)",) $(if $(LIMIT),--limit "$(LIMIT)",)

show-atom:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- show-atom --atom-id "$(ATOM_ID)" $(if $(SOURCE),--source "$(SOURCE)",)

atom-context:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- atom-context --atom-id "$(ATOM_ID)" $(if $(SOURCE),--source "$(SOURCE)",)

truth-export:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- truth-export --out "$(OUT)" --candidate-lean-report "$(LEAN_REPORT)"


deliver-check:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deliver-check "$(BASE)"

deposit:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deposit "$(BASE)" "$(ATOM_ID)" "$(GID)"

deposit-uncovered:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deposit-uncovered "$(BASE)" "$(GID)"

cover:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh cover "$(ATOM_ID)" "$(GID)"

cover-batch:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh cover-batch "$(ATOMS)"

decompose:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- decompose-atom --atom "$(ATOM_ID)" $(foreach offset,$(SPLIT_AT),--split-at "$(offset)") $(if $(filter 1,$(DRY_RUN)),--dry-run,)

settle:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- settle-atom --request "$(REQUEST)"

settle-clear:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- settle-atom --clear "$(ATOM_ID)"

worktree:
	@/bin/bash tools/scripts/worktree-init.sh "$(KIND)" "$(NAME)" "$(WORKTREE_DEST)" "$(BASE)" "$${WORKTREE_ALLOW_LOW_DISK}"
worktree: export WORKTREE_ALLOW_LOW_DISK := $(if $(filter command line,$(origin ALLOW_LOW_DISK)),$(value ALLOW_LOW_DISK),0)

worktree-checkpoint:
	@python3 -B tools/scripts/worktree/worktree_protocol.py checkpoint --path . --message-file "$$CHECKPOINT_MESSAGE"
worktree-checkpoint: export CHECKPOINT_MESSAGE := $(value MESSAGE)

worktree-publish:
	@python3 -B tools/scripts/worktree/worktree_protocol.py publish --path . --branch "$$PUBLICATION_BRANCH" --commit "$$PUBLICATION_COMMIT"
worktree-publish: export PUBLICATION_BRANCH := $(value HEAD)
worktree-publish: export PUBLICATION_COMMIT := $(if $(COMMIT),$(value COMMIT),HEAD)

worktree-finalize:
	@test "$$FINALIZATION_JOINED" = 1 || { echo 'Host must join this task writers before finalization' >&2; exit 64; }; python3 -B tools/scripts/worktree/worktree_protocol.py finalize --path . --branch "$$PUBLICATION_BRANCH" --writers-joined
worktree-finalize: export PUBLICATION_BRANCH := $(value HEAD)
worktree-finalize: export FINALIZATION_JOINED := $(value WRITERS_JOINED)

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

# Requests are Lean commands; the shell only transports compiler invocations.
search-reduction:
	@$(MAKE) lean LEAN_TARGETS="LeanInformationAuditRegAnalysis.SearchReduction.Commands $(SEARCH_MODULES)" && $(MAKE) search-reduction-run

# Replay only after the runner and request imports have been built.
search-reduction-run:
	@test -f "$$SEARCH_REDUCTION_REQUESTS" || { echo 'REQUESTS must name a Lean declaration list' >&2; exit 2; }; lake -d tools/lean-inspector-reg env lean -j1 "$$SEARCH_REDUCTION_REQUESTS"
search-reduction search-reduction-run: export SEARCH_REDUCTION_REQUESTS := $(value REQUESTS)

search-reduction-test:
	@for module in GraphModel GraphCalibration Calibration FaultPaths SingleSourceModel VocabularyModel PresentationCoverage SingleSourceTests RawOriginsTests Faults RealNegative VocabularyTransport VocabularyTests InformationTests; do $(MAKE) lean LEAN_TARGETS="LeanInformationAuditRegTests.SearchReduction.$$module" || exit $$?; done

# Reexecute every probe and guard even when the compiled fixtures are current.
search-reduction-replay-test:
	@$(MAKE) lean LEAN_TARGETS="LeanInformationAuditRegAnalysis.SearchReduction.Commands LeanInformationAuditRegTests.SearchReduction.Candidates LeanInformationAuditRegTests.SearchReduction.VocabularyCandidates LeanInformationAuditRegTests.SearchReduction.GraphCandidates D5.S0.Tower.NonPisotVerdict.SubstitutionTowerClause D5.S3.ConceptDynamics.Epistemic.RobustKnowledgeFactivity" && $(MAKE) search-reduction-run REQUESTS=tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/GraphCalibration.lean && $(MAKE) -j1 search-reduction-replay-calibration search-reduction-replay-faults search-reduction-replay-real-negative search-reduction-replay-vocabulary

search-reduction-replay-calibration:
	@$(MAKE) search-reduction-run REQUESTS=tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/Calibration.lean
search-reduction-replay-faults:
	@$(MAKE) search-reduction-run REQUESTS=tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/Faults.lean
search-reduction-replay-real-negative:
	@$(MAKE) search-reduction-run REQUESTS=tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/RealNegative.lean

search-reduction-replay-vocabulary:
	@$(MAKE) search-reduction-run REQUESTS=tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/VocabularyTransport.lean && $(MAKE) search-reduction-run REQUESTS=tools/lean-inspector/LeanInformationAuditRegTests/SearchReduction/VocabularyTests.lean

