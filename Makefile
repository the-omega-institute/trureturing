SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
AUTO_MERGE ?= 1
DRAFT ?= 0
ALLOW_LOW_DISK ?= 0
WORKTREE_DEST = $(if $(DEST),$(DEST),../trureturing-$(NAME))
LEAN_REPORT ?= .lake/build/stratalint/raw-lean-report.json
export LEAN_SKIP_LOCK ?= 0
CENSUS_OUT ?= build/census/$(shell date -u +%Y%m%dT%H%M%S)
CENSUS_PREFIX ?= D5
.PHONY: help test lean-cache-ensure lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib warm-donor lean lean-report build emit dag filemap scribe-release scribe-release-publish scribe-release-fetch ingest mathlib-reanchor echo-residual-summary digestion-readiness show-atom atom-context truth-export deliver-check deposit deposit-uncovered cover cover-batch decompose settle settle-clear worktree worktree-clean worktree-remove pr pr-open pr-watch gate census census-derivational

help:
	@printf '%s\n' 'make pr HEAD=branch MESSAGE=file [AUTO_MERGE=0] [DRAFT=1]  Open a PR; auto-merge defaults on; drafts return without merging or watching CI' 'make pr-open HEAD=branch MESSAGE=file  Same options as make pr' 'make pr-watch PR=number HEAD_SHA=sha  Wait for required CI on the exact commit' 'make lean [LEAN_TARGETS="..."] [LEAN_SKIP_LOCK=1]  Build Lean; set LEAN_SKIP_LOCK=1 to skip the shared build lock' 'make test  Run lean-report and check-current' 'make worktree KIND=x NAME=y [BASE=origin/dev] [DEST=DIR] [ALLOW_LOW_DISK=1]  Initialize a worktree; refuse below 5% available disk unless explicitly overridden' 'make gate [BASE=origin/dev]  Run independent CI-equivalent commands' 'make lean-report  Produce the canonical raw Lean report' 'make emit [BASE=origin/dev] [PATHS=FILE]  Emit changed Scribe projections and values' 'make dag DIGEST=HEX64 [PREFIX=scribe-resources]  Fetch a published full Scribe pack and render the DAG' 'make filemap  Render FILEMAP on demand from Meta/FILEMAP.toml' 'make scribe-release  Rebuild and verify local Scribe release assets' 'make scribe-release-publish TARGET=COMMIT [PREFIX=scribe-resources]  Publish or verify the exact Scribe resource release' 'make scribe-release-fetch DIGEST=HEX64 [PREFIX=scribe-resources]  Fetch and verify the exact Scribe resource pack' 'make worktree-remove NAMES="DIR [DIR ...]" [FORCE=1]  Remove named worktrees; explicit FORCE=1 disables the 300-second removal timeout'

test:
	@set -e; paths="$$(mktemp)"; trap 'rm -f "$$paths"' EXIT; git diff --name-only -z "$(BASE)" -- > "$$paths"; git ls-files --others --exclude-standard -z >> "$$paths"; make lean-report; dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo; dotnet tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll check-current --candidate-lean-report "$(LEAN_REPORT)" --scribe-paths-from "$$paths"

lean-cache-ensure:
	@/bin/bash tools/scripts/worktree/lean-cache-ensure.sh

# Optional integration verification is explicit and validated by the producer.
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_MODE ?= production
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_SOURCE_REF ?=
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_SOURCE_COMMIT ?=

lean-cache-to-github-without-mathlib:
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh publish --mode "$$LEAN_CACHE_MODE" --source-ref "$$LEAN_CACHE_SOURCE_REF" --source-commit "$$LEAN_CACHE_SOURCE_COMMIT"

lean-cache-from-github-without-mathlib:
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh fetch --mode "$$LEAN_CACHE_MODE" --source-ref "$$LEAN_CACHE_SOURCE_REF" --source-commit "$$LEAN_CACHE_SOURCE_COMMIT"

warm-donor:
	@/bin/bash tools/scripts/worktree/warm-donor.sh

lean:
	@/bin/bash tools/scripts/worktree/lean-cache-run.sh --build $(LEAN_TARGETS)

lean-report:
	@/bin/bash tools/scripts/report/lean-report.sh

build: lean

emit:
	@/bin/bash tools/scripts/scribe.sh emit

emit: export BASE ?= origin/dev
emit: export PATHS ?=

PREFIX ?= scribe-resources
DIGEST ?=
SCRIBE_PACK = Generated/$(PREFIX)/$(DIGEST)/scribe-resources.zip

dag:
	@test -n "$(DIGEST)" || { echo 'make dag: DIGEST is required' >&2; exit 2; }; make scribe-release-fetch DIGEST="$(DIGEST)" PREFIX="$(PREFIX)" && dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- dag-render --scribe-pack "$(SCRIBE_PACK)" --scribe-pack-digest "$(DIGEST)"

filemap:
	@dotnet run --project tools/StrataLint.Scribe/StrataLint.Scribe.csproj --configuration Release -- filemap

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
	@/bin/bash tools/scripts/ingest.sh mathlib-reanchor "$(BASE)"

echo-residual-summary:
	@/bin/bash tools/scripts/report/echo-residual-summary.sh

digestion-readiness:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- digest-status --readiness

show-atom:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- show-atom --atom-id "$(ATOM_ID)"

atom-context:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- atom-context --atom-id "$(ATOM_ID)"

truth-export:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- truth-export --out "$(OUT)" --candidate-lean-report "$(LEAN_REPORT)"


census:
	@python3 tools/lean-inspector/Census/pipeline.py --output "$(CENSUS_OUT)" --lean-report "$(LEAN_REPORT)" --prefix "$(CENSUS_PREFIX)"

census-derivational:
	@python3 tools/lean-inspector/Census/Structure/derivational.py --directory "$(CENSUS_OUT)"

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
	@set -e; \
	make lean-report; \
	dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo; \
	cli=tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll; paths="$$(mktemp)"; trap 'rm -f "$$paths"' EXIT; git diff --name-only -z "$(BASE)" -- > "$$paths"; git ls-files --others --exclude-standard -z >> "$$paths"; \
	dotnet "$$cli" check-current --candidate-lean-report "$(LEAN_REPORT)" --scribe-paths-from "$$paths"; \
	bash tools/scripts/workflow/scribe-content-checks.sh "$(LEAN_REPORT)" tools/StrataLint.Scribe/bin/Release/net10.0/StrataLint.Scribe.dll "$$paths"; \
	dotnet "$$cli" filemap-conform; \
	dotnet "$$cli" check-delta --protected-base "$$(git rev-parse --verify '$(BASE)^{commit}')" --candidate-lean-report "$(LEAN_REPORT)"
