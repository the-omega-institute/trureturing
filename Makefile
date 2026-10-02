SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
WORKTREE_DEST = $(if $(DEST),$(DEST),../trureturing-$(NAME))
LEAN_REPORT ?= .lake/build/stratalint/raw-lean-report.json
CENSUS_OUT ?= build/census/$(shell date -u +%Y%m%dT%H%M%S)
CENSUS_PREFIX ?= D5
.PHONY: help test lean-cache-ensure lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib warm-donor lean lean-report build emit ingest align-digestion-status refresh-source-registry mathlib-reanchor echo-residual-summary digestion-readiness show-atom atom-context truth-export deliver-check deposit deposit-uncovered cover cover-batch decompose quarantine quarantine-clear settle settle-clear worktree worktree-clean worktree-remove pr-open pr-watch gate census census-derivational

help:
	@printf '%s\n' 'make test  Run lean-report and check-current' 'make worktree KIND=x NAME=y [BASE=origin/dev] [DEST=DIR]  Initialize an isolated worktree; Lean cache is lazy and never symlinked' 'make gate [BASE=origin/dev]  Run independent CI-equivalent commands' 'make lean-report  Produce the canonical raw Lean report' 'Report policy and REBUILD_REPORT_CACHE=1 accept only make command-line assignments, including recursive make; inherited environment values are ignored'

test:
	@set -e; make lean-report; dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo; dotnet tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll check-current --candidate-lean-report "$(LEAN_REPORT)"

lean-cache-ensure:
	@/bin/bash tools/scripts/worktree/lean-cache-ensure.sh

# Optional integration verification is explicit and validated by the producer.
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_MODE ?= production
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_SOURCE_REF ?=
lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib: export LEAN_CACHE_SOURCE_COMMIT ?=

lean-cache-to-github-without-mathlib:
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh publish --mode "$$LEAN_CACHE_MODE" --source-ref "$$LEAN_CACHE_SOURCE_REF" --source-commit "$$LEAN_CACHE_SOURCE_COMMIT"

lean-cache-from-github-without-mathlib:
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh fetch --mode "$$LEAN_CACHE_MODE" --source-ref "$$LEAN_CACHE_SOURCE_REF" --source-commit "$$LEAN_CACHE_SOURCE_COMMIT" $(if $(filter 1,$(REFRESH_STALE)),--refresh-stale,)

warm-donor:
	@/bin/bash tools/scripts/worktree/warm-donor.sh

lean:
	@/bin/bash tools/scripts/worktree/lean-cache-run.sh --build $(LEAN_TARGETS)

# GNU make preserves command-line origin through recursive MAKEFLAGS.
lean-report:
	@/bin/bash tools/scripts/report/lean-report.sh --cache-miss-policy "$(if $(filter command line,$(origin LEAN_REPORT_CACHE_MISS_POLICY)),$(LEAN_REPORT_CACHE_MISS_POLICY),fetch-or-fail)" --rebuild-report-cache "$(if $(filter command line,$(origin REBUILD_REPORT_CACHE)),$(REBUILD_REPORT_CACHE),0)"

build: lean

emit:
	@/bin/bash tools/scripts/scribe.sh emit

ingest:
	@/bin/bash tools/scripts/ingest.sh ingest "$(BASE)" "$(SOURCE)"

align-digestion-status:
	@/bin/bash tools/scripts/ingest.sh align-digestion-status "$(BASE)" "$(PLAN)"

refresh-source-registry:
	@/bin/bash tools/scripts/ingest.sh refresh-source-registry "$(BASE)" "$(SOURCE)" "$(PLAN_HASH)"

mathlib-reanchor:
	@/bin/bash tools/scripts/ingest.sh mathlib-reanchor "$(BASE)"

echo-residual-summary:
	@/bin/bash tools/scripts/report/echo-residual-summary.sh "$(BASE)"

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
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh cover "$(BASE)" "$(ATOM_ID)" "$(GID)"

cover-batch:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh cover-batch "$(BASE)" "$(ATOMS)"

decompose:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- decompose-atom --atom "$(ATOM_ID)" --base "$(BASE)" $(foreach offset,$(SPLIT_AT),--split-at "$(offset)") $(if $(filter 1,$(DRY_RUN)),--dry-run,)

quarantine:
	@/bin/bash tools/scripts/ingest.sh quarantine "$(BASE)" "$(REQUEST)"

quarantine-clear:
	@/bin/bash tools/scripts/ingest.sh quarantine-clear "$(BASE)" "$(ATOM_ID)"

settle:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- settle-atom --request "$(REQUEST)" --base "$(BASE)"

settle-clear:
	@test -x tools/StrataLint.Cli/bin/Release/net10.0/StrataLint || dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release >/dev/null; dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- settle-atom --clear "$(ATOM_ID)" --base "$(BASE)"

worktree:
	@/bin/bash tools/scripts/worktree-init.sh "$(KIND)" "$(NAME)" "$(WORKTREE_DEST)" "$(BASE)"

worktree-clean:
	@/bin/bash tools/scripts/clean-lanes.sh --base "$(BASE)" --lanes-only --force

worktree-remove:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- worktree remove --names "$${WORKTREE_REMOVE_NAMES}"
# Make also exports command-line variables; never expand the original NAMES on that path.
unexport NAMES
worktree-remove: override WORKTREE_REMOVE_NAMES := $(value NAMES)
export WORKTREE_REMOVE_NAMES

pr-open:
	@/bin/bash tools/scripts/pr.sh open --head "$(HEAD)" --message-file "$(MESSAGE)" $(if $(filter 1,$(AUTO_MERGE)),--auto-merge,) $(if $(WATCH_TIMEOUT_SECONDS),--timeout-seconds "$(WATCH_TIMEOUT_SECONDS)",) $(if $(WATCH_INTERVAL_SECONDS),--interval-seconds "$(WATCH_INTERVAL_SECONDS)",)

pr-watch:
	@/bin/bash tools/scripts/pr.sh watch --pr "$(PR)" --head-sha "$(HEAD_SHA)" $(if $(WATCH_TIMEOUT_SECONDS),--timeout-seconds "$(WATCH_TIMEOUT_SECONDS)",) $(if $(WATCH_INTERVAL_SECONDS),--interval-seconds "$(WATCH_INTERVAL_SECONDS)",)

gate:
	@set -e; \
	make lean-report; \
	dotnet build tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -nologo; \
	cli=tools/StrataLint.Cli/bin/Release/net10.0/StrataLint.dll; \
	dotnet "$$cli" check-current --candidate-lean-report "$(LEAN_REPORT)"; \
	bash tools/scripts/workflow/scribe-content-checks.sh "$(LEAN_REPORT)"; \
	dotnet "$$cli" filemap-conform; \
	dotnet "$$cli" check-delta --protected-base "$$(git rev-parse --verify '$(BASE)^{commit}')" --candidate-lean-report "$(LEAN_REPORT)"
