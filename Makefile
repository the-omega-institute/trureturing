SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
WORKTREE_DEST = $(if $(DEST),$(abspath $(DEST)),$(abspath ../trureturing-$(NAME)))
LEAN_REPORT ?= .lake/build/stratalint/raw-lean-report.json
.PHONY: help test lean-cache-ensure lean-cache-to-github-without-mathlib lean-cache-from-github-without-mathlib warm-donor lean lean-report build emit ingest echo-residual-summary show-atom theory-candidates truth-export deliver-check receipts-stage deposit cover cover-batch worktree worktree-clean pr-open pr-watch preflight gate

help:
	@printf '%s\n' 'make help                         Show this target list' 'make test                         Run the mathematical gate (Lean, admission, Scribe, values)' 'make lean-cache-ensure            Ensure a private Lean build cache is available' 'make lean-cache-to-github-without-mathlib  Publish this tree'\''s own Lean build output to a GitHub release; dependency packages are excluded' 'make lean-cache-from-github-without-mathlib  Fetch this tree'\''s own Lean build output from a GitHub release, or fail closed; mathlib still comes from lake exe cache get' 'make warm-donor                  Update and build a clean dev checkout for optional machine-local scheduling' 'make lean                         Build the pinned Lean project' 'make lean-report                  Produce the canonical raw Lean report' 'make build                        Build the pinned Lean content' 'make emit                         Emit canonical Scribe documents, catalog, and values' 'make ingest [BASE=origin/dev]     Consume the raw Lean report and align theory receipts' 'make echo-residual-summary [BASE=origin/dev]  Emit the content-addressed residual projection bytes' 'make show-atom ATOM_ID=x          Print and verify one digestion atom without writing' 'make theory-candidates [OWNER_OVERRIDE_FILE=path]  Print the read-only theory candidate projection' 'make truth-export OUT=dir [LEAN_REPORT=path]  Export immutable STRICT active frozen truth to dir/truth-export.v1.json' 'make deliver-check [BASE=origin/dev]  Run theorem delivery in canonical freeze-last order' 'make receipts-stage [BASE=origin/dev]  Re-derive staged receipts and reject unsafe absorption' 'make deposit ATOM_ID=x GID=g [BASE=origin/dev]  Deposit theorem, freeze, and receipt in two commits' 'make cover ATOM_ID=x GID=g [BASE=origin/dev]  Cover an atom and align its post-cover receipt' 'make cover-batch ATOMS=file [BASE=origin/dev]  Cover strict TSV atom/GID pairs with one Lean report' 'make worktree KIND=x NAME=y [BASE=origin/dev] [DEST=DIR]  Initialize an isolated worktree; Lean cache is lazy and never symlinked' 'make worktree-clean [BASE=origin/dev]  Reclaim registered lanes that are merged into BASE and have no uncommitted work' 'make pr-open HEAD=branch MESSAGE=file  Create from a message file whose first line is the title, arm auto-merge, and wait for required-CI verdict' 'make pr-watch PR=n                Wait for required-CI verdict on an existing PR' 'make preflight [BASE=origin/dev]  Pre-verify all three required CI checks (engineering / lean-inspect / admission) locally before pushing' 'make gate [BASE=origin/dev]       Run the local CI-equivalent admission flow'

test:
	@/bin/bash tools/scripts/workflow/math-gate.sh

lean-cache-ensure:
	@/bin/bash tools/scripts/worktree/lean-cache-ensure.sh

lean-cache-to-github-without-mathlib:
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh publish

lean-cache-from-github-without-mathlib:
	@/bin/bash tools/scripts/worktree/lean-cache-publish.sh fetch

warm-donor:
	@/bin/bash tools/scripts/worktree/warm-donor.sh

lean:
	@/bin/bash tools/scripts/worktree/lean-cache-run.sh lake build

lean-report:
	@/bin/bash tools/scripts/report/lean-report.sh

build: lean

emit:
	@/bin/bash tools/scripts/scribe.sh emit

ingest:
	@/bin/bash tools/scripts/ingest.sh ingest "$(BASE)"

echo-residual-summary:
	@/bin/bash tools/scripts/report/echo-residual-summary.sh "$(BASE)"

show-atom:
	@dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- show-atom --atom-id "$(ATOM_ID)"

theory-candidates:
	@dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- theory-candidates $(if $(strip $(OWNER_OVERRIDE_FILE)),--owner-override-file "$(OWNER_OVERRIDE_FILE)",)

truth-export:
	@dotnet run --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- truth-export --out "$(OUT)" --candidate-lean-report "$(LEAN_REPORT)"

deliver-check:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deliver-check "$(BASE)"

receipts-stage:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh receipts-stage "$(BASE)"

deposit:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deposit "$(BASE)" "$(ATOM_ID)" "$(GID)"

cover:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh cover "$(BASE)" "$(ATOM_ID)" "$(GID)"

cover-batch:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh cover-batch "$(BASE)" "$(ATOMS)"

worktree:
	@/bin/bash tools/scripts/worktree-init.sh "$(KIND)" "$(NAME)" "$(WORKTREE_DEST)" "$(BASE)"

worktree-clean:
	@/bin/bash tools/scripts/clean-lanes.sh --base "$(BASE)" --lanes-only --force

pr-open:
	@/bin/bash tools/scripts/pr.sh open --head "$(HEAD)" --message-file "$(MESSAGE)" $(if $(WATCH_TIMEOUT_SECONDS),--timeout-seconds "$(WATCH_TIMEOUT_SECONDS)",) $(if $(WATCH_INTERVAL_SECONDS),--interval-seconds "$(WATCH_INTERVAL_SECONDS)",)

pr-watch:
	@/bin/bash tools/scripts/pr.sh watch --pr "$(PR)" $(if $(WATCH_TIMEOUT_SECONDS),--timeout-seconds "$(WATCH_TIMEOUT_SECONDS)",) $(if $(WATCH_INTERVAL_SECONDS),--interval-seconds "$(WATCH_INTERVAL_SECONDS)",)

preflight:
	@BASE="$(BASE)" /bin/bash tools/scripts/preflight.sh

gate:
	@/bin/bash tools/scripts/local-harness-gate.sh --base "$(BASE)" $(GATE_ARGS)
