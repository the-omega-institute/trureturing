SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
WORKTREE_DEST = $(if $(DEST),$(abspath $(DEST)),$(abspath ../trureturing-$(NAME)))
.PHONY: help test lean-cache-ensure lean lean-report build emit ingest echo-residual-summary show-atom deliver-check receipts-stage deposit cover worktree pr-open preflight gate

help:
	@printf '%s\n' 'make help                         Show this target list' 'make test                         Run the mathematical gate (Lean, admission, Scribe, values)' 'make lean-cache-ensure            Ensure a private Lean build cache is available' 'make lean                         Build the pinned Lean project' 'make lean-report                  Produce the canonical raw Lean report' 'make build                        Build the pinned Lean content' 'make emit                         Emit canonical Scribe documents, catalog, and values' 'make ingest [BASE=origin/dev]     Consume the raw Lean report and align theory receipts' 'make echo-residual-summary [BASE=origin/dev]  Emit the content-addressed residual projection bytes' 'make show-atom ATOM_ID=x          Print and verify one digestion atom without writing' 'make deliver-check [BASE=origin/dev]  Run theorem delivery in canonical freeze-last order' 'make receipts-stage [BASE=origin/dev]  Re-derive staged receipts and reject unsafe absorption' 'make deposit ATOM_ID=x GID=g [BASE=origin/dev]  Deposit theorem, freeze, and receipt in two commits' 'make cover ATOM_ID=x GID=g [BASE=origin/dev]  Cover an atom and align its post-cover receipt' 'make worktree NAME=x [BASE=origin/dev] [DEST=DIR]  Initialize an isolated worktree; .lake is copied, never symlinked' 'make pr-open HEAD=branch TITLE=t [BODY=file]  Open a PR to dev and arm auto-merge' 'make preflight [BASE=origin/dev]  Pre-verify all three required CI checks (engineering / lean-inspect / admission) locally before pushing' 'make gate [BASE=origin/dev]       Run the local CI-equivalent admission flow'

test: lean-cache-ensure
	@/bin/bash tools/scripts/workflow/math-gate.sh

lean-cache-ensure:
	@/bin/bash tools/scripts/worktree/lean-cache-ensure.sh

lean: lean-cache-ensure
	@lake build

lean-report: lean-cache-ensure
	@/bin/bash tools/scripts/report/lean-report.sh

build: lean-cache-ensure lean

emit:
	@/bin/bash tools/scripts/scribe.sh emit

ingest:
	@/bin/bash tools/scripts/ingest.sh "$(BASE)"

echo-residual-summary:
	@/bin/bash tools/scripts/report/echo-residual-summary.sh "$(BASE)"

show-atom:
	@dotnet run --no-build --project tools/StrataLint.Cli/StrataLint.Cli.csproj --configuration Release -- show-atom --atom-id "$(ATOM_ID)"

deliver-check:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deliver-check "$(BASE)"

receipts-stage:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh receipts-stage "$(BASE)"

deposit:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh deposit "$(BASE)" "$(ATOM_ID)" "$(GID)"

cover:
	@/bin/bash tools/scripts/workflow/playbook-workflows.sh cover "$(BASE)" "$(ATOM_ID)" "$(GID)"

worktree:
	@/bin/bash tools/scripts/worktree-init.sh "$(NAME)" "$(WORKTREE_DEST)" "$(BASE)"

pr-open:
	@/bin/bash tools/scripts/pr.sh open --head "$(HEAD)" --title "$(TITLE)" $(if $(BODY),--body-file "$(BODY)",)

preflight:
	@BASE="$(BASE)" /bin/bash tools/scripts/preflight.sh

gate:
	@/bin/bash tools/scripts/local-harness-gate.sh --base "$(BASE)" $(GATE_ARGS)
