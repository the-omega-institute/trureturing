SHELL := /bin/bash
.DEFAULT_GOAL := help

BASE ?= origin/dev
WORKTREE_PATH = $(if $(filter command line,$(origin PATH)),$(PATH),$(abspath ../trureturing-$(NAME)))

.PHONY: help dotnet test lean build emit emit-check selftest gate worktree

help:
	@printf '%s\n' 'make help                         Show this target list' 'make dotnet                       Restore and build .NET with warnings as errors' 'make test                         Run the .NET test suite' 'make lean                         Build the pinned Lean project' 'make build                        Run make dotnet and make lean' 'make emit                         Emit canonical Scribe documents, catalog, and values' 'make emit-check                   Check canonical Scribe documents, catalog, and values' 'make selftest                     Run deterministic StrataLint selftest' 'make gate [BASE=origin/dev]       Run the local CI-equivalent admission flow' 'make worktree NAME=x [BASE=origin/dev] [PATH=DIR]  Initialize an isolated worktree; .lake is copied, never symlinked'

dotnet:
	@/bin/bash Meta/StrataLint/scripts/dotnet-build.sh

test:
	@dotnet test Meta/StrataLint/StrataLint.sln --configuration Release --verbosity normal

lean:
	@lake build

build: dotnet lean

emit:
	@/bin/bash Meta/StrataLint/scripts/scribe.sh emit

emit-check:
	@/bin/bash Meta/StrataLint/scripts/scribe.sh check

selftest:
	@/bin/bash Meta/StrataLint/scripts/stratalint-selftest.sh

gate:
	@/bin/bash Meta/StrataLint/scripts/local-harness-gate.sh --base "$(BASE)"

worktree:
	@/bin/bash Meta/StrataLint/scripts/worktree-init.sh "$(NAME)" "$(WORKTREE_PATH)" "$(BASE)"
