#!/usr/bin/env bash
set -euo pipefail

args=(publish --repository . --mode production --prepare-only)
if [[ "${LEAN_CACHE_INDEXED:-0}" == 1 ]]; then args+=(--indexed); fi
export FULL_BUILD=1 PYTHONUNBUFFERED=1
exec bash .github/actions/lean-compile-layer/measure.sh --report \
  bash tools/scripts/worktree/lean-cache-publish.sh "${args[@]}"
