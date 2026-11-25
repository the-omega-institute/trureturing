#!/usr/bin/env bash
set -euo pipefail

driver="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
mode="${LEAN_CACHE_MODE:-production}"
args=(publish --repository . --mode "$mode" --prepare-only)
if [[ "$mode" == verification ]]; then
  args+=(--source-ref "${GITHUB_REF:?}" --source-commit "${GITHUB_SHA:?}")
fi
if [[ "${LEAN_CACHE_INDEXED:-0}" == 1 ]]; then args+=(--indexed); fi
export FULL_BUILD=1 PYTHONUNBUFFERED=1 STRATALINT_ACCEPT_COLD_BUILD=1
exec bash "$driver/.github/actions/lean-compile-layer/measure.sh" --compile \
  bash "$driver/tools/scripts/worktree/lean-cache-publish.sh" "${args[@]}"
