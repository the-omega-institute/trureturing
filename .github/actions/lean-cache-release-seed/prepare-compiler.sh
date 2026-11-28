#!/usr/bin/env bash
set -euo pipefail

driver="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
args=(publish --repository . --mode verification --prepare-only --indexed
  --source-ref "${GITHUB_REF:?}" --source-commit "${GITHUB_SHA:?}")
export FULL_BUILD=1 PYTHONUNBUFFERED=1 STRATALINT_ACCEPT_COLD_BUILD=1
exec bash "$driver/.github/actions/lean-compile-layer/measure.sh" --compile \
  bash "$driver/tools/scripts/worktree/lean-cache-publish.sh" "${args[@]}"
