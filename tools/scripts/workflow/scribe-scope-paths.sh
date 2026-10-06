#!/usr/bin/env bash
set -euo pipefail
if [[ $# -ne 1 ]]; then
  echo "usage: scribe-scope-paths.sh CHANGED_PATHS_FILE" >&2
  exit 2
fi
CHANGED_PATHS_FILE="$1"
if [[ -f "$CHANGED_PATHS_FILE" ]]; then
  cat -- "$CHANGED_PATHS_FILE"
else
  REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
  if ! git -C "$REPO_ROOT" rev-parse --verify --quiet 'HEAD^1^{commit}' >/dev/null; then
    echo "SCRIBE_SCOPE_FIRST_PARENT_MISSING: candidate HEAD has no first parent" >&2
    exit 2
  fi
  git -C "$REPO_ROOT" diff --name-only -z HEAD^1 HEAD
fi
