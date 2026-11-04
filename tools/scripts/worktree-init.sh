#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
KIND="${1-}"
NAME="${2-}"
TARGET="${3-}"
BASE="${4-origin/dev}"
ALLOW_LOW_DISK="${5-0}"

[[ -n "$KIND" ]] || { echo "WORKTREE_INIT_MISSING_KIND" >&2; exit 64; }
[[ -n "$NAME" ]] || { echo "WORKTREE_INIT_MISSING_NAME" >&2; exit 65; }
[[ -n "$TARGET" ]] || { echo "WORKTREE_INIT_MISSING_TARGET" >&2; exit 66; }
[[ -n "$BASE" ]] || { echo "WORKTREE_INIT_MISSING_BASE" >&2; exit 67; }
[[ "$ALLOW_LOW_DISK" == 0 || "$ALLOW_LOW_DISK" == 1 ]] || { echo "WORKTREE_INIT_INVALID_ALLOW_LOW_DISK" >&2; exit 64; }
[[ $# -le 5 ]] || { echo "WORKTREE_INIT_UNEXPECTED_ARGUMENT" >&2; exit 64; }

cd "$ROOT"
disk_arguments=(check-disk --path "$ROOT" --path "$TARGET")
if [[ "$ALLOW_LOW_DISK" == 1 ]]; then disk_arguments+=(--allow-low-disk); fi
unset WORKTREE_REQUIRE_DISK_CHECK
if [[ "$ALLOW_LOW_DISK" == 0 && ( "${WORKTREE_PREFER_IDLE:-0}" == 1 || -d "$TARGET" ) ]]; then
  # Reusing an existing directory needs no new checkout allocation.
  # The creator checks disk space after the reuse and recovery paths.
  export WORKTREE_REQUIRE_DISK_CHECK=1
else
  python3 -B "$ROOT/tools/scripts/host-cleanup.py" "${disk_arguments[@]}"
fi

creation_arguments=()
if [[ "${WORKTREE_PREFER_IDLE:-0}" == 1 ]]; then creation_arguments+=(--prefer-idle); fi

exec dotnet run \
  --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release \
  -- \
  worktree \
  --kind "$KIND" \
  --name "$NAME" \
  --path "$TARGET" \
  --base "$BASE" \
  ${creation_arguments[@]+"${creation_arguments[@]}"}
