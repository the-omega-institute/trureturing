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
python3 -B "$ROOT/tools/scripts/host-cleanup.py" "${disk_arguments[@]}"

exec dotnet run \
  --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release \
  -- \
  worktree \
  --kind "$KIND" \
  --name "$NAME" \
  --path "$TARGET" \
  --base "$BASE"
