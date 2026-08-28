#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
KIND="${1-}"
NAME="${2-}"
TARGET="${3-}"
BASE="${4-origin/dev}"

[[ -n "$KIND" ]] || { echo "WORKTREE_INIT_MISSING_KIND" >&2; exit 64; }
[[ -n "$NAME" ]] || { echo "WORKTREE_INIT_MISSING_NAME" >&2; exit 65; }
[[ -n "$TARGET" ]] || { echo "WORKTREE_INIT_MISSING_TARGET" >&2; exit 66; }
[[ -n "$BASE" ]] || { echo "WORKTREE_INIT_MISSING_BASE" >&2; exit 67; }

cd "$ROOT"
exec dotnet run \
  --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release \
  -- \
  worktree \
  --kind "$KIND" \
  --name "$NAME" \
  --path "$TARGET" \
  --base "$BASE"
