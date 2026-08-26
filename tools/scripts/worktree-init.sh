#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
KIND="${1:-}"
NAME="${2:-}"
TARGET="${3:-}"
BASE="${4:-origin/dev}"

BRANCH="harness/$KIND/$NAME"

cd "$ROOT"
exec dotnet run \
  --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release \
  -- \
  worktree \
  --branch "$BRANCH" \
  --path "$TARGET" \
  --base "$BASE"
