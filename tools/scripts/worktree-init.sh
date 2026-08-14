#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
NAME="${1:-}"
TARGET="${2:-}"
BASE="${3:-origin/dev}"

cd "$ROOT"
exec dotnet run \
  --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release \
  -- \
  worktree \
  --branch "harness/$NAME" \
  --path "$TARGET" \
  --base "$BASE"
