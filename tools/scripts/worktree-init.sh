#!/usr/bin/env bash
set -euo pipefail

# make's requested PATH variable names the new worktree. Restore a tool PATH
# before invoking the CLI. The CLI copies .lake; symlink sharing is forbidden.
export PATH="$HOME/.dotnet:$HOME/.elan/bin:/usr/local/share/dotnet:/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin"

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
