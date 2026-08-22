#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
NAME="${1:-}"
TARGET="${2:-}"
BASE="${3:-origin/dev}"
# 默认顺手回收已合入且干净的旧 lane(CLAUDE.md 第 16 条)。CLEAN=0 保留它们。
CLEAN="${4:-1}"

arguments=(
  worktree
  --branch "harness/$NAME"
  --path "$TARGET"
  --base "$BASE"
)
if [[ "$CLEAN" == "0" ]]; then arguments+=(--no-clean-lanes); fi

cd "$ROOT"
exec dotnet run \
  --project tools/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release \
  -- \
  "${arguments[@]}"
