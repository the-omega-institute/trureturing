#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"

cd "$ROOT"
exec dotnet run \
  --project "$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release \
  -- \
  worktree ensure-cache
