#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"

cd "$ROOT"
# Reusable MSBuild nodes inherit the caller's output pipes and can outlive ensure-cache.
export MSBUILDDISABLENODEREUSE=1
exec dotnet run \
  --project "$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release \
  -- \
  worktree ensure-cache
