#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"

if [[ -L "$ROOT/.lake" ]]; then
  printf '%s\n' 'LEAN_CACHE status=refused reason=.lake_is_a_symlink; shared_Lean_caches_are_forbidden' >&2
  exit 1
fi

if [[ -d "$ROOT/.lake" ]]; then
  printf '%s\n' 'LEAN_CACHE status=present method=none'
  exit 0
fi

cd "$ROOT"
exec dotnet run \
  --project "$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release \
  -- \
  worktree ensure-cache
