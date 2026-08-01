#!/usr/bin/env bash
set -u

if [[ -L .lake ]]; then
  printf '%s\n' 'LEAN_CACHE status=refused reason=.lake_is_a_symlink; shared_Lean_caches_are_forbidden' >&2
  exit 1
fi

if [[ -d .lake ]]; then
  printf '%s\n' 'LEAN_CACHE status=present method=none'
  exit 0
fi

exec dotnet run \
  --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj \
  --configuration Release \
  -- \
  worktree ensure-cache
