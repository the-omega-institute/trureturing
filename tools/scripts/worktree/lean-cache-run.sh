#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"

command=with-cache-reader
if [[ "${1:-}" == "--git" ]]; then
  command=cache-git
  shift
fi

cd "$ROOT"
exec dotnet run \
  --project "$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj" \
  --configuration Release \
  -- \
  worktree "$command" -- "$@"
