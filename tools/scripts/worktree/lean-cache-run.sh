#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"

cd "$ROOT"
# Common stages supply a validated DLL; standalone calls refresh it through MSBuild.
if [[ -n "${STRATALINT_LEAN_CLI_DLL:-}" ]]; then
  cli=(dotnet "$STRATALINT_LEAN_CLI_DLL")
else
  cli=(dotnet run --project "$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj" --configuration Release --)
fi
exec "${cli[@]}" worktree with-cache-writer -- "$@"
