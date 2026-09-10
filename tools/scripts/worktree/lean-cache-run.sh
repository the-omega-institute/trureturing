#!/usr/bin/env bash
set -u

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"

cd "$ROOT"
# Common stages supply a validated DLL; standalone calls refresh it through MSBuild.
if [[ -n "${STRATALINT_LEAN_PRODUCER_DLL:-}" ]]; then
  cli=(dotnet "$STRATALINT_LEAN_PRODUCER_DLL")
else
  cli=(dotnet run --project "$ROOT/tools/StrataLint.Lean/StrataLint.Lean.csproj" --configuration Release --)
fi
exec "${cli[@]}" lean-cache-writer -- "$@"
