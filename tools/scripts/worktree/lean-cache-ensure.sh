#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"

cd "$ROOT"
# Common stages supply a validated DLL; standalone calls refresh it through MSBuild.
if [[ -n "${STRATALINT_LEAN_PRODUCER_DLL:-}" ]]; then
  [[ "$STRATALINT_LEAN_PRODUCER_DLL" == /* && -f "$STRATALINT_LEAN_PRODUCER_DLL" ]] || {
    echo "lean-cache-ensure: STRATALINT_LEAN_PRODUCER_DLL must be an existing absolute path" >&2
    exit 2
  }
  cli=(dotnet "$STRATALINT_LEAN_PRODUCER_DLL")
else
  cli=(dotnet run --project "$ROOT/tools/StrataLint.Lean/StrataLint.Lean.csproj" --configuration Release --)
fi
exec "${cli[@]}" ensure-cache
