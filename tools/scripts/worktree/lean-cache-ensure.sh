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
  # Reused MSBuild nodes can hold these output pipes after the producer exits.
  export MSBUILDDISABLENODEREUSE=1
  cli=(dotnet run --project "$ROOT/tools/StrataLint.Lean/StrataLint.Lean.csproj" --configuration Release --)
fi
# An optional donor repository seeds a fresh .lake by clonefile; the native
# producer receives it only as an explicit argument, never from the environment.
donor=()
[[ -z "${STRATALINT_LEAN_CACHE_DONOR_REPOSITORY:-}" ]] || donor=(--donor-repository "$STRATALINT_LEAN_CACHE_DONOR_REPOSITORY")
exec "${cli[@]}" ensure-cache ${donor[@]+"${donor[@]}"}
