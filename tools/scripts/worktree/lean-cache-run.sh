#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
[[ $# -gt 0 ]] || { echo 'lean-cache-run: COMMAND is required' >&2; exit 2; }
cd "$ROOT"
if [[ -n "${STRATALINT_LEAN_PRODUCER_DLL:-}" ]]; then
  [[ "$STRATALINT_LEAN_PRODUCER_DLL" == /* && -f "$STRATALINT_LEAN_PRODUCER_DLL" ]] || { echo 'lean-cache-run: candidate producer DLL is absent' >&2; exit 2; }
  cli=(dotnet "$STRATALINT_LEAN_PRODUCER_DLL")
else
  cli=(dotnet run --project "$ROOT/tools/StrataLint.Lean/StrataLint.Lean.csproj" --configuration Release --)
fi
donor=()
[[ -z "${STRATALINT_LEAN_CACHE_DONOR_REPOSITORY:-}" ]] || donor=(--donor-repository "$STRATALINT_LEAN_CACHE_DONOR_REPOSITORY")
exec "${cli[@]}" with-cache-reader ${donor[@]+"${donor[@]}"} -- "$@"
