#!/bin/bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
RESULTS_DIRECTORY="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-test-results.XXXXXXXX")"

finish() {
  local rc="$1"
  trap - EXIT
  rm -rf -- "$RESULTS_DIRECTORY"
  exit "$rc"
}
trap 'finish "$?"' EXIT

dotnet test "$@" --configuration Release --verbosity normal \
  --logger 'trx;LogFilePrefix=canonical' --results-directory "$RESULTS_DIRECTORY"

OWNER_ASSEMBLY_ARGS=()
full_suite=1
for argument in "$@"; do
  if [[ "$argument" == "--filter" || "$argument" == --filter=* ]]; then
    full_suite=0
  fi
done

if [[ "$full_suite" -eq 1 ]]; then
  owner_assemblies="$(dotnet run \
    --project "$ROOT/tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" \
    --configuration Release --no-build --no-launch-profile -- \
    list-test-owner-assemblies --repository "$ROOT")"
  while IFS= read -r owner_assembly; do
    [[ -n "$owner_assembly" ]] || continue
    OWNER_ASSEMBLY_ARGS+=(--required-assembly "$owner_assembly")
  done <<< "$owner_assemblies"
fi

dotnet run \
  --project "$ROOT/tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" \
  --configuration Release --no-build --no-launch-profile -- \
  verify-trx --results-directory "$RESULTS_DIRECTORY" "${OWNER_ASSEMBLY_ARGS[@]}"
