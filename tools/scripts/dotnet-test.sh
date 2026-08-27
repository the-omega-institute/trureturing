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
dotnet run \
  --project "$ROOT/tools/StrataLint.EngineeringScope/StrataLint.EngineeringScope.csproj" \
  --configuration Release --no-launch-profile -- \
  verify-trx --results-directory "$RESULTS_DIRECTORY"
