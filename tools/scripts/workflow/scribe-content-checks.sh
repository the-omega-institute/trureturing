#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 2 ]]; then
  echo "usage: scribe-content-checks.sh REPORT [SCRIBE_DLL]" >&2
  exit 2
fi

REPORT="$1"
SCRIBE_DLL="${2:-}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="$REPO_ROOT/tools/StrataLint.Scribe/StrataLint.Scribe.csproj"
if [[ ! -s "$REPORT" ]]; then
  echo "scribe-content-checks: raw Lean report is missing or empty at $REPORT" >&2
  exit 2
fi
SCRIBE=(dotnet run --project "$PROJECT" --configuration Release --)
if [[ -n "$SCRIBE_DLL" ]]; then
  SCRIBE=(dotnet "$SCRIBE_DLL")
fi

cd "$REPO_ROOT"
run_scribe() {
  STRATALINT_LEAN_REPORT="$REPORT" "${SCRIBE[@]}" "$@"
}

run_scribe projections --check --report "$REPORT"
run_scribe emit --check
run_scribe emit-values --check
run_scribe describe-report --check
