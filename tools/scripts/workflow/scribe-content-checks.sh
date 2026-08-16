#!/usr/bin/env bash
set -euo pipefail

if [[ $# -lt 1 || $# -gt 5 ]]; then
  echo "usage: scribe-content-checks.sh REPORT [SCRIBE_DLL [BASE [CHANGES_FILE PRODUCER_PATHS_FILE]]]" >&2
  exit 2
fi

REPORT="$1"
SCRIBE_DLL="${2:-}"
BASE="${3:-${STRATALINT_SCRIBE_BASE:-}}"
CHANGES_FILE="${4:-${STRATALINT_SCRIBE_CHANGES_FILE:-}}"
PRODUCER_PATHS_FILE="${5:-${STRATALINT_SCRIBE_PRODUCER_PATHS_FILE:-}}"
REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="$REPO_ROOT/tools/StrataLint.Scribe/StrataLint.Scribe.csproj"
if [[ ! -s "$REPORT" ]]; then
  echo "scribe-content-checks: raw Lean report is missing or empty at $REPORT" >&2
  exit 2
fi
if [[ -z "$BASE" ]]; then
  echo "scribe-content-checks: an exact merge-base is required for delta-scoped checks" >&2
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

DELTA_ARGS=()
TMP_ROOT=""
cleanup() {
  if [[ -n "$TMP_ROOT" ]]; then rm -rf -- "$TMP_ROOT"; fi
}
trap cleanup EXIT
if [[ -z "$CHANGES_FILE" && -z "$PRODUCER_PATHS_FILE" ]]; then
  TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-scribe-checks.XXXXXXXX")"
  CHANGES_FILE="$TMP_ROOT/changes"
  PRODUCER_PATHS_FILE="$TMP_ROOT/producer-paths"
  "$REPO_ROOT/tools/scripts/workflow/scribe-delta-input.sh" \
    "$REPO_ROOT" "$BASE" "$CHANGES_FILE" "$PRODUCER_PATHS_FILE"
elif [[ -z "$CHANGES_FILE" || -z "$PRODUCER_PATHS_FILE" ]]; then
  echo "scribe-content-checks: both delta manifest paths are required" >&2
  exit 2
fi
DELTA_ARGS=(
  --base "$BASE"
  --changes-file "$CHANGES_FILE"
  --producer-paths-file "$PRODUCER_PATHS_FILE")

run_scribe projections --check --report "$REPORT"
run_scribe emit --check "${DELTA_ARGS[@]}"
run_scribe emit-values --check "${DELTA_ARGS[@]}"
run_scribe describe-report --check
