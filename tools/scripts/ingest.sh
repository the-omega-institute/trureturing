#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
VERB="${1:-}"
BASE="${2:-}"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/tools/scripts/report/report-consumer.sh"
INPUT="$ROOT/tools/scripts/report/lean-report-input.sh"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"
BASE_TREE=""
REPORT_INPUT_STATE=""

cleanup() {
  [[ -z "$BASE_TREE" ]] || rm -rf -- "$BASE_TREE"
}
trap cleanup EXIT

report_input_state() {
  local base_sha current_address baseline_address
  base_sha="$(git -C "$ROOT" rev-parse --verify "${BASE}^{commit}")"
  BASE_TREE="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-ingest-base.XXXXXXXX")"
  git -C "$ROOT" archive --format=tar "$base_sha" | tar -xf - -C "$BASE_TREE"
  current_address="$("$INPUT" address --repository "$ROOT")"
  baseline_address="$("$INPUT" address --repository "$BASE_TREE")"
  if [[ "${current_address%% *}" == "${baseline_address%% *}" ]]; then
    REPORT_INPUT_STATE=unchanged
  else
    REPORT_INPUT_STATE=changed
  fi
}

cd "$ROOT"
[[ -n "$BASE" ]] \
  || { echo "USAGE: ingest.sh ingest|align-digestion-status|mathlib-reanchor BASE" >&2; exit 2; }
case "$VERB" in
  ingest)
    report_input_state
    cleanup
    BASE_TREE=""
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      ingest --base "$BASE" --report-input-state "$REPORT_INPUT_STATE"
    ;;
  align-digestion-status)
    exec "$CONSUMER" --role digestion-alignment-consumer --report "$REPORT" -- \
      dotnet run --project "$PROJECT" --configuration Release -- \
        align-digestion-status --base "$BASE"
    ;;
  mathlib-reanchor)
    make -C "$ROOT" lean-report
    base_sha="$(git -C "$ROOT" merge-base HEAD "$BASE")"
    dotnet run --project "$PROJECT" --configuration Release -- \
      ledger-reanchor-mathlib --base "$base_sha"
    exec "$CONSUMER" --role digestion-alignment-consumer --report "$REPORT" -- \
      dotnet run --project "$PROJECT" --configuration Release -- \
        align-digestion-status --base "$base_sha"
    ;;
  *)
    echo "USAGE: ingest.sh ingest|align-digestion-status|mathlib-reanchor BASE" >&2
    exit 2
    ;;
esac
