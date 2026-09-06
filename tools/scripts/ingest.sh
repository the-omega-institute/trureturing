#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
VERB="${1:-}"
BASE="${2:-}"
PAYLOAD="${3:-}"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/tools/scripts/report/report-consumer.sh"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"

cd "$ROOT"
usage() {
  echo "USAGE: ingest.sh ingest|align-digestion-status|mathlib-reanchor|quarantine|quarantine-clear BASE [SOURCE|REQUEST|ATOM_ID]" >&2
  exit 2
}

[[ -n "$BASE" ]] || usage
case "$VERB" in
  ingest)
    [[ $# -le 3 ]] || usage
    ingest_args=(ingest --base "$BASE")
    set -f
    for selector in $PAYLOAD; do
      ingest_args+=(--source "$selector")
    done
    set +f
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      "${ingest_args[@]}"
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
  quarantine)
    [[ -n "$PAYLOAD" ]] || usage
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      quarantine-atom --request "$PAYLOAD" --base "$BASE"
    ;;
  quarantine-clear)
    [[ -n "$PAYLOAD" ]] || usage
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      quarantine-atom --clear "$PAYLOAD" --base "$BASE"
    ;;
  *)
    usage
    ;;
esac
