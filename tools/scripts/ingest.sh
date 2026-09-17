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
  echo "USAGE: ingest.sh ingest|align-digestion-status|refresh-source-registry|mathlib-reanchor|quarantine|quarantine-clear BASE [SOURCE|REQUEST|ATOM_ID|1] [PLAN_SHA256]" >&2
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
    if [[ -n "$PAYLOAD" && ${#ingest_args[@]} -eq 3 ]]; then
      echo "SOURCE must contain at least one selector" >&2
      usage
    fi
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      "${ingest_args[@]}"
    ;;
  refresh-source-registry|align-digestion-status)
    alignment_args=(--base "$BASE")
    if [[ "$VERB" == refresh-source-registry ]]; then
      [[ $# -le 4 && -n "$PAYLOAD" ]] || usage
      alignment_args+=(--refresh-source "$PAYLOAD")
      if [[ -n "${4:-}" ]]; then
        alignment_args+=(--apply "$4")
      else
        alignment_args+=(--plan)
      fi
    else
      [[ $# -le 3 && ( -z "$PAYLOAD" || "$PAYLOAD" == 1 ) ]] || usage
      if [[ "$PAYLOAD" == 1 ]]; then
        alignment_args+=(--plan)
      fi
    fi
    exec "$CONSUMER" --role digestion-alignment-consumer --report "$REPORT" --protected-base "$BASE" -- \
      dotnet run --project "$PROJECT" --configuration Release -- \
        align-digestion-status "${alignment_args[@]}"
    ;;
  mathlib-reanchor)
    base_sha="$(git -C "$ROOT" merge-base HEAD "$BASE")"
    BASE="$base_sha"
    make -C "$ROOT" lean-report BASE="$base_sha"
    dotnet run --project "$PROJECT" --configuration Release -- \
      ledger-reanchor-mathlib --base "$base_sha"
    exec "$CONSUMER" --role digestion-alignment-consumer --report "$REPORT" --protected-base "$BASE" -- \
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
