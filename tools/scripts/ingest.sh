#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
VERB="${1:-}"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/tools/scripts/report/report-consumer.sh"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"

cd "$ROOT"
usage() {
  echo "USAGE: ingest.sh ingest [SOURCES] | align-digestion-status [1] | refresh-source-registry SOURCE [1] | mathlib-reanchor BASE | quarantine REQUEST | quarantine-clear ATOM_ID" >&2
  exit 2
}

align() {
  exec "$CONSUMER" --role digestion-alignment-consumer --report "$REPORT" -- \
    dotnet run --project "$PROJECT" --configuration Release -- \
      align-digestion-status "$@"
}

case "$VERB" in
  ingest)
    [[ $# -le 2 ]] || usage
    ingest_args=(ingest)
    set -f
    for selector in ${2:-}; do
      ingest_args+=(--source "$selector")
    done
    set +f
    if [[ -n "${2:-}" && ${#ingest_args[@]} -eq 1 ]]; then
      echo "SOURCE must contain at least one selector" >&2
      usage
    fi
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      "${ingest_args[@]}"
    ;;
  align-digestion-status)
    [[ $# -le 2 && ( -z "${2:-}" || "${2:-}" == 1 ) ]] || usage
    if [[ "${2:-}" == 1 ]]; then
      align --plan
    else
      align
    fi
    ;;
  refresh-source-registry)
    [[ $# -le 3 && -n "${2:-}" && ( -z "${3:-}" || "${3:-}" == 1 ) ]] || usage
    if [[ "${3:-}" == 1 ]]; then
      align --refresh-source "$2" --plan
    else
      align --refresh-source "$2"
    fi
    ;;
  mathlib-reanchor)
    [[ $# -eq 2 && -n "$2" ]] || usage
    make -C "$ROOT" lean-report
    base_sha="$(git -C "$ROOT" merge-base HEAD "$2")"
    dotnet run --project "$PROJECT" --configuration Release -- \
      ledger-reanchor-mathlib --base "$base_sha"
    align
    ;;
  quarantine)
    [[ $# -eq 2 && -n "$2" ]] || usage
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      quarantine-atom --request "$2"
    ;;
  quarantine-clear)
    [[ $# -eq 2 && -n "$2" ]] || usage
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      quarantine-atom --clear "$2"
    ;;
  *)
    usage
    ;;
esac
