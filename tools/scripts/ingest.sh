#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
VERB="${1:-}"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"

cd "$ROOT"
usage() {
  echo "USAGE: ingest.sh ingest SOURCES | mathlib-reanchor BASE [OLD_REPORT]" >&2
  exit 2
}

case "$VERB" in
  ingest)
    [[ $# -eq 2 && -n "$2" ]] || usage
    ingest_args=(ingest)
    set -f
    for selector in ${2:-}; do
      ingest_args+=(--source "$selector")
    done
    set +f
    if [[ ${#ingest_args[@]} -eq 1 ]]; then
      echo "SOURCE must contain at least one selector" >&2
      usage
    fi
    exec dotnet run --project "$PROJECT" --configuration Release -- \
      "${ingest_args[@]}"
    ;;
  mathlib-reanchor)
    [[ ( $# -eq 2 || $# -eq 3 ) && -n "$2" ]] || usage
    make -C "$ROOT" lean-report
    base_sha="$(git -C "$ROOT" merge-base HEAD "$2")"
    reanchor_args=(ledger-reanchor-mathlib --base "$base_sha")
    if [[ -n "${3:-}" ]]; then
      reanchor_args+=(--old-report "$3")
    fi
    dotnet run --project "$PROJECT" --configuration Release -- \
      "${reanchor_args[@]}"
    ;;
  *)
    usage
    ;;
esac
