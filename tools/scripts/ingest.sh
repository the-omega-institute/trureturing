#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
VERB="${1:-}"
PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"

cd "$ROOT"
usage() {
  echo "USAGE: ingest.sh ingest [SOURCES] | mathlib-reanchor BASE" >&2
  exit 2
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
  mathlib-reanchor)
    [[ $# -eq 2 && -n "$2" ]] || usage
    make -C "$ROOT" lean-report
    base_sha="$(git -C "$ROOT" merge-base HEAD "$2")"
    dotnet run --project "$PROJECT" --configuration Release -- \
      ledger-reanchor-mathlib --base "$base_sha"
    ;;
  *)
    usage
    ;;
esac
