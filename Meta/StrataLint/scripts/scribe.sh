#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Scribe/StrataLint.Scribe.csproj"
LEAN_REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/Meta/StrataLint/scripts/report-consumer.sh"
MODE="${1:-}"

case "$MODE" in
  emit) ;;
  check) ;;
  *) echo "usage: scribe.sh emit|check" >&2; exit 2 ;;
esac

run_scribe() {
  local command=(dotnet run --project "$PROJECT" --configuration Release -- "$1")
  if [[ "$MODE" == "check" ]]; then
    command+=(--check)
  fi
  if [[ "$1" == "emit" ]]; then
    "$CONSUMER" --role scribe-consumer --report "$LEAN_REPORT" -- "${command[@]}"
  else
    "${command[@]}"
  fi
}

cd "$ROOT"
run_scribe emit
run_scribe catalog
run_scribe emit-values
run_scribe filemap
