#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
PROJECT="$ROOT/tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj"
LEAN_REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/tools/scripts/report/report-consumer.sh"
MODE="${1:-}"

case "$MODE" in
  emit) ;;
  *) echo "usage: scribe.sh emit" >&2; exit 2 ;;
esac

run_scribe() {
  local command=(dotnet run --project "$PROJECT" --configuration Release -- "$1")
  if [[ "$1" == "emit" ]]; then
    "$CONSUMER" --role scribe-consumer --report "$LEAN_REPORT" -- "${command[@]}"
  else
    "${command[@]}"
  fi
}

run_generator() {
  case "$1" in
    emit|emit-values) run_scribe "$1" ;;
    *) echo "scribe: unknown generator '$1'" >&2; return 2 ;;
  esac
}

generators=(emit emit-values)

cd "$ROOT"
for generator in "${generators[@]}"; do run_generator "$generator"; done
