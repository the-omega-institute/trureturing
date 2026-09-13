#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
PROJECT="$ROOT/tools/StrataLint.Scribe.Documents/StrataLint.Scribe.Documents.csproj"
CLI_PROJECT="$ROOT/tools/StrataLint.Cli/StrataLint.Cli.csproj"
LEAN_REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/tools/scripts/report/report-consumer.sh"
MODE="${1:-}"
SOURCE_ARGS=()
if [[ $# -ge 2 ]]; then SOURCE_ARGS=(--base "$2"); fi

case "$MODE" in
  emit) ;;
  *) echo "usage: scribe.sh emit [BASE]" >&2; exit 2 ;;
esac

run_scribe() {
  local command=(dotnet run --project "$PROJECT" --configuration Release -- "$1")
  if [[ "$1" == "emit" ]]; then
    "$CONSUMER" --role scribe-consumer --report "$LEAN_REPORT" ${SOURCE_ARGS[@]+"${SOURCE_ARGS[@]}"} -- "${command[@]}"
  else
    "${command[@]}"
  fi
}

# The truth DAG projection lives here rather than in the Scribe binary: building the graph needs a
# RepositorySnapshot, which only the CLI's git gateway produces.
run_dag() {
  local command=(dotnet run --project "$CLI_PROJECT" --configuration Release -- dag-render)
  "${command[@]}"
}

run_generator() {
  case "$1" in
    emit|emit-values|filemap) run_scribe "$1" ;;
    dag) run_dag ;;
    *) echo "scribe: unknown generator '$1'" >&2; return 2 ;;
  esac
}

generators=(emit emit-values filemap dag)

cd "$ROOT"
for generator in "${generators[@]}"; do run_generator "$generator"; done
