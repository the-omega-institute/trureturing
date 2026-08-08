#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Scribe/StrataLint.Scribe.csproj"
CLI_PROJECT="$ROOT/Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj"
LEAN_REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
CONSUMER="$ROOT/Meta/StrataLint/scripts/report/report-consumer.sh"
MODE="${1:-}"
ORDER="${STRATALINT_PR_A_ORDER:-canonical}"
PARALLELISM="${STRATALINT_PR_A_PARALLELISM:-1}"

case "$MODE" in
  emit) ;;
  check) ;;
  *) echo "usage: scribe.sh emit|check" >&2; exit 2 ;;
esac

[[ "$PARALLELISM" =~ ^(1|4)$ ]] \
  || { echo "scribe: STRATALINT_PR_A_PARALLELISM must be 1 or 4" >&2; exit 2; }

run_scribe() {
  local command=(dotnet run --project "$PROJECT" --configuration Release -- "$1")
  if [[ "${STRATALINT_PR_A_NO_BUILD:-0}" == "1" ]]; then
    command=(dotnet run --no-build --project "$PROJECT" --configuration Release -- "$1")
  fi
  if [[ "$MODE" == "check" ]]; then
    command+=(--check)
  fi
  if [[ "$1" == "emit" ]]; then
    "$CONSUMER" --role scribe-consumer --report "$LEAN_REPORT" -- "${command[@]}"
  else
    "${command[@]}"
  fi
}

# The truth DAG projection lives here rather than in the Scribe binary: building the graph needs a
# RepositorySnapshot, which only the CLI's git gateway produces. Same emit/check contract.
run_dag() {
  local command=(dotnet run --project "$CLI_PROJECT" --configuration Release -- dag-render)
  if [[ "${STRATALINT_PR_A_NO_BUILD:-0}" == "1" ]]; then
    command=(dotnet run --no-build --project "$CLI_PROJECT" --configuration Release -- dag-render)
  fi
  if [[ "$MODE" == "check" ]]; then
    command+=(--check)
  fi
  "${command[@]}"
}

run_generator() {
  case "$1" in
    emit|catalog|emit-values|filemap) run_scribe "$1" ;;
    dag) run_dag ;;
    *) echo "scribe: unknown generator '$1'" >&2; return 2 ;;
  esac
}

case "$ORDER" in
  canonical) generators=(emit catalog emit-values filemap dag) ;;
  reverse) generators=(dag filemap emit-values catalog emit) ;;
  seeded-shuffle) generators=(emit-values dag emit filemap catalog) ;;
  *) echo "scribe: STRATALINT_PR_A_ORDER must be canonical, reverse, or seeded-shuffle" >&2; exit 2 ;;
esac

cd "$ROOT"
if [[ "$PARALLELISM" == "1" ]]; then
  for generator in "${generators[@]}"; do run_generator "$generator"; done
else
  running=0
  for generator in "${generators[@]}"; do
    run_generator "$generator" &
    ((running += 1))
    if ((running == PARALLELISM)); then
      wait
      running=0
    fi
  done
  wait
fi
