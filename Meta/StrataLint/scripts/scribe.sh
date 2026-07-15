#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
PROJECT="$ROOT/Meta/StrataLint/StrataLint.Scribe/StrataLint.Scribe.csproj"
INSPECTOR="$ROOT/Meta/StrataLint/lean-inspector/inspect.sh"
LEAN_REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
MODE="${1:-}"

case "$MODE" in
  emit) ;;
  check) ;;
  *) echo "usage: scribe.sh emit|check" >&2; exit 2 ;;
esac

run_scribe() {
  if [[ "$MODE" == "check" ]]; then
    dotnet run --project "$PROJECT" --configuration Release -- "$1" --check
  else
    dotnet run --project "$PROJECT" --configuration Release -- "$1"
  fi
}

cd "$ROOT"
if [[ "${SCRIBE_USE_EXISTING_REPORT:-0}" != "1" ]]; then
  LAKE_BIN="${LAKE_BIN:-$(command -v lake || true)}"
  [[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
    || { echo "scribe.sh: an absolute lake executable is required" >&2; exit 2; }
  LAKE_BIN="$LAKE_BIN" "$INSPECTOR" --repository "$ROOT" --output "$LEAN_REPORT"
fi
run_scribe emit
run_scribe catalog
run_scribe emit-values
run_scribe filemap
