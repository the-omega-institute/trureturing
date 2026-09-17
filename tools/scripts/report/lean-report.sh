#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
REPORT="${LEAN_REPORT:-$ROOT/.lake/build/stratalint/raw-lean-report.json}"
BASE="${STRATALINT_HISTORY_BASE:-}"
PURPOSE="${TEMPLATE_HISTORY:-check}"
while [[ $# -gt 0 ]]; do
  [[ $# -ge 2 && -n "$2" ]] || { echo 'lean-report: option requires a value' >&2; exit 2; }
  case "$1" in
    --protected-base) BASE="$2" ;;
    --purpose) PURPOSE="$2" ;;
    *) echo "lean-report: unknown option $1" >&2; exit 2 ;;
  esac
  shift 2
done
[[ "$PURPOSE" == check || "$PURPOSE" == seed || "$PURPOSE" == discharge ]] \
  || { echo 'lean-report: invalid purpose' >&2; exit 2; }
[[ "$REPORT" == /* ]] || REPORT="$ROOT/$REPORT"
base_args=()
if [[ -n "$BASE" ]]; then
  BASE="$(git -C "$ROOT" rev-parse --verify --end-of-options "${BASE}^{commit}")"
  base_args=(--protected-base "$BASE")
fi
"$ROOT/tools/lean-inspector/inspect.sh" --repository "$ROOT" --output "$REPORT"
STRATALINT_HISTORY_CLI_BUILT=1 "$ROOT/tools/scripts/report/history-report.sh" produce \
  --report "$REPORT" --purpose "$PURPOSE" ${base_args[@]+"${base_args[@]}"}
