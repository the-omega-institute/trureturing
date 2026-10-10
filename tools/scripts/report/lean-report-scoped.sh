#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
TARGETS='' OUTPUT="${LEAN_REPORT:-$ROOT/.lake/build/stratalint/scoped-lean-report.json}"
LOG_DIR="${STRATALINT_LEAN_REPORT_LOG_DIR:-}"
while [[ $# -gt 0 ]]; do
  [[ $# -ge 2 ]] || { echo "lean-report-scoped: $1 requires a value" >&2; exit 2; }
  case "$1" in
    --targets) TARGETS="$2" ;;
    --output) OUTPUT="$2" ;;
    --log-dir) LOG_DIR="$2" ;;
    *) echo "lean-report-scoped: unknown option '$1'" >&2; exit 2 ;;
  esac
  shift 2
done
[[ "$TARGETS" =~ [^[:space:]] && -n "$OUTPUT" ]] \
  || { echo 'lean-report-scoped: explicit nonempty --targets are required' >&2; exit 2; }
ARGS=(produce --repository "$ROOT" --report "$OUTPUT" --targets "$TARGETS")
[[ -z "$LOG_DIR" ]] || ARGS+=(--log-dir "$LOG_DIR")
exec "$ROOT/tools/scripts/report/report-supervisor.sh" --role lean-producer --lean-slot -- \
  python3 -B "$ROOT/tools/lean-inspector/scoped.py" "${ARGS[@]}"
