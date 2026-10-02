#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
POLICY=fetch-or-fail
REBUILD=0
while [[ $# -gt 0 ]]; do
  [[ $# -ge 2 ]] || { echo 'lean-report.sh: option requires a value' >&2; exit 2; }
  case "$1" in
    --cache-miss-policy) POLICY="$2" ;;
    --rebuild-report-cache) REBUILD="$2" ;;
    *) echo "lean-report.sh: unknown option '$1'" >&2; exit 2 ;;
  esac
  shift 2
done
case "$POLICY" in
  fetch-or-fail|reuse-or-build) ;;
  *) echo 'lean-report.sh: policy requires fetch-or-fail or reuse-or-build; rebuild with make lean-report REBUILD_REPORT_CACHE=1' >&2; exit 2 ;;
esac
if [[ "$REBUILD" == 1 ]]; then POLICY=build; fi
INSPECTOR_ARGS=(--repository "$ROOT" --output "${LEAN_REPORT:-$ROOT/.lake/build/stratalint/raw-lean-report.json}"
                --cache-miss-policy "$POLICY")
if [[ -n "${STRATALINT_LEAN_REPORT_LOG_DIR:-}" ]]; then
  INSPECTOR_ARGS+=(--log-dir "$STRATALINT_LEAN_REPORT_LOG_DIR")
fi
exec "$ROOT/tools/lean-inspector/inspect.sh" "${INSPECTOR_ARGS[@]}"
