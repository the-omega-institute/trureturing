#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
POLICY="${LEAN_REPORT_CACHE_MISS_POLICY:-fetch-or-fail}"
if [[ "${REBUILD_REPORT_CACHE:-0}" == 1 ]]; then POLICY=build; fi
INSPECTOR_ARGS=(--repository "$ROOT" --output "${LEAN_REPORT:-$ROOT/.lake/build/stratalint/raw-lean-report.json}"
                --cache-miss-policy "$POLICY")
if [[ -n "${STRATALINT_LEAN_REPORT_LOG_DIR:-}" ]]; then
  INSPECTOR_ARGS+=(--log-dir "$STRATALINT_LEAN_REPORT_LOG_DIR")
fi
exec "$ROOT/tools/lean-inspector/inspect.sh" "${INSPECTOR_ARGS[@]}"
