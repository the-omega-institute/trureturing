#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
INSPECTOR_ARGS=(--repository "$ROOT" --output "${LEAN_REPORT:-$ROOT/.lake/build/stratalint/raw-lean-report.json}")
# Only this local entry recovers incompatible seeds. Shared inspect.sh callers
# retain their ordinary cold and incremental production paths.
if [[ "${REBUILD_REPORT_CACHE:-0}" == 1 ]]; then
  export STRATALINT_LEAN_REPORT_REUSE=0
else
  SEED="${STRATALINT_LEAN_REPORT_SEED:-${LEAN_REPORT:-$ROOT/.lake/build/stratalint/raw-lean-report.json}}"
  [[ "$SEED" == /* ]] || SEED="$ROOT/$SEED"
  seed_status() {
    python3 -B "$ROOT/tools/lean-inspector/reuse.py" seed-version --repository "$ROOT" --report "$SEED"
  }
  STATUS="$(seed_status)"
  read -r LOCAL_VERSION CURRENT_VERSION REASON <<< "$STATUS"
  if [[ "$REASON" != version-matched ]]; then
    DEV_SEED_VERSION=unavailable
    if /bin/bash "$ROOT/tools/scripts/worktree/lean-cache-publish.sh" fetch --mode production --refresh-stale; then
      SEED="$ROOT/.lake/build/stratalint/raw-lean-report.json"
      STATUS="$(seed_status)"
      read -r DEV_SEED_VERSION CURRENT_VERSION REASON <<< "$STATUS"
      export STRATALINT_LEAN_REPORT_SEED="$SEED"
    else
      REASON=fetch-unavailable
    fi
    if [[ "$REASON" != version-matched ]]; then
      printf 'LEAN_REPORT_CACHE_INCOMPATIBLE local_version=%s current_version=%s dev_seed_version=%s reason=%s\n' \
        "$LOCAL_VERSION" "$CURRENT_VERSION" "$DEV_SEED_VERSION" "$REASON" >&2
      printf '%s\n' 'Rebuild explicitly with make lean-report REBUILD_REPORT_CACHE=1' >&2
      exit 4
    fi
  fi
fi
if [[ -n "${STRATALINT_LEAN_REPORT_LOG_DIR:-}" ]]; then
  INSPECTOR_ARGS+=(--log-dir "$STRATALINT_LEAN_REPORT_LOG_DIR")
fi
exec "$ROOT/tools/lean-inspector/inspect.sh" "${INSPECTOR_ARGS[@]}"
