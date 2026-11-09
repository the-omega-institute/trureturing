#!/usr/bin/env bash
# Metadata helpers only: business commands retain their native owner and streams.
MAINTENANCE_LOG_SOURCE=""
MAINTENANCE_LOG_STATE=""

maintenance_log_begin() {
  local script="$1" repository="$2" owner="$3" parent="$4" state=""
  MAINTENANCE_LOG_SOURCE="$(cat "$repository/tools/scripts/maintenance_log.py" 2>/dev/null)" || return 0
  if state="$(cd / && python3 -B -c "$MAINTENANCE_LOG_SOURCE" begin \
      --repository "$repository" --script "$script" --owner-pid "$owner" --parent-pid "$parent" \
      </dev/null 2>/dev/null)" && [[ "$state" =~ ^[0-9a-f]{32}: ]]; then
    MAINTENANCE_LOG_STATE="$state"
    export TRURETURING_MAINTENANCE_RUN_ID="${state%%:*}"
  fi
  return 0
}

maintenance_log_finish() {
  local rc="$1"
  if [[ -n "$MAINTENANCE_LOG_STATE" ]]; then
    (cd / && python3 -B -c "$MAINTENANCE_LOG_SOURCE" finish \
      --state "$MAINTENANCE_LOG_STATE" --exit-code "$rc" </dev/null >/dev/null 2>/dev/null) || true
  fi
  return 0
}
