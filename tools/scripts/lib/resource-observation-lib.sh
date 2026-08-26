#!/usr/bin/env bash

resource_observation_number_or_unknown() {
  local value="${1:-}"
  if [[ "$value" =~ ^[0-9]+$ ]]; then printf '%s' "$value"; else printf 'unknown'; fi
}

resource_disk_free_kb() {
  local root="$1"
  df -Pk "$root" 2>/dev/null \
    | awk 'NR > 1 { value=$4 } END { if (value ~ /^[0-9]+$/) print value }' \
    || true
}

resource_fd_soft_limit() {
  local value=""
  value="$(ulimit -Sn 2>/dev/null || true)"
  resource_observation_number_or_unknown "$value"
}

resource_observe() {
  local stage="$1"
  local root="$2"
  local fd_peak="${3:-unknown}"
  local rss_peak_kb="${4:-unknown}"
  local disk_free_kb=""
  disk_free_kb="$(resource_disk_free_kb "$root")"
  printf 'RESOURCE_OBSERVATION stage=%s disk_free_kb=%s fd_soft_limit=%s fd_peak=%s rss_peak_kb=%s\n' \
    "$stage" \
    "$(resource_observation_number_or_unknown "$disk_free_kb")" \
    "$(resource_fd_soft_limit)" \
    "$(resource_observation_number_or_unknown "$fd_peak")" \
    "$(resource_observation_number_or_unknown "$rss_peak_kb")" >&2
}
