#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
RENDERER="$SCRIPT_DIR/render-maintenance-launcher.sh"
# shellcheck source=.fkst/scripts/host-contract.sh
source "$SCRIPT_DIR/host-contract.sh"

main() {
  local host_config="${HOST_CONFIG:-}" deployed expected
  [[ -n "$host_config" ]] \
    || { printf 'maintenance-launcher-check: HOST_CONFIG is required\n' >&2; return 2; }
  host_contract_load "$host_config"
  deployed="${DEPLOYED_LAUNCHER:-$FKST_MAINTENANCE_LAUNCHER_PATH}"
  host_contract_validate_value DEPLOYED_LAUNCHER absolute_path "$deployed"
  [[ -f "$deployed" ]] \
    || { printf 'maintenance-launcher-check: deployed launcher is missing: %s\n' "$deployed" >&2; return 1; }

  MAINTENANCE_LAUNCHER_CHECK_TMP="$(mktemp -d -t maintenance-launcher-check.XXXXXXXX)"
  trap 'rm -rf "$MAINTENANCE_LAUNCHER_CHECK_TMP"' EXIT
  expected="$MAINTENANCE_LAUNCHER_CHECK_TMP/expected.plist"
  HOST_CONFIG="$HOST_CONFIG" OUTPUT="$expected" /bin/bash "$RENDERER" >/dev/null
  if ! cmp -s "$expected" "$deployed"; then
    printf 'maintenance-launcher-check: deployed launcher differs from tracked render: %s\n' \
      "$deployed" >&2
    return 1
  fi
  printf 'maintenance-launcher-check: conformant: %s\n' "$deployed"
}

main "$@"
