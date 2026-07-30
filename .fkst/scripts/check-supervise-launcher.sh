#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
RENDERER="$SCRIPT_DIR/render-supervise-launcher.sh"
# shellcheck source=.fkst/scripts/host-contract.sh
source "$SCRIPT_DIR/host-contract.sh"

main() {
  local host_config="${HOST_CONFIG:-}" deployed expected
  [[ -n "$host_config" ]] \
    || { printf 'supervise-launcher-check: HOST_CONFIG is required\n' >&2; return 2; }
  host_contract_load "$host_config"
  host_contract_require FKST_SUPERVISE_LAUNCHER_PATH
  deployed="${DEPLOYED_LAUNCHER:-$FKST_SUPERVISE_LAUNCHER_PATH}"
  host_contract_validate_value DEPLOYED_LAUNCHER absolute_path "$deployed"
  [[ -f "$deployed" ]] \
    || { printf 'supervise-launcher-check: deployed launcher is missing: %s\n' "$deployed" >&2; return 1; }

  SUPERVISE_LAUNCHER_CHECK_TMP="$(mktemp -d -t supervise-launcher-check.XXXXXXXX)"
  trap 'rm -rf "$SUPERVISE_LAUNCHER_CHECK_TMP"' EXIT
  expected="$SUPERVISE_LAUNCHER_CHECK_TMP/expected.plist"
  HOST_CONFIG="$HOST_CONFIG" OUTPUT="$expected" /bin/bash "$RENDERER" >/dev/null
  if ! cmp -s "$expected" "$deployed"; then
    printf 'supervise-launcher-check: deployed launcher differs from tracked render: %s\n' \
      "$deployed" >&2
    return 1
  fi
  printf 'supervise-launcher-check: conformant: %s\n' "$deployed"
}

main "$@"
