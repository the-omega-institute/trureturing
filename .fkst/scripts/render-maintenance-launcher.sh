#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
TEMPLATE="$SCRIPT_DIR/../launchd/maintenance.plist.in"
# shellcheck source=.fkst/scripts/host-contract.sh
source "$SCRIPT_DIR/host-contract.sh"

xml_escape() {
  printf '%s' "$1" \
    | sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' -e 's/>/\&gt;/g' \
      -e 's/"/\&quot;/g' -e "s/'/\\&apos;/g"
}

replace_placeholder() {
  local name="$1" value="$2" escaped
  escaped="$(xml_escape "$value")"
  RENDERED="${RENDERED//@@$name@@/$escaped}"
}

main() {
  local host_config="${HOST_CONFIG:-}" output temporary output_directory
  [[ -n "$host_config" ]] \
    || { printf 'maintenance-launcher: HOST_CONFIG is required\n' >&2; return 2; }
  host_contract_load "$host_config"
  [[ -f "$TEMPLATE" ]] \
    || { printf 'maintenance-launcher: template is missing: %s\n' "$TEMPLATE" >&2; return 2; }

  output="${OUTPUT:-$FKST_MAINTENANCE_LAUNCHER_PATH}"
  host_contract_validate_value OUTPUT absolute_path "$output"
  output_directory="$(dirname -- "$output")"
  [[ -d "$output_directory" ]] \
    || { printf 'maintenance-launcher: output directory does not exist: %s\n' "$output_directory" >&2; return 2; }

  RENDERED="$(<"$TEMPLATE")"
  replace_placeholder FKST_MAINTENANCE_LAUNCHD_LABEL "$FKST_MAINTENANCE_LAUNCHD_LABEL"
  replace_placeholder FKST_HOST_ROOT "$FKST_HOST_ROOT"
  replace_placeholder HOST_CONFIG "$HOST_CONFIG"
  replace_placeholder PATH "$PATH"
  replace_placeholder FKST_GITHUB_BOT_LOGIN "$FKST_GITHUB_BOT_LOGIN"
  replace_placeholder FKST_DEVLOOP_INTEGRATION_BRANCH "$FKST_DEVLOOP_INTEGRATION_BRANCH"
  replace_placeholder FKST_MAINTENANCE_LAUNCHER_LOG "$FKST_MAINTENANCE_LAUNCHER_LOG"
  if printf '%s\n' "$RENDERED" | grep -qE '@@[A-Z][A-Z0-9_]*@@'; then
    printf 'maintenance-launcher: template contains an unresolved placeholder\n' >&2
    return 2
  fi

  temporary="$(mktemp "$output_directory/.maintenance-launcher.XXXXXXXX")"
  trap 'rm -f "$temporary"' EXIT
  printf '%s\n' "$RENDERED" > "$temporary"
  if command -v plutil >/dev/null 2>&1; then
    plutil -lint "$temporary" >/dev/null
  fi
  chmod 644 "$temporary"
  mv "$temporary" "$output"
  trap - EXIT
  printf '%s\n' "$output"
  if [[ -z "${OUTPUT:-}" ]]; then
    /bin/bash "$SCRIPT_DIR/install-launchd-launcher.sh" \
      "$output" "$FKST_MAINTENANCE_LAUNCHD_LABEL"
  fi
}

main "$@"
