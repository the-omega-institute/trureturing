#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
TEMPLATE="$SCRIPT_DIR/../launchd/supervise.plist.in"
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

load_package_composition() {
  local workspace="$SCRIPT_DIR/../fkst.workspace.toml" data
  [[ -f "$workspace" ]] \
    || { printf 'supervise-launcher: workspace manifest is missing: %s\n' "$workspace" >&2; return 2; }
  data="$("$FKST_PYTHON_BIN" - "$workspace" <<'PY'
import re
import sys
import tomllib
from pathlib import PurePosixPath

try:
    with open(sys.argv[1], "rb") as handle:
        manifest = tomllib.load(handle)
    sources = [
        source for source in manifest.get("external_sources", [])
        if source.get("id") == "fkst-packages-platform"
    ]
    if len(sources) != 1:
        raise ValueError("expected one fkst-packages-platform source")
    packages = sources[0].get("packages")
    if (
        not isinstance(packages, list)
        or not packages
        or any(
            not isinstance(value, str)
            or re.fullmatch(r"[a-z0-9][a-z0-9-]*", value) is None
            for value in packages
        )
        or len(packages) != len(set(packages))
    ):
        raise ValueError("platform packages must be unique non-empty strings")
    units = manifest.get("workspace", {}).get("units")
    if not isinstance(units, list) or not units:
        raise ValueError("workspace units must be a non-empty array")
    host_packages = []
    for unit in units:
        path = PurePosixPath(unit) if isinstance(unit, str) else None
        if (
            path is None
            or len(path.parts) != 2
            or path.parts[0] != "packages"
            or re.fullmatch(r"[a-z0-9][a-z0-9-]*", path.parts[1]) is None
        ):
            raise ValueError("workspace units must be canonical packages/<name> paths")
        host_packages.append(path.parts[1])
    if len(host_packages) != len(set(host_packages)):
        raise ValueError("workspace units contain duplicate package names")
except Exception as error:
    raise SystemExit(f"{sys.argv[1]}: {error}")

print(" ".join(packages))
print(" ".join(host_packages))
PY
)" || {
    printf 'supervise-launcher: invalid workspace package composition\n' >&2
    return 2
  }
  FKST_PLATFORM_PACKAGES="$(printf '%s\n' "$data" | sed -n '1p')"
  FKST_HOST_PACKAGES="$(printf '%s\n' "$data" | sed -n '2p')"
}

require_runtime_executable() {
  local path="$1"
  [[ -f "$path" && -x "$path" ]] \
    || {
      printf 'supervise-launcher: runtime executable is missing or not executable: %s\n' \
        "$path" >&2
      return 2
    }
}

require_runtime_directory() {
  local path="$1"
  [[ -d "$path" ]] \
    || { printf 'supervise-launcher: runtime directory is missing: %s\n' "$path" >&2; return 2; }
}

validate_runtime_paths() {
  local run_script runtime_deploy_config log_directory
  require_runtime_executable "$FKST_ZSH_BIN"
  require_runtime_executable "$FKST_BASH_BIN"
  require_runtime_executable "$FKST_PYTHON_BIN"
  [[ -f "$HOST_CONFIG" && -r "$HOST_CONFIG" ]] \
    || { printf 'supervise-launcher: host config is missing or unreadable: %s\n' "$HOST_CONFIG" >&2; return 2; }
  require_runtime_directory "$FKST_HOST_ROOT"
  require_runtime_directory "$FKST_HOST_ROOT/packages"
  runtime_deploy_config="$FKST_HOST_ROOT/.fkst/deploy.env"
  [[ -f "$runtime_deploy_config" && -r "$runtime_deploy_config" ]] \
    || {
      printf 'supervise-launcher: runtime deploy config is missing or unreadable: %s\n' \
        "$runtime_deploy_config" >&2
      return 2
    }
  require_runtime_directory "$FKST_PLATFORM_ROOT"
  require_runtime_directory "$FKST_DURABLE_ROOT"
  require_runtime_directory "$FKST_RUNTIME_ROOT"
  run_script="$FKST_PLATFORM_ROOT/scripts/run.sh"
  [[ -f "$run_script" && -r "$run_script" ]] \
    || { printf 'supervise-launcher: platform run script is missing or unreadable: %s\n' "$run_script" >&2; return 2; }
  log_directory="$(dirname -- "$FKST_SUPERVISE_LAUNCHER_LOG")"
  [[ -d "$log_directory" && -w "$log_directory" ]] \
    || { printf 'supervise-launcher: log directory is missing or not writable: %s\n' "$log_directory" >&2; return 2; }
  if [[ -e "$FKST_SUPERVISE_LAUNCHER_LOG" || -L "$FKST_SUPERVISE_LAUNCHER_LOG" ]]; then
    [[ -f "$FKST_SUPERVISE_LAUNCHER_LOG" && -w "$FKST_SUPERVISE_LAUNCHER_LOG" ]] \
      || {
        printf 'supervise-launcher: existing log path is not a writable regular file: %s\n' \
          "$FKST_SUPERVISE_LAUNCHER_LOG" >&2
        return 2
      }
  fi
}

main() {
  local host_config="${HOST_CONFIG:-}" output temporary output_directory
  [[ -n "$host_config" ]] \
    || { printf 'supervise-launcher: HOST_CONFIG is required\n' >&2; return 2; }
  host_contract_load "$host_config"
  host_contract_require \
    FKST_BASH_BIN \
    FKST_ZSH_BIN \
    FKST_PYTHON_BIN \
    FKST_SUPERVISE_LAUNCHER_LOG \
    FKST_SUPERVISE_LAUNCHER_PATH
  validate_runtime_paths
  load_package_composition
  [[ -f "$TEMPLATE" ]] \
    || { printf 'supervise-launcher: template is missing: %s\n' "$TEMPLATE" >&2; return 2; }

  output="${OUTPUT:-$FKST_SUPERVISE_LAUNCHER_PATH}"
  host_contract_validate_value OUTPUT absolute_path "$output"
  output_directory="$(dirname -- "$output")"
  [[ -d "$output_directory" ]] \
    || { printf 'supervise-launcher: output directory does not exist: %s\n' "$output_directory" >&2; return 2; }

  RENDERED="$(<"$TEMPLATE")"
  replace_placeholder FKST_LAUNCHD_LABEL "$FKST_LAUNCHD_LABEL"
  replace_placeholder FKST_ZSH_BIN "$FKST_ZSH_BIN"
  replace_placeholder HOST_CONFIG "$HOST_CONFIG"
  replace_placeholder FKST_BASH_BIN "$FKST_BASH_BIN"
  replace_placeholder FKST_SUPERVISE_LAUNCHER_LOG "$FKST_SUPERVISE_LAUNCHER_LOG"
  replace_placeholder FKST_HOST_ROOT "$FKST_HOST_ROOT"
  replace_placeholder FKST_PLATFORM_PACKAGES "$FKST_PLATFORM_PACKAGES"
  replace_placeholder FKST_HOST_PACKAGES "$FKST_HOST_PACKAGES"
  if printf '%s\n' "$RENDERED" | grep -qE '@@[A-Z][A-Z0-9_]*@@'; then
    printf 'supervise-launcher: template contains an unresolved placeholder\n' >&2
    return 2
  fi

  temporary="$(mktemp "$output_directory/.supervise-launcher.XXXXXXXX")"
  trap 'rm -f "$temporary"' EXIT
  printf '%s\n' "$RENDERED" > "$temporary"
  if command -v plutil >/dev/null 2>&1; then
    plutil -lint "$temporary" >/dev/null
  fi
  chmod 644 "$temporary"
  mv "$temporary" "$output"
  trap - EXIT
  printf '%s\n' "$output"
}

main "$@"
