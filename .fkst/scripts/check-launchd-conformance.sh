#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd -P)"
REPOSITORY_ROOT="$(cd -- "$SCRIPT_DIR/../.." && pwd -P)"
INVENTORY="$SCRIPT_DIR/../operations.toml"
# shellcheck source=.fkst/scripts/host-contract.sh
source "$SCRIPT_DIR/host-contract.sh"

die() {
  printf 'launchd-conformance-check: %s\n' "$*" >&2
  return 1
}

default_launchd_enumerator() {
  local output header line pid status label extra
  output="$(/bin/launchctl list)" || return $?
  IFS= read -r header <<EOF
$output
EOF
  [[ "$header" == $'PID\tStatus\tLabel' ]] || return 65
  while IFS= read -r line || [[ -n "$line" ]]; do
    [[ "$line" == "$header" ]] && continue
    read -r pid status label extra <<EOF
$line
EOF
    [[ -n "${pid:-}" && -n "${status:-}" && -n "${label:-}" && -z "${extra:-}" ]] \
      || return 65
    printf '%s\n' "$label"
  done <<EOF
$output
EOF
}

load_declared_units() {
  "$FKST_PYTHON_BIN" - "$INVENTORY" <<'PY'
import re
import sys
import tomllib

ID = re.compile(r"[a-z0-9][a-z0-9-]*")

try:
    with open(sys.argv[1], "rb") as handle:
        inventory = tomllib.load(handle)
    units = inventory.get("launchd_units")
    operations = inventory.get("operations")
    if (
        not isinstance(units, list)
        or not units
        or any(not isinstance(unit, str) or ID.fullmatch(unit) is None for unit in units)
        or len(units) != len(set(units))
    ):
        raise ValueError("launchd_units must be a unique non-empty canonical array")
    if not isinstance(operations, list):
        raise ValueError("operations must be an array")
    by_id = {
        operation.get("id"): operation
        for operation in operations
        if isinstance(operation, dict) and isinstance(operation.get("id"), str)
    }
    for unit in units:
        for role in ("render", "check"):
            operation_id = f"{unit}-launcher-{role}"
            expected = {
                "id": operation_id,
                "make_target": operation_id,
                "implementation": f".fkst/scripts/{role}-{unit}-launcher.sh",
            }
            operation = by_id.get(operation_id)
            if operation is None:
                raise ValueError(f"launchd unit {unit} has no {role} operation")
            for key, value in expected.items():
                if operation.get(key) != value:
                    raise ValueError(
                        f"launchd unit {unit} {role} operation has invalid {key}"
                    )
except Exception as error:
    raise SystemExit(f"{sys.argv[1]}: {error}")

for unit in sorted(units):
    print(unit)
PY
}

contains_unit() {
  local wanted="$1" unit
  shift
  for unit in "$@"; do
    [[ "$unit" == "$wanted" ]] && return 0
  done
  return 1
}

main() {
  local host_config="${HOST_CONFIG:-}" enumerator="${FKST_LAUNCHD_ENUMERATOR:-}"
  local make_bin="${FKST_MAKE_BIN:-}" supervise_prefix maintenance_prefix namespace
  local labels enumerator_status label unit declared_output template renderer checker
  local -a host_units=() declared_units=()
  [[ -n "$host_config" ]] || { die 'HOST_CONFIG is required'; return; }
  host_contract_load "$host_config"
  host_contract_require \
    FKST_PYTHON_BIN \
    FKST_LAUNCHD_LABEL \
    FKST_MAINTENANCE_LAUNCHD_LABEL

  supervise_prefix="${FKST_LAUNCHD_LABEL%.supervise}"
  maintenance_prefix="${FKST_MAINTENANCE_LAUNCHD_LABEL%.maintenance}"
  [[ "$FKST_LAUNCHD_LABEL" == "$supervise_prefix.supervise" \
      && "$FKST_MAINTENANCE_LAUNCHD_LABEL" == "$maintenance_prefix.maintenance" \
      && "$supervise_prefix" == "$maintenance_prefix" ]] \
    || { die 'configured launchd labels do not share a deployment namespace'; return; }
  namespace="$supervise_prefix"

  if [[ -n "$enumerator" ]]; then
    [[ "$enumerator" == /* && -f "$enumerator" && -x "$enumerator" ]] \
      || { die "launchd membership enumerator is not an executable absolute path: $enumerator"; return; }
    set +e
    labels="$("$enumerator")"
    enumerator_status=$?
    set -e
  else
    set +e
    labels="$(default_launchd_enumerator)"
    enumerator_status=$?
    set -e
  fi
  if [[ "$enumerator_status" -ne 0 ]]; then
    die "launchd membership enumerator failed with exit $enumerator_status"
    return
  fi

  while IFS= read -r label || [[ -n "$label" ]]; do
    [[ -z "$label" ]] && continue
    [[ "$label" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] \
      || { die "launchd membership enumerator returned an invalid label: $label"; return; }
    [[ "$label" == "$namespace."* ]] || continue
    unit="${label#"$namespace."}"
    [[ "$unit" =~ ^[a-z0-9][a-z0-9-]*$ ]] \
      || { die "deployment launchd label has a noncanonical unit id: $label"; return; }
    if [[ "${#host_units[@]}" -gt 0 ]] \
        && contains_unit "$unit" "${host_units[@]}"; then
      die "launchd membership enumerator returned duplicate unit $unit"
      return
    fi
    host_units+=("$unit")
  done <<EOF
$labels
EOF
  [[ "${#host_units[@]}" -gt 0 ]] \
    || { die "no launchd units found for deployment namespace $namespace"; return; }

  declared_output="$(load_declared_units)" \
    || { die 'operational launchd inventory is unavailable or invalid'; return; }
  while IFS= read -r unit || [[ -n "$unit" ]]; do
    [[ -n "$unit" ]] && declared_units+=("$unit")
  done <<EOF
$declared_output
EOF
  [[ "${#declared_units[@]}" -gt 0 ]] \
    || { die 'operational launchd inventory returned an ungrounded empty set'; return; }

  for unit in "${host_units[@]}"; do
    contains_unit "$unit" "${declared_units[@]}" \
      || { die "launchd unit $unit is absent from operational inventory"; return; }
  done
  for unit in "${declared_units[@]}"; do
    contains_unit "$unit" "${host_units[@]}" \
      || { die "inventory launchd unit $unit is absent from host membership"; return; }
    template="$REPOSITORY_ROOT/.fkst/launchd/$unit.plist.in"
    renderer="$REPOSITORY_ROOT/.fkst/scripts/render-$unit-launcher.sh"
    checker="$REPOSITORY_ROOT/.fkst/scripts/check-$unit-launcher.sh"
    [[ -f "$template" ]] || { die "launchd unit $unit template is missing: $template"; return; }
    [[ -f "$renderer" ]] \
      || { die "launchd unit $unit renderer is missing: $renderer"; return; }
    [[ -f "$checker" ]] \
      || { die "launchd unit $unit checker is missing: $checker"; return; }
  done

  if [[ -z "$make_bin" ]]; then
    make_bin="$(command -v make)" \
      || { die 'make is unavailable'; return; }
  fi
  [[ "$make_bin" == /* && -f "$make_bin" && -x "$make_bin" ]] \
    || { die "make is not an executable absolute path: $make_bin"; return; }
  for unit in "${declared_units[@]}"; do
    HOST_CONFIG="$HOST_CONFIG" "$make_bin" -s -C "$REPOSITORY_ROOT" \
      "$unit-launcher-check"
  done
  printf 'launchd-conformance-check: conformant units: %s\n' "${declared_units[*]}"
}

main "$@"
