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

require_runtime_package_directory() {
  local kind="$1" path="$2"
  [[ -d "$path" ]] \
    || {
      printf 'supervise-launcher: runtime %s package directory is missing: %s\n' \
        "$kind" "$path" >&2
      return 2
    }
}

validate_runtime_package_contract() {
  local tracked_workspace="$SCRIPT_DIR/../fkst.workspace.toml"
  local target_workspace="$FKST_HOST_ROOT/fkst.workspace.toml"
  local target_lock="$FKST_HOST_ROOT/fkst.lock"
  local package
  [[ -f "$target_workspace" && -r "$target_workspace" ]] \
    || {
      printf 'supervise-launcher: target fkst.workspace.toml is missing or unreadable: %s\n' \
        "$target_workspace" >&2
      return 2
    }
  [[ -f "$target_lock" && -r "$target_lock" ]] \
    || {
      printf 'supervise-launcher: target fkst.lock is missing or unreadable: %s\n' \
        "$target_lock" >&2
      return 2
    }

  "$FKST_PYTHON_BIN" - \
      "$tracked_workspace" \
      "$target_workspace" \
      "$target_lock" \
      "$FKST_PLATFORM_ROOT" \
      "$FKST_PLATFORM_PACKAGES" \
      "$FKST_HOST_PACKAGES" <<'PY'
import re
import subprocess
import sys
import tomllib
from pathlib import Path, PurePosixPath

REV_RE = re.compile(r"[0-9a-fA-F]{40}")
SOURCE_ID = "fkst-packages-platform"


def fail(message):
    raise ValueError(message)


def load_toml(path, role):
    try:
        with path.open("rb") as handle:
            data = tomllib.load(handle)
    except Exception as error:
        fail(f"{role} is invalid: {path}: {error}")
    if not isinstance(data, dict):
        fail(f"{role} must be a TOML table: {path}")
    return data


def tables(data, key, role):
    value = data.get(key, [])
    if isinstance(value, dict):
        value = [value]
    if not isinstance(value, list) or any(not isinstance(item, dict) for item in value):
        fail(f"{role} {key} must be a table array")
    return value


def source_composition(data, role):
    all_sources = tables(data, "external_sources", role)
    source_ids = []
    for source in all_sources:
        source_id = source.get("id")
        git_url = source.get("git")
        rev = source.get("rev")
        packages = source.get("packages")
        libraries = source.get("libraries")
        if (
            not isinstance(source_id, str)
            or re.fullmatch(r"[a-z0-9][a-z0-9-]*", source_id) is None
        ):
            fail(f"{role} contains an invalid external source id")
        if not isinstance(git_url, str) or not git_url:
            fail(f"{role} external source {source_id} is missing git")
        if not isinstance(rev, str) or REV_RE.fullmatch(rev) is None:
            fail(f"{role} external source {source_id} rev is not a full git SHA")
        for field, values in (("packages", packages), ("libraries", libraries)):
            if (
                not isinstance(values, list)
                or any(not isinstance(item, str) or not item for item in values)
                or len(values) != len(set(values))
            ):
                fail(f"{role} external source {source_id} {field} are invalid")
        source_ids.append(source_id)
    if len(source_ids) != len(set(source_ids)):
        fail(f"{role} contains duplicate external source ids")
    sources = [item for item in all_sources if item.get("id") == SOURCE_ID]
    if len(sources) != 1:
        fail(f"{role} must declare exactly one {SOURCE_ID} source")
    source = sources[0]
    git_url = source.get("git")
    packages = source.get("packages")
    if (
        not isinstance(packages, list)
        or not packages
        or any(not isinstance(item, str) or not item for item in packages)
        or len(packages) != len(set(packages))
    ):
        fail(f"{role} platform packages are invalid")
    workspace = data.get("workspace")
    units = workspace.get("units") if isinstance(workspace, dict) else None
    if not isinstance(units, list) or not units:
        fail(f"{role} workspace.units must be a non-empty array")
    host_packages = []
    for unit in units:
        path = PurePosixPath(unit) if isinstance(unit, str) else None
        if (
            path is None
            or len(path.parts) != 2
            or path.parts[0] != "packages"
            or not path.parts[1]
        ):
            fail(f"{role} workspace.units contains a noncanonical host package")
        host_packages.append(path.parts[1])
    if len(host_packages) != len(set(host_packages)):
        fail(f"{role} host packages contain duplicates")
    return packages, host_packages, source, all_sources


try:
    tracked_path = Path(sys.argv[1])
    target_path = Path(sys.argv[2])
    lock_path = Path(sys.argv[3])
    platform_root = Path(sys.argv[4])
    requested_platform = sys.argv[5].split()
    requested_host = sys.argv[6].split()

    tracked = load_toml(tracked_path, "tracked workspace manifest")
    target = load_toml(target_path, "target workspace manifest")
    lock = load_toml(lock_path, "target lockfile")
    tracked_platform, tracked_host, _, _ = source_composition(
        tracked,
        "tracked workspace manifest",
    )
    target_platform, target_host, target_source, target_sources = source_composition(
        target,
        "target workspace manifest",
    )
    if (
        target_platform != tracked_platform
        or target_host != tracked_host
        or requested_platform != tracked_platform
        or requested_host != tracked_host
    ):
        fail("runtime package composition differs from the tracked checkout")
    for package in requested_platform:
        owners = [
            source.get("id")
            for source in target_sources
            if package in source.get("packages", [])
        ]
        if len(owners) != 1:
            fail(f"requested platform package {package} has ambiguous ownership")
        if owners[0] != SOURCE_ID:
            fail(f"requested platform package {package} belongs to unexpected source {owners[0]}")

    lock_sources = [item for item in tables(lock, "external_source", "target lockfile") if item.get("id") == SOURCE_ID]
    if len(lock_sources) != 1:
        fail(f"target lockfile must contain exactly one {SOURCE_ID} source")
    lock_source = lock_sources[0]
    intent = lock_source.get("intent")
    resolved = lock_source.get("resolved")
    intended_rev = intent.get("rev") if isinstance(intent, dict) else None
    locked_rev = resolved.get("rev") if isinstance(resolved, dict) else None
    workspace_rev = target_source.get("rev")
    target_git = target_source.get("git")
    if lock_source.get("git") != target_git:
        fail("target workspace source git differs from target lockfile")
    if not isinstance(intended_rev, str) or REV_RE.fullmatch(intended_rev) is None:
        fail("target lockfile intent.rev is not a full git SHA")
    if not isinstance(locked_rev, str) or REV_RE.fullmatch(locked_rev) is None:
        fail("target lockfile resolved.rev is not a full git SHA")
    if intended_rev.lower() != locked_rev.lower():
        fail("target lockfile intent.rev differs from resolved.rev")
    if workspace_rev.lower() != intended_rev.lower():
        fail("target workspace source rev differs from target lockfile")
    lock_libraries = lock_source.get("libraries")
    if (
        not isinstance(lock_libraries, list)
        or any(not isinstance(item, dict) for item in lock_libraries)
    ):
        fail("target lockfile libraries must be a table array")
    lock_library_names = [item.get("name") for item in lock_libraries]
    if (
        any(not isinstance(name, str) or not name for name in lock_library_names)
        or len(lock_library_names) != len(set(lock_library_names))
    ):
        fail("target lockfile library names are invalid")
    if target_source.get("libraries") != lock_library_names:
        fail("target workspace libraries differ from target lockfile")

    try:
        platform_head = subprocess.run(
            ["git", "-C", str(platform_root), "rev-parse", "HEAD"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ).stdout.strip()
        platform_origin = subprocess.run(
            ["git", "-C", str(platform_root), "config", "--get", "remote.origin.url"],
            check=True,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        ).stdout.strip()
    except (FileNotFoundError, subprocess.CalledProcessError) as error:
        fail(f"trusted platform checkout identity is unavailable: {platform_root}: {error}")
    if platform_head.lower() != locked_rev.lower():
        fail("trusted platform checkout HEAD differs from target lockfile")
    if platform_origin.rstrip("/") != target_git.rstrip("/"):
        fail("trusted platform checkout origin differs from target workspace source")
except ValueError as error:
    print(f"supervise-launcher: {error}", file=sys.stderr)
    raise SystemExit(2)
PY

  for package in $FKST_PLATFORM_PACKAGES; do
    require_runtime_package_directory \
      platform "$FKST_PLATFORM_ROOT/packages/$package"
  done
  for package in $FKST_HOST_PACKAGES; do
    require_runtime_package_directory \
      host "$FKST_HOST_ROOT/packages/$package"
  done
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
  validate_runtime_package_contract
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
