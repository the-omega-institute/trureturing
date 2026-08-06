#!/usr/bin/env bash
set -euo pipefail

main() {
  local source="$1" label="$2"
  local launch_agents_dir="${FKST_LAUNCH_AGENTS_DIR:-$HOME/Library/LaunchAgents}"
  local destination temporary
  [[ "$source" == /* && -f "$source" && ! -L "$source" ]] \
    || { printf 'launchd-launcher-install: source is not a regular file: %s\n' "$source" >&2; return 2; }
  [[ "$label" =~ ^[A-Za-z0-9][A-Za-z0-9._-]*$ ]] \
    || { printf 'launchd-launcher-install: invalid label: %s\n' "$label" >&2; return 2; }
  [[ "$launch_agents_dir" == /* && -d "$launch_agents_dir" && ! -L "$launch_agents_dir" ]] \
    || { printf 'launchd-launcher-install: LaunchAgents directory is unavailable: %s\n' "$launch_agents_dir" >&2; return 2; }
  destination="$launch_agents_dir/$label.plist"
  [[ ! -L "$destination" ]] \
    || { printf 'launchd-launcher-install: installed member must not be a symlink: %s\n' "$destination" >&2; return 2; }
  temporary="$(mktemp "$launch_agents_dir/.${label}.XXXXXXXX")"
  trap 'rm -f "$temporary"' EXIT
  cp "$source" "$temporary"
  chmod 644 "$temporary"
  mv "$temporary" "$destination"
  trap - EXIT
  printf '%s\n' "$destination"
}

[[ "$#" -eq 2 ]] \
  || { printf 'usage: install-launchd-launcher.sh SOURCE LABEL\n' >&2; exit 2; }
main "$@"
