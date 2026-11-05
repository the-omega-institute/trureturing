#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C


# The report consumer also sources the shared manifest and memo primitives.
if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  COMMAND="${1:-}"
  if [[ -n "$COMMAND" ]]; then shift; fi
  REPOSITORY=""
  while [[ $# -gt 0 ]]; do
    case "$1" in
      --repository) REPOSITORY="${2:?--repository needs a value}"; shift 2 ;;
      *) echo "lean-cache-input: unknown argument '$1'" >&2; exit 2 ;;
    esac
  done
  [[ "$COMMAND" == "partition" || "$COMMAND" == "partition-path" ]] \
    || { echo "usage: lean-cache-input.sh partition|partition-path --repository DIR" >&2; exit 2; }
  [[ -n "$REPOSITORY" && "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
    || { echo "lean-cache-input: --repository requires an absolute directory" >&2; exit 2; }
  REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
  TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-lean-input.XXXXXXXX")"
  cleanup() { rm -rf -- "$TMP_ROOT"; }
  trap cleanup EXIT
fi

lean_partition_helper() {
  local helper
  helper="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/lean_cache.py"
  python3 "$helper" "$@" --repository "$REPOSITORY"
}

hash_file() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | awk '{print $1}'
  elif command -v openssl >/dev/null 2>&1; then
    openssl dgst -sha256 "$1" | awk '{print $NF}'
  else
    shasum -a 256 "$1" | awk '{print $1}'
  fi
}

if [[ "${BASH_SOURCE[0]}" == "$0" ]]; then
  lean_partition_helper "$COMMAND"
fi
