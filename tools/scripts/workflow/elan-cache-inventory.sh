#!/usr/bin/env bash
set -euo pipefail
[[ $# == 1 && -n "$1" ]] || { echo 'elan-cache-inventory: ELAN_DIRECTORY is required' >&2; exit 2; }
printf '%s\n' 'ELAN_CACHE_TOOLCHAINS'
ELAN_HOME="$1" "$1/bin/elan" toolchain list
