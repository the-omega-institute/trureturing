#!/usr/bin/env bash
# Import a transported report as an incremental seed, with no producer logs.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
BUNDLE="" CACHE_ROOT=""
while [[ $# -gt 0 ]]; do
  [[ $# -ge 2 ]] || exit 2
  case "$1" in
    --bundle) BUNDLE="$2" ;;
    --cache-root) CACHE_ROOT="$2" ;;
    *) echo "lean-report-ci-baseline: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift 2
done
[[ "$BUNDLE" == /* && "$CACHE_ROOT" == /* ]] \
  || { echo 'lean-report-ci-baseline: absolute --bundle and --cache-root are required' >&2; exit 2; }
exec python3 "$SCRIPT_DIR/../../lean-inspector/report_cache.py" import --report "$BUNDLE" --cache-root "$CACHE_ROOT"
