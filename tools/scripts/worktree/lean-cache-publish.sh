#!/usr/bin/env bash
# Release snapshots are optional local seeds. The caller owns the private cache writer.
# Names bind the resolved dependency/platform partition, declared report format
# and execution family; publisher suffixes disambiguate immutable snapshots.
# Production publication accepts clean protected-dev content from local or CI
# callers. Fetch filters old or mismatched names before requests for a snapshot
# and checks the manifest's full key before downloading build assets.
set -euo pipefail
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
ROOT="$(cd "$SCRIPT_DIR/../../.." && pwd -P)"
command=(python3 "$SCRIPT_DIR/lean_cache_release.py" "$@")
if [[ -f "$ROOT/tools/scripts/maintenance_log.py" ]]; then
  if [[ -n "${TRURETURING_MAINTENANCE_RUN_ID:-}" ]]; then
    export TRURETURING_MAINTENANCE_PARENT_RUN_ID="$TRURETURING_MAINTENANCE_RUN_ID"
  fi
  unset TRURETURING_MAINTENANCE_RUN_ID
  export TRURETURING_MAINTENANCE_SCRIPT=lean-cache-publish
  export TRURETURING_MAINTENANCE_REPOSITORY="$ROOT"
fi
exec "${command[@]}"
