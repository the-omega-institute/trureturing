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
  exec python3 -B "$ROOT/tools/scripts/maintenance_log.py" run \
    --repository "$ROOT" --script lean-cache-publish -- "${command[@]}"
fi
exec "${command[@]}"
