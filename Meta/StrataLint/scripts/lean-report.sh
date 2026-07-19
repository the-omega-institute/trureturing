#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
SUPERVISOR="$ROOT/Meta/StrataLint/scripts/report-supervisor.sh"
INSPECTOR="$ROOT/Meta/StrataLint/lean-inspector/inspect.sh"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
LAKE_BIN="${LAKE_BIN:-$(command -v lake || true)}"

[[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo "lean-report.sh: an absolute lake executable is required" >&2; exit 2; }

exec "$SUPERVISOR" --role lean-producer --lean-slot -- \
  env LAKE_BIN="$LAKE_BIN" "$INSPECTOR" --repository "$ROOT" --output "$REPORT"
