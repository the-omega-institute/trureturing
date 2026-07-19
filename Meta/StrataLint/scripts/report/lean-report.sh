#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
INSPECTOR="$ROOT/Meta/StrataLint/lean-inspector/inspect.sh"
PAIR="$ROOT/Meta/StrataLint/scripts/lean-report-pair.sh"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
LAKE_BIN="${LAKE_BIN:-$(command -v lake || true)}"

[[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo "lean-report.sh: an absolute lake executable is required" >&2; exit 2; }

exec "$PAIR" --single \
  --producer "$INSPECTOR" \
  --lake-bin "$LAKE_BIN" \
  --candidate-root "$ROOT" \
  --candidate-output "$REPORT"
