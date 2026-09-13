#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
INSPECTOR="$ROOT/tools/lean-inspector/inspect.sh"
PAIR="$ROOT/tools/scripts/lean-report-pair.sh"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
LAKE_BIN="${LAKE_BIN:-$(command -v lake || true)}"

[[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo "lean-report.sh: an absolute lake executable is required" >&2; exit 2; }

# Every invocation enters the incremental producer with optional partitioned seeds.
export STRATALINT_REPORT_CACHE_ROOT="${STRATALINT_REPORT_CACHE_ROOT:-$ROOT/.lake/report-cache}"

exec "$PAIR" \
  --producer "$INSPECTOR" \
  --lake-bin "$LAKE_BIN" \
  --candidate-root "$ROOT" \
  --candidate-output "$REPORT"
