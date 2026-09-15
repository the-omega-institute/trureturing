#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
INSPECTOR="$ROOT/tools/lean-inspector/inspect.sh"
PAIR="$ROOT/tools/scripts/lean-report-pair.sh"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
# Every invocation enters the incremental producer with optional partitioned seeds.
export STRATALINT_REPORT_CACHE_ROOT="${STRATALINT_REPORT_CACHE_ROOT:-$ROOT/.lake/report-cache}"

exec "$PAIR" \
  --producer "$INSPECTOR" \
  --candidate-root "$ROOT" \
  --candidate-output "$REPORT" "$@"
