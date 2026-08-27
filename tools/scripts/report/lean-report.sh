#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
INSPECTOR="$ROOT/tools/lean-inspector/inspect.sh"
PAIR="$ROOT/tools/scripts/lean-report-pair.sh"
REPORT="$ROOT/.lake/build/stratalint/raw-lean-report.json"
LAKE_BIN="${LAKE_BIN:-$(command -v lake || true)}"

[[ -n "$LAKE_BIN" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" ]] \
  || { echo "lean-report.sh: an absolute lake executable is required" >&2; exit 2; }

# Local opt-in: warm the same host/UID-scoped, content-addressed report
# cache that local-harness-gate exports (identical default path), so a repeat run of
# an unchanged tree restores the canonical report instead of re-running the Lean
# producer under the serialized global slot. Never enabled in CI (which leaves the
# env unset), so CI report production stays byte-for-byte unchanged; the pair helper
# ignores the env when unset and fail-closes on any cache root it does not own.
if [[ "${CI:-}" != "true" && "${CI:-}" != "1" ]]; then
  export STRATALINT_REPORT_CACHE_ROOT="${STRATALINT_REPORT_CACHE_ROOT:-${XDG_CACHE_HOME:-$HOME/.cache}/stratalint-lean-report-cache}"
fi

exec "$PAIR" \
  --producer "$INSPECTOR" \
  --lake-bin "$LAKE_BIN" \
  --candidate-root "$ROOT" \
  --candidate-output "$REPORT"
