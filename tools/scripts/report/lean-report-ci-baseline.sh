#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIRECTORY="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
# Optional staging: stdout names a ready cache root (or normalized bundle).
# The caller must require that output before treating this as a successful stage.
if ! python3 "$SCRIPT_DIRECTORY/lean-report-cache.py" stage "$@"; then
  printf 'LEAN_REPORT_CI_BASELINE status=fallback reason=invalid-or-unavailable-bundle\n' >&2
fi
