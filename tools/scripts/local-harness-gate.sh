#!/bin/bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd -P)"
CANDIDATE_ROOT="$ROOT"
arguments=()
while [[ $# -gt 0 ]]; do
  case "$1" in
    --candidate) [[ $# -ge 2 ]] || exit 2; CANDIDATE_ROOT="$2"; shift 2 ;;
    --base|--purpose) [[ $# -ge 2 ]] || exit 2; arguments+=("$1" "$2"); shift 2 ;;
    --plan) arguments+=("$1"); shift ;;
    *) echo "local-harness-gate: unknown argument $1" >&2; exit 2 ;;
  esac
done
cd "$CANDIDATE_ROOT"
exec python3 tools/scripts/workflow/ci_checks.py local "${arguments[@]}"
