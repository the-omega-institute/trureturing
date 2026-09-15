#!/usr/bin/env bash
set -euo pipefail
PRODUCER="" LAKE_BIN="" CANDIDATE_ROOT="" CANDIDATE_OUTPUT=""
while [[ $# -gt 0 ]]; do
  [[ $# -ge 2 && -n "$2" ]] || { echo "lean-report-pair: $1 requires a value" >&2; exit 2; }
  case "$1" in
    --producer) PRODUCER="$2" ;;
    --lake-bin) LAKE_BIN="$2" ;;
    --candidate-root) CANDIDATE_ROOT="$2" ;;
    --candidate-output) CANDIDATE_OUTPUT="$2" ;;
    *) echo "lean-report-pair: unknown argument '$1'" >&2; exit 2 ;;
  esac
  shift 2
done
[[ "$PRODUCER" == /* && -x "$PRODUCER" && "$LAKE_BIN" == /* && -x "$LAKE_BIN" \
   && -d "$CANDIDATE_ROOT" && "$CANDIDATE_OUTPUT" == /* ]] \
  || { echo 'lean-report-pair: absolute producer/Lake/output and existing candidate root are required' >&2; exit 2; }
# The current default workflow calls this candidate-only interface. Production,
# validation, supervision, and publication all belong to the Inspector entry.
exec env LAKE_BIN="$LAKE_BIN" "$PRODUCER" --repository "$CANDIDATE_ROOT" --output "$CANDIDATE_OUTPUT"
