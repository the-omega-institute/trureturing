#!/usr/bin/env bash
set -euo pipefail

ROLE=""
REPORT=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --role) ROLE="$2"; shift 2 ;;
    --report) REPORT="$2"; shift 2 ;;
    --) shift; break ;;
    *) echo "report-consumer: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ -n "$ROLE" ]] || { echo "report-consumer: --role is required" >&2; exit 2; }
[[ -s "$REPORT" ]] || {
  echo "report-consumer: raw Lean report is missing at $REPORT; run make lean-report first" >&2
  exit 2
}
[[ $# -gt 0 ]] || { echo "report-consumer: command is required after --" >&2; exit 2; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
SUPERVISOR="$ROOT/Meta/StrataLint/scripts/report-supervisor.sh"
set +e
"$SUPERVISOR" --role "$ROLE" -- "$@"
rc=$?
set -e
if [[ "$rc" -ne 0 ]]; then
  echo "report-consumer: consumption failed; the raw Lean report may be stale, run make lean-report first" >&2
fi
exit "$rc"
