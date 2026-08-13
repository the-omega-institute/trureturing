#!/usr/bin/env bash
set -euo pipefail

ROLE=""
REPORT=""

report_bundle_suffixes() {
  printf '%s\n' '' .sha256 .input.attestation .provenance.json
}

if [[ "${1:-}" == "--bundle-suffixes" ]]; then
  report_bundle_suffixes
  exit 0
fi

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

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd -P)"
SUPERVISOR="$ROOT/Meta/StrataLint/scripts/report/report-supervisor.sh"
INPUT_VERIFIER="$ROOT/Meta/StrataLint/scripts/report/lean-report-input.sh"
SNAPSHOT_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-report-consumer.XXXXXXXX")"
cleanup() { rm -rf -- "$SNAPSHOT_ROOT"; }
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

SNAPSHOT_REPORT="$SNAPSHOT_ROOT/$(basename "$REPORT")"
while IFS= read -r suffix; do
  [[ -f "${REPORT}${suffix}" ]] || {
    echo "report-consumer: raw Lean report bundle is incomplete at ${REPORT}${suffix}; run make lean-report first" >&2
    exit 2
  }
  cp "${REPORT}${suffix}" "${SNAPSHOT_REPORT}${suffix}"
done < <(report_bundle_suffixes)
"$INPUT_VERIFIER" verify --repository "$ROOT" --report "$SNAPSHOT_REPORT"
set +e
"$SUPERVISOR" --role "$ROLE" -- env STRATALINT_LEAN_REPORT="$SNAPSHOT_REPORT" "$@"
rc=$?
set -e
if [[ "$rc" -ne 0 ]]; then
  echo "report-consumer: consumption failed; the raw Lean report may be stale, run make lean-report first" >&2
fi
exit "$rc"
