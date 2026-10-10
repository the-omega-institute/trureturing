#!/usr/bin/env bash
set -euo pipefail

ROLE=""
REPORT=""
TARGETS=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --role) ROLE="$2"; shift 2 ;;
    --report) REPORT="$2"; shift 2 ;;
    --targets)
      [[ $# -ge 2 && -n "$2" ]] || { echo 'report-consumer: --targets must be nonempty' >&2; exit 2; }
      TARGETS="$2"; shift 2 ;;
    --) shift; break ;;
    *) echo "report-consumer: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

REPAIR='run make lean-report first'
if [[ -n "$TARGETS" ]]; then
  REPAIR="run make lean-report-scoped LEAN_TARGETS=\"$TARGETS\" LEAN_REPORT=\"$REPORT\" first"
fi

[[ -n "$ROLE" ]] || { echo "report-consumer: --role is required" >&2; exit 2; }
[[ -s "$REPORT" ]] || {
  echo "report-consumer: raw Lean report is missing at $REPORT; $REPAIR" >&2
  exit 2
}
[[ $# -gt 0 ]] || { echo "report-consumer: command is required after --" >&2; exit 2; }

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)"
SUPERVISOR="$ROOT/tools/scripts/report/report-supervisor.sh"
INPUT_VERIFIER="$ROOT/tools/scripts/report/lean-report-input.sh"
SNAPSHOT_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-report-consumer.XXXXXXXX")"
cleanup() { rm -rf -- "$SNAPSHOT_ROOT"; }
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

SNAPSHOT_REPORT="$SNAPSHOT_ROOT/$(basename "$REPORT")"
for suffix in '' .sha256 .input.attestation .provenance.json .materials.zip; do
  [[ -f "${REPORT}${suffix}" ]] || {
    echo "report-consumer: raw Lean report bundle is incomplete at ${REPORT}${suffix}; $REPAIR" >&2
    exit 2
  }
  cp "${REPORT}${suffix}" "${SNAPSHOT_REPORT}${suffix}"
done
if [[ -n "$TARGETS" ]]; then
  "$INPUT_VERIFIER" verify-scoped --repository "$ROOT" --report "$SNAPSHOT_REPORT" --targets "$TARGETS"
else
  "$INPUT_VERIFIER" verify --repository "$ROOT" --report "$SNAPSHOT_REPORT"
fi
set +e
"$SUPERVISOR" --role "$ROLE" -- env STRATALINT_LEAN_REPORT="$SNAPSHOT_REPORT" "$@"
rc=$?
set -e
exit "$rc"
