#!/usr/bin/env bash
set -euo pipefail

ROLE=""
REPORT=""
SOURCE_INPUTS=()
if [[ -n "${BASE+x}" ]]; then SOURCE_INPUTS=(--base "$BASE"); fi
while [[ $# -gt 0 ]]; do
  case "$1" in
    --role) ROLE="$2"; shift 2 ;;
    --report) REPORT="$2"; shift 2 ;;
    --base|--push-before|--push-head)
      [[ $# -ge 2 ]] || { echo "report-consumer: $1 requires a value" >&2; exit 2; }
      SOURCE_INPUTS+=("$1" "$2"); shift 2 ;;
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
SUPERVISOR="$ROOT/tools/scripts/report/report-supervisor.sh"
INPUT_VERIFIER="$ROOT/tools/scripts/report/lean-report-input.sh"
SOURCE_ARGS=()
source_arguments="$(python3 "$ROOT/tools/scripts/workflow/checked-ci-identity.py" \
  --repository "$ROOT" --report-source-arguments --acquire-pinned \
  ${SOURCE_INPUTS[@]+"${SOURCE_INPUTS[@]}"})" || exit 2
while IFS= read -r argument; do SOURCE_ARGS+=("$argument"); done <<< "$source_arguments"
SNAPSHOT_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-report-consumer.XXXXXXXX")"
cleanup() { rm -rf -- "$SNAPSHOT_ROOT"; }
trap cleanup EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM

SNAPSHOT_REPORT="$SNAPSHOT_ROOT/$(basename "$REPORT")"
for suffix in '' .sha256 .input.attestation .provenance.json .materials.zip; do
  [[ -f "${REPORT}${suffix}" ]] || {
    echo "report-consumer: raw Lean report bundle is incomplete at ${REPORT}${suffix}; run make lean-report first" >&2
    exit 2
  }
  cp "${REPORT}${suffix}" "${SNAPSHOT_REPORT}${suffix}"
done
if [[ -f "${REPORT}.source-context.json" ]]; then
  cp "${REPORT}.source-context.json" "${SNAPSHOT_REPORT}.source-context.json"
fi
"$INPUT_VERIFIER" verify --repository "$ROOT" --report "$SNAPSHOT_REPORT" "${SOURCE_ARGS[@]}"
# The verifier and the consumer receive the same immutable request identity.
export STRATALINT_SOURCE_BASE="" STRATALINT_PUSH_BEFORE="" STRATALINT_PUSH_HEAD=""
if [[ "${SOURCE_ARGS[0]}" == --base ]]; then
  export STRATALINT_SOURCE_BASE="${SOURCE_ARGS[1]}"
else
  export STRATALINT_PUSH_BEFORE="${SOURCE_ARGS[1]}" STRATALINT_PUSH_HEAD="${SOURCE_ARGS[3]}"
fi
set +e
"$SUPERVISOR" --role "$ROLE" -- env STRATALINT_LEAN_REPORT="$SNAPSHOT_REPORT" "$@"
rc=$?
set -e
exit "$rc"
