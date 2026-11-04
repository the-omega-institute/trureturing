#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

COMMAND="${1:-}"
if [[ -n "$COMMAND" ]]; then shift; fi
# The repository (R) and pair provenance (A) are different canonical preimages.
# Keep their byte definitions here for producers and bundle transport alike.
input_coordinates() {
  local selection
  selection="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/lean-report-selection.py"
  python3 -B "$selection" coordinates "$@"
}
if [[ "$COMMAND" == "coordinates" ]]; then
  input_coordinates "$@"
  exit $?
fi
REPOSITORY=""
REPORT=""
TARGETS=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository|--report|--targets)
      [[ $# -ge 2 && -n "$2" ]] || { echo "lean-report-input: $1 requires a value" >&2; exit 2; }
      case "$1" in --repository) REPOSITORY="$2" ;; --report) REPORT="$2" ;; --targets) TARGETS="$2" ;; esac
      shift 2 ;;
    *) echo "lean-report-input: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ "$COMMAND" == "address" || "$COMMAND" == "verify" || "$COMMAND" == "modules" \
  || "$COMMAND" == "producer-paths" || "$COMMAND" == "scribe-producer-paths" || "$COMMAND" == "verify-scoped" ]] \
  || { echo "usage: lean-report-input.sh address|verify|modules|producer-paths|scribe-producer-paths|verify-scoped --repository DIR [--report FILE] [--targets ROOTS]" >&2; exit 2; }
[[ -n "$REPOSITORY" && "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
  || { echo "lean-report-input: --repository requires an absolute directory" >&2; exit 2; }
REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
if [[ "$COMMAND" == "verify-scoped" ]]; then
  [[ "$REPORT" == /* && "$TARGETS" =~ [^[:space:]] ]] \
    || { echo 'lean-report-input: verify-scoped requires an absolute --report and nonempty --targets' >&2; exit 2; }
  SCRIPT_DIRECTORY="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
  exec python3 -B "$SCRIPT_DIRECTORY/../../lean-inspector/scoped.py" verify \
    --repository "$REPOSITORY" --report "$REPORT" --targets "$TARGETS"
fi
if [[ "$COMMAND" == "verify" ]]; then
  [[ -n "$REPORT" && "$REPORT" == /* && -s "$REPORT" ]] \
    || { echo "lean-report-input: raw Lean report is missing; run make lean-report first" >&2; exit 2; }
fi

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-report-input.XXXXXXXX")"
cleanup() { rm -rf -- "$TMP_ROOT"; }
trap cleanup EXIT

SCRIPT_DIRECTORY="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
source "$SCRIPT_DIRECTORY/../worktree/lean-cache-input.sh"

# The registered policy is validated before any command exposes inputs.
SELECTION="$SCRIPT_DIRECTORY/lean-report-selection.py"
[[ -r "$SELECTION" ]] || { echo "lean-report-input: selection loader is absent: $SELECTION" >&2; exit 2; }
case "$COMMAND" in
  modules|producer-paths|scribe-producer-paths)
    python3 "$SELECTION" "$COMMAND" --repository "$REPOSITORY"
    exit $?
    ;;
esac
repository_address() {
  python3 -B "$SELECTION" address --repository "$REPOSITORY"
}

verify_report_sha() {
  local declared="" declared_name="" actual
  [[ -f "${REPORT}.sha256" ]] \
    || { echo "lean-report-input: report SHA is missing; run make lean-report first" >&2; return 2; }
  read -r declared declared_name < "${REPORT}.sha256" || true
  actual="$(hash_file "$REPORT")"
  [[ "$declared" =~ ^[0-9a-f]{64}$ \
    && "$declared" == "$actual" \
    && "$declared_name" == "$(basename "$REPORT")" \
    && "$(awk 'END {print NR}' "${REPORT}.sha256")" == "1" ]] \
    || { echo "lean-report-input: raw Lean report SHA is stale; run make lean-report first" >&2; return 2; }
  REPORT_SHA256="$actual"
}

case "$COMMAND" in
  address)
    repository_address
    ;;
  verify)
    python3 -B "$SELECTION" validate --repository "$REPOSITORY" || exit 2
    verify_report_sha
    [[ -f "${REPORT}.input.attestation" ]] \
      || { echo "lean-report-input: production input attestation is missing; run make lean-report first" >&2; exit 2; }
    schema=""
    declared=""
    producer=""
    attested_report=""
    extra=""
    {
      IFS= read -r schema || true
      IFS= read -r declared || true
      IFS= read -r producer || true
      IFS= read -r attested_report || true
      IFS= read -r extra || true
    } < "${REPORT}.input.attestation"
    [[ "$schema" == "schema=stratalint-lean-report-input-attestation-v1" ]] \
      || { echo "lean-report-input: production input attestation is malformed or stale; run make lean-report first" >&2; exit 2; }
    [[ "$declared" =~ ^repository_input_sha256=[0-9a-f]{64}$ \
      && "$producer" =~ ^producer_sha256=[0-9a-f]{64}$ \
      && "$attested_report" == "report_sha256=$REPORT_SHA256" \
      && -z "$extra" ]] \
      || { echo "lean-report-input: production input attestation is malformed or stale; run make lean-report first" >&2; exit 2; }
    declared="${declared#repository_input_sha256=}"
    producer="${producer#producer_sha256=}"
    address_output="$(repository_address)" || exit 2
    # Validate the complete tuple before read can collapse an empty field.
    address_pattern='^([0-9a-f]{64} ){3}[0-9a-f]{64}$'
    [[ "$address_output" =~ $address_pattern ]] \
      || { echo "lean-report-input: repository address is malformed" >&2; exit 2; }
    IFS=' ' read -r address current_producer current_sources current_config <<< "$address_output"
    [[ "$producer" == "$current_producer" ]] \
      || { echo "lean-report-input: raw Lean report producer is stale for current repository inputs; run make lean-report first" >&2; exit 2; }
    [[ "$declared" == "$address" ]] \
      || { echo "lean-report-input: raw Lean report is stale for current repository inputs; run make lean-report first" >&2; exit 2; }
    python3 -B "$SCRIPT_DIRECTORY/../../lean-inspector/publication.py" verify-inputs "$REPORT" --repository "$REPOSITORY"
    ;;
esac
