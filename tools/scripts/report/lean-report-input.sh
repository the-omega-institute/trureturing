#!/usr/bin/env bash
set -euo pipefail

export LC_ALL=C

COMMAND="${1:-}"
if [[ -n "$COMMAND" ]]; then shift; fi
# The repository (R) and pair provenance (A) are different canonical preimages.
# Keep their byte definitions here for producers and bundle transport alike.
input_coordinates() {
  python3 - "$@" <<'PY'
import hashlib
import re
import sys

fields = sys.argv[1:]
if len(fields) != 4 or any(not re.fullmatch(r"[0-9a-f]{64}", v) for v in fields):
    raise SystemExit("lean-report-input: coordinates require producer, resident, sources, config SHA-256")
producer, resident, sources, config = fields
common = (f"repository_inspector_sha256={resident}\n"
          f"lean_sources_sha256={sources}\nlean_config_sha256={config}\n")
pair = "schema=stratalint-lean-report-input-v1\n" + f"producer_sha256={producer}\n" + common
repository = "schema=stratalint-lean-report-repository-input-v1\n" + common
print(hashlib.sha256(pair.encode("ascii")).hexdigest(),
      hashlib.sha256(repository.encode("ascii")).hexdigest())
PY
}
if [[ "$COMMAND" == "coordinates" ]]; then
  input_coordinates "$@"
  exit $?
fi
REPOSITORY=""
REPORT=""
PRODUCER_OVERRIDE=""
INSPECTOR_OVERRIDE=""
while [[ $# -gt 0 ]]; do
  case "$1" in
    --repository) REPOSITORY="$2"; shift 2 ;;
    --report) REPORT="$2"; shift 2 ;;
    --producer) PRODUCER_OVERRIDE="$2"; shift 2 ;;
    --inspector) INSPECTOR_OVERRIDE="$2"; shift 2 ;;
    *) echo "lean-report-input: unknown argument '$1'" >&2; exit 2 ;;
  esac
done

[[ "$COMMAND" == "address" || "$COMMAND" == "verify" || "$COMMAND" == "modules" \
  || "$COMMAND" == "producer-paths" || "$COMMAND" == "scribe-producer-paths" ]] \
  || { echo "usage: lean-report-input.sh address|verify|modules|producer-paths|scribe-producer-paths --repository DIR [--report FILE] [--producer FILE] [--inspector FILE]" >&2; exit 2; }
[[ -n "$REPOSITORY" && "$REPOSITORY" == /* && -d "$REPOSITORY" ]] \
  || { echo "lean-report-input: --repository requires an absolute directory" >&2; exit 2; }
[[ -z "$PRODUCER_OVERRIDE" || ( "$PRODUCER_OVERRIDE" == /* && -f "$PRODUCER_OVERRIDE" ) ]] \
  || { echo "lean-report-input: --producer requires an absolute file" >&2; exit 2; }
[[ -z "$INSPECTOR_OVERRIDE" || ( "$INSPECTOR_OVERRIDE" == /* && -f "$INSPECTOR_OVERRIDE" ) ]] \
  || { echo "lean-report-input: --inspector requires an absolute file" >&2; exit 2; }
REPOSITORY="$(cd "$REPOSITORY" && pwd -P)"
if [[ "$COMMAND" == "verify" ]]; then
  [[ -n "$REPORT" && "$REPORT" == /* && -s "$REPORT" ]] \
    || { echo "lean-report-input: raw Lean report is missing; run make lean-report first" >&2; exit 2; }
fi

TMP_ROOT="$(mktemp -d "${TMPDIR:-/tmp}/stratalint-report-input.XXXXXXXX")"
cleanup() { rm -rf -- "$TMP_ROOT"; }
trap cleanup EXIT

SCRIPT_DIRECTORY="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
source "$SCRIPT_DIRECTORY/../worktree/lean-cache-input.sh"

append_producer_manifest_entry() {
  local manifest="$1"
  local relative="$2"
  local path="$REPOSITORY/$relative"
  if [[ "$relative" == "lean-report-inputs.json" ]]; then
    path="$TMP_ROOT/selection-policy.json"
  elif [[ "$relative" == "tools/lean-inspector/inspect.sh" && -n "$PRODUCER_OVERRIDE" ]]; then
    path="$PRODUCER_OVERRIDE"
  elif [[ "$relative" == "tools/lean-inspector/Inspector.lean" && -n "$INSPECTOR_OVERRIDE" ]]; then
    path="$INSPECTOR_OVERRIDE"
  fi
  [[ -f "$path" ]] \
    || { echo "lean-report-input: repository input is absent: $path" >&2; return 2; }
  printf '%s\0%s\0' "$relative" "$path" >> "${manifest}.requests"
}

# The registered policy is validated before any command exposes inputs.
SELECTION="$SCRIPT_DIRECTORY/lean-report-selection.py"
[[ -r "$SELECTION" ]] || { echo "lean-report-input: selection loader is absent: $SELECTION" >&2; exit 2; }
case "$COMMAND" in
  modules|producer-paths|scribe-producer-paths)
    python3 "$SELECTION" "$COMMAND" --repository "$REPOSITORY"
    exit $?
    ;;
esac
python3 "$SELECTION" snapshot --repository "$REPOSITORY" --output "$TMP_ROOT" || exit 2

producer_sha256() {
  local manifest="$1"
  local relative
  : > "$manifest"
  : > "${manifest}.unsorted"
  : > "${manifest}.unsorted.requests"
  local producer_paths="$TMP_ROOT/producer-paths"
  while IFS= read -r relative; do
    append_producer_manifest_entry "${manifest}.unsorted" "$relative" || return 2
  done < "$producer_paths"
  materialize_manifest "${manifest}.unsorted" || return 2
  sort "${manifest}.unsorted" > "$manifest" || return 2
  rm -f -- "${manifest}.unsorted"
  hash_file "$manifest"
}

registered_input_hash() {
  local kind="$1" relative
  local manifest="$TMP_ROOT/$kind.manifest"
  : > "${manifest}.requests"
  while IFS= read -r relative; do
    append_manifest_entry "$manifest" "$relative" || return 2
  done < "$TMP_ROOT/$kind-paths"
  materialize_manifest "$manifest" || return 2
  hash_file "$manifest"
}

# Repository address preimage v1 hashes the resident inspector producer,
# Trureturing.lean + D5/**/*.lean + tools/lean-inspector/**/*.lean sources,
# and the Lean toolchain/lake configuration as three named SHA-256 fields.
repository_address() {
  local resident_manifest="$TMP_ROOT/resident-inspector.manifest"
  local resident_sha256 sources_sha256 config_sha256

  prepare_memo
  resident_sha256="$(producer_sha256 "$resident_manifest")" || return 2
  sources_sha256="$(registered_input_hash sources)" || return 2
  config_sha256="$(registered_input_hash config)" || return 2

  local coordinates address_sha256
  coordinates="$(input_coordinates "$resident_sha256" "$resident_sha256" "$sources_sha256" "$config_sha256")" || return 2
  address_sha256="${coordinates#* }"
  store_memo_updates
  printf '%s %s %s %s\n' \
    "$address_sha256" "$resident_sha256" "$sources_sha256" "$config_sha256"
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
    ;;
esac
