#!/usr/bin/env bash
set -uo pipefail

schema_version=pfci-segment-evidence-v1
segment=lean-inspect
event=null
event_input="${EVENT-}"
merge_commit=null
tree=null
base=null
source_head=null
raw_rc=2
outcome=missing-required-input
report_input_address=null
report_sha256=null
judge_source_address=null
scribe_source_address=null
selected_test_ids_json=null
ordered_check_ids_json='[]'
temporary_directory=
evidence_output=

bootstrap_segment_evidence_emit() {
  if [[ "$#" -ne 15 ]]; then
    return 2
  fi
  printf '%s\0' "$@" | python3 -c '
import json
import sys

payload = sys.stdin.buffer.read().split(b"\0")
if not payload or payload[-1] != b"" or len(payload) != 16:
    raise ValueError("bootstrap evidence requires exactly 15 fields")
values = [value.decode("utf-8", errors="strict") for value in payload[:-1]]

def nullable(value):
    return None if value == "null" else value

def string_array(value, fallback):
    if value == "null":
        return None
    try:
        decoded = json.loads(value)
        if not isinstance(decoded, list) or any(not isinstance(item, str) for item in decoded):
            raise ValueError()
        return decoded
    except Exception:
        return fallback

try:
    raw_rc = int(values[7])
except ValueError:
    raw_rc = 2
evidence = {
    "schema_version": values[0],
    "segment": values[1],
    "event": nullable(values[2]),
    "merge_commit": nullable(values[3]),
    "tree": nullable(values[4]),
    "base": nullable(values[5]),
    "source_head": nullable(values[6]),
    "raw_rc": raw_rc,
    "outcome": values[8],
    "report_input_address": nullable(values[9]),
    "report_sha256": nullable(values[10]),
    "judge_source_address": nullable(values[11]),
    "scribe_source_address": nullable(values[12]),
    "selected_test_ids": string_array(values[13], None),
    "ordered_check_ids": string_array(values[14], []),
}
sys.stdout.write(json.dumps(evidence, ensure_ascii=True, separators=(",", ":")) + "\n")
'
}

encode_evidence_line() {
  local encoded=
  local encode_status=0
  if declare -F segment_evidence_emit >/dev/null; then
    encoded="$(segment_evidence_emit \
      "$schema_version" "$segment" "$event" "$merge_commit" "$tree" "$base" \
      "$source_head" "$raw_rc" "$outcome" "$report_input_address" \
      "$report_sha256" "$judge_source_address" "$scribe_source_address" \
      "$selected_test_ids_json" "$ordered_check_ids_json")" || encode_status=$?
  else
    encode_status=2
  fi
  if [[ "$encode_status" -ne 0 || -z "$encoded" || "$encoded" == *$'\n'* ]]; then
    raw_rc=2
    outcome=subprocess-infrastructure-failed
    encoded="$(bootstrap_segment_evidence_emit \
      "$schema_version" "$segment" "$event" "$merge_commit" "$tree" "$base" \
      "$source_head" "$raw_rc" "$outcome" "$report_input_address" \
      "$report_sha256" "$judge_source_address" "$scribe_source_address" \
      "$selected_test_ids_json" "$ordered_check_ids_json")" || encoded=
  fi
  if [[ -z "$encoded" || "$encoded" == *$'\n'* ]]; then
    raw_rc=2
    outcome=subprocess-infrastructure-failed
    encoded='{"schema_version":"pfci-segment-evidence-v1","segment":"lean-inspect","event":null,"merge_commit":null,"tree":null,"base":null,"source_head":null,"raw_rc":2,"outcome":"subprocess-infrastructure-failed","report_input_address":null,"report_sha256":null,"judge_source_address":null,"scribe_source_address":null,"selected_test_ids":null,"ordered_check_ids":[]}'
  fi
  evidence_line="$encoded"
}

emit_evidence() {
  local command_status="$?"
  local evidence_line=
  local evidence_tmp=
  trap - EXIT
  if [[ "$raw_rc" -eq 0 && "$command_status" -ne 0 ]]; then
    raw_rc=2
    outcome=subprocess-infrastructure-failed
  fi
  if [[ -n "$temporary_directory" && -d "$temporary_directory" ]]; then
    rm -rf -- "$temporary_directory"
  fi

  encode_evidence_line
  if [[ -n "$evidence_output" ]]; then
    evidence_tmp="$(dirname "$evidence_output")/.$(basename "$evidence_output").tmp.$$"
    if ! printf '%s\n' "$evidence_line" > "$evidence_tmp" \
      || ! mv -f -- "$evidence_tmp" "$evidence_output"; then
      rm -f -- "$evidence_tmp"
      printf 'SEGMENT_LEAN_INSPECT_EVIDENCE_FAILED operation=publish path=%s exit=2\n' \
        "$evidence_output" >&2
      raw_rc=2
      outcome=subprocess-infrastructure-failed
      encode_evidence_line
    fi
  fi
  printf '%s\n' "$evidence_line"
  exit "$raw_rc"
}
trap emit_evidence EXIT

finish() {
  raw_rc="$1"
  outcome="$2"
  exit "$raw_rc"
}

record_check() {
  local updated_checks
  if ! updated_checks="$(segment_evidence_array_append "$ordered_check_ids_json" "$1")"; then
    printf 'SEGMENT_LEAN_INSPECT_EVIDENCE_FAILED operation=record-check check=%s exit=2\n' \
      "$1" >&2
    finish 2 subprocess-infrastructure-failed
  fi
  ordered_check_ids_json="$updated_checks"
}

evidence_library="${BASH_SOURCE[0]%/*}/../lib/segment-evidence-lib.sh"
if [[ ! -f "$evidence_library" ]]; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=evidence-library path=%s reason=not-regular\n' \
    "$evidence_library" >&2
  outcome=subprocess-infrastructure-failed
  exit 2
fi
if ! source "$evidence_library"; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=evidence-library path=%s reason=source-failed\n' \
    "$evidence_library" >&2
  outcome=subprocess-infrastructure-failed
  exit 2
fi
if ! declare -F segment_evidence_emit >/dev/null \
  || ! declare -F segment_evidence_array_append >/dev/null; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=evidence-library path=%s reason=entrypoint-missing\n' \
    "$evidence_library" >&2
  outcome=subprocess-infrastructure-failed
  exit 2
fi

if [[ -z "$event_input" ]]; then
  printf '%s\n' 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=EVENT reason=missing' >&2
  finish 2 missing-required-input
fi
if [[ "$event_input" != PR && "$event_input" != push ]]; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=EVENT value=%q reason=invalid\n' \
    "$event_input" >&2
  finish 2 missing-required-input
fi
event="$event_input"

repository_input="${REPOSITORY-}"
report_input="${REPORT-}"
evidence_input="${LEAN_INSPECT_EVIDENCE-}"
scribe_dll_input="${SCRIBE_DLL-}"
expected_scribe_address="${SCRIBE_SOURCE_ADDRESS-}"
report_cache_bundle="${REPORT_CACHE_BUNDLE-}"
report_cache_root="${REPORT_CACHE_ROOT-}"

for required_name in REPOSITORY REPORT LEAN_INSPECT_EVIDENCE SCRIBE_SOURCE_ADDRESS; do
  case "$required_name" in
    REPOSITORY) required_value="$repository_input" ;;
    REPORT) required_value="$report_input" ;;
    LEAN_INSPECT_EVIDENCE) required_value="$evidence_input" ;;
    SCRIBE_SOURCE_ADDRESS) required_value="$expected_scribe_address" ;;
  esac
  if [[ -z "$required_value" ]]; then
    printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=%s reason=missing\n' "$required_name" >&2
    finish 2 missing-required-input
  fi
done
if [[ ! "$expected_scribe_address" =~ ^[0-9a-f]{64}$ ]]; then
  printf 'SEGMENT_LEAN_INSPECT_ADDRESS_FAILED kind=scribe reason=invalid-expected-address\n' >&2
  finish 2 scribe-address-verification-failed
fi
if ! repository="$(cd "$repository_input" 2>/dev/null && pwd -P)"; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=REPOSITORY path=%s reason=unavailable\n' \
    "$repository_input" >&2
  finish 2 invalid-path
fi
if ! git -C "$repository" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=REPOSITORY path=%s reason=not-git-work-tree\n' \
    "$repository" >&2
  finish 2 invalid-path
fi
case "$report_input" in
  /*) ;;
  *) printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=REPORT reason=not-absolute\n' >&2; finish 2 invalid-path ;;
esac
case "$evidence_input" in
  /*) ;;
  *) printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=LEAN_INSPECT_EVIDENCE reason=not-absolute\n' >&2; finish 2 invalid-path ;;
esac
report_parent_input="$(dirname "$report_input")"
if ! mkdir -p -- "$report_parent_input" \
  || ! report_parent="$(cd "$report_parent_input" 2>/dev/null && pwd -P)"; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=REPORT path=%s reason=parent-unavailable\n' \
    "$report_input" >&2
  finish 2 invalid-path
fi
report="$report_parent/$(basename "$report_input")"
evidence_parent_input="$(dirname "$evidence_input")"
if ! evidence_parent="$(cd "$evidence_parent_input" 2>/dev/null && pwd -P)"; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=LEAN_INSPECT_EVIDENCE path=%s reason=parent-unavailable\n' \
    "$evidence_input" >&2
  finish 2 invalid-path
fi
evidence_output="$evidence_parent/$(basename "$evidence_input")"
if [[ "$evidence_output" != "$report_parent/lean-inspect-segment-evidence.json" ]]; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=LEAN_INSPECT_EVIDENCE path=%s reason=noncanonical\n' \
    "$evidence_output" >&2
  finish 2 invalid-path
fi
for optional_path in "$report_cache_bundle" "$report_cache_root"; do
  if [[ -n "$optional_path" && "$optional_path" != /* ]]; then
    printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=report-cache path=%s reason=not-absolute\n' \
      "$optional_path" >&2
    finish 2 invalid-path
  fi
done

required_inputs=(
  tools/scripts/report/lean-report-bundle-lib.sh
  tools/scripts/report/lean-report-input.sh
  tools/scripts/report/lean-report-ci-baseline.sh
  tools/scripts/lean-report-pair.sh
  tools/lean-inspector/inspect.sh
  tools/lean-inspector/Inspector.lean
  tools/scripts/workflow/scribe-content-checks.sh
)
for required_input in "${required_inputs[@]}"; do
  if [[ ! -f "$repository/$required_input" ]]; then
    printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=required-input path=%s reason=not-regular\n' \
      "$repository/$required_input" >&2
    finish 2 missing-required-input
  fi
done

temporary_directory="$(mktemp -d "${TMPDIR:-/tmp}/segment-lean-inspect.XXXXXX")" ||
  finish 2 subprocess-infrastructure-failed
parents_log="$temporary_directory/parents.log"
parents_status=0
parents_line="$(git -C "$repository" rev-list --parents -n 1 HEAD 2>"$parents_log")" || parents_status=$?
cat "$parents_log" >&2
if [[ "$parents_status" -ne 0 ]]; then
  printf 'SEGMENT_LEAN_INSPECT_SUBPROCESS_FAILED check=resolve-parents exit=%s\n' \
    "$parents_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
read -r -a parent_parts <<< "$parents_line"
if [[ "${#parent_parts[@]}" -lt 1 || ! "${parent_parts[0]}" =~ ^[0-9a-f]{40}$ ]]; then
  finish 2 subprocess-infrastructure-failed
fi
merge_commit="${parent_parts[0]}"
tree_status=0
tree_value="$(git -C "$repository" rev-parse 'HEAD^{tree}' 2>"$parents_log")" || tree_status=$?
cat "$parents_log" >&2
if [[ "$tree_status" -ne 0 || ! "$tree_value" =~ ^[0-9a-f]{40}$ ]]; then
  finish 2 subprocess-infrastructure-failed
fi
tree="$tree_value"
parent_count=$((${#parent_parts[@]} - 1))
if [[ "$parent_count" -lt 1 ]]; then
  printf 'SEGMENT_LEAN_INSPECT_IDENTITY_FAILED event=%s parent-count=%s\n' \
    "$event" "$parent_count" >&2
  finish 2 parent-mismatch
fi
base="${parent_parts[1]}"
if [[ "$event" == PR && "$parent_count" -ne 2 ]]; then
  printf 'SEGMENT_LEAN_INSPECT_IDENTITY_FAILED event=PR parent-count=%s\n' "$parent_count" >&2
  finish 2 parent-mismatch
fi
if [[ "$parent_count" -eq 2 ]]; then
  source_head="${parent_parts[2]}"
fi

verify_binary_attestation() {
  python3 - "$1" "$2" <<'PY'
import pathlib
import re
import sys

path = pathlib.Path(sys.argv[1] + ".source-address")
expected = sys.argv[2]
try:
    data = path.read_bytes()
except OSError:
    raise SystemExit(2)
match = re.fullmatch(
    rb"schema=stratalint-dotnet-binary-source-address-v1\n"
    rb"source_address=([0-9a-f]{64})\n",
    data,
)
if match is None:
    raise SystemExit(2)
raise SystemExit(0 if match.group(1).decode("ascii") == expected else 1)
PY
}

effective_scribe_dll=
if [[ -n "$scribe_dll_input" ]]; then
  if [[ "$scribe_dll_input" != /* ]]; then
    printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=SCRIBE_DLL path=%s reason=not-absolute\n' \
      "$scribe_dll_input" >&2
    finish 2 invalid-path
  fi
  if [[ ! -s "$scribe_dll_input" ]]; then
    printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=SCRIBE_DLL path=%s reason=missing\n' \
      "$scribe_dll_input" >&2
    finish 2 missing-required-input
  fi
  attestation_status=0
  verify_binary_attestation "$scribe_dll_input" "$expected_scribe_address" || attestation_status=$?
  case "$attestation_status" in
    0) effective_scribe_dll="$scribe_dll_input" ;;
    1)
      printf 'SEGMENT_LEAN_INSPECT_CACHE_MISS kind=scribe reason=source-address-mismatch\n' >&2
      ;;
    *)
      printf 'SEGMENT_LEAN_INSPECT_ADDRESS_FAILED kind=scribe reason=malformed-attestation path=%s\n' \
        "$scribe_dll_input.source-address" >&2
      finish 2 scribe-address-verification-failed
      ;;
  esac
fi

input_helper="$repository/tools/scripts/report/lean-report-input.sh"
bundle_validator="$repository/tools/scripts/report/lean-report-bundle-lib.sh"
# shellcheck source=/dev/null
if ! source "$bundle_validator" \
  || ! declare -F lean_report_bundle_validate >/dev/null; then
  printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=bundle-validator path=%s reason=source-failed\n' \
    "$bundle_validator" >&2
  finish 2 subprocess-infrastructure-failed
fi
address_log="$temporary_directory/report-address.log"
address_status=0
address_output="$("$input_helper" address --repository "$repository" 2>"$address_log")" || address_status=$?
cat "$address_log" >&2
read -r address_value producer_value sources_value config_value extra_value <<< "$address_output"
if [[ "$address_status" -ne 0 \
  || ! "$address_value" =~ ^[0-9a-f]{64}$ \
  || ! "$producer_value" =~ ^[0-9a-f]{64}$ \
  || ! "$sources_value" =~ ^[0-9a-f]{64}$ \
  || ! "$config_value" =~ ^[0-9a-f]{64}$ \
  || -n "${extra_value-}" ]]; then
  printf 'SEGMENT_LEAN_INSPECT_ADDRESS_FAILED kind=lean-report exit=%s\n' "$address_status" >&2
  finish 2 lean-report-address-verification-failed
fi
report_bundle_is_valid() {
  local candidate="$1"
  lean_report_bundle_validate \
    "$candidate" "$address_value" "$producer_value" "$producer_value" \
    "$sources_value" "$config_value" >/dev/null
}

clear_report_output() {
  local suffix
  for suffix in '' .sha256 .input.attestation .provenance.json .materials.zip; do
    rm -f -- "${report}${suffix}"
  done
  rm -rf -- "${report}.logs"
}

copy_report_bundle() {
  local source="$1"
  local suffix
  clear_report_output
  for suffix in '' .input.attestation .provenance.json .materials.zip; do
    cp -- "${source}${suffix}" "${report}${suffix}" || return 1
  done
  local copied_sha
  copied_sha="$(sha256sum "$report" | awk '{print $1}')" || return 1
  [[ "$copied_sha" =~ ^[0-9a-f]{64}$ ]] || return 1
  printf '%s  %s\n' "$copied_sha" "$(basename "$report")" > "${report}.sha256" || return 1
  if [[ -d "${source}.logs" ]]; then
    cp -R -- "${source}.logs" "${report}.logs" || return 1
  fi
  report_bundle_is_valid "$report"
}

report_ready=0
if report_bundle_is_valid "$report"; then
  report_ready=1
  printf 'SEGMENT_LEAN_INSPECT_REPORT source=existing status=reused\n' >&2
else
  clear_report_output
fi
if [[ "$report_ready" -eq 0 && -n "$report_cache_bundle" ]] \
  && report_bundle_is_valid "$report_cache_bundle"; then
  if copy_report_bundle "$report_cache_bundle"; then
    report_ready=1
    printf 'SEGMENT_LEAN_INSPECT_REPORT source=cache status=reused\n' >&2
  else
    clear_report_output
  fi
fi

if [[ "$report_ready" -eq 0 ]]; then
  lake_bin="${LAKE_BIN-${HOME-}/.elan/bin/lake}"
  if [[ -z "$lake_bin" ]]; then
    printf '%s\n' 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=LAKE_BIN reason=missing' >&2
    finish 2 missing-required-input
  fi
  if [[ "$lake_bin" != /* || ! -x "$lake_bin" ]]; then
    printf 'SEGMENT_LEAN_INSPECT_INPUT_FAILED field=LAKE_BIN path=%s reason=invalid\n' \
      "$lake_bin" >&2
    finish 2 invalid-path
  fi
  if [[ -n "$report_cache_bundle" && -n "$report_cache_root" ]]; then
    baseline_log="$temporary_directory/report-baseline.log"
    baseline_status=0
    delta_cache_root="$("$repository/tools/scripts/report/lean-report-ci-baseline.sh" \
      --bundle "$report_cache_bundle" --cache-root "$report_cache_root" \
      2>"$baseline_log")" || baseline_status=$?
    cat "$baseline_log" >&2
    if [[ "$baseline_status" -eq 0 && "$delta_cache_root" == /* ]]; then
      export STRATALINT_REPORT_CACHE_ROOT="$delta_cache_root"
    else
      printf 'SEGMENT_LEAN_INSPECT_REPORT_CACHE status=unavailable exit=%s\n' \
        "$baseline_status" >&2
      unset STRATALINT_REPORT_CACHE_ROOT
    fi
  fi
  producer="$repository/tools/lean-inspector/inspect.sh"
  pair_producer="$repository/tools/scripts/lean-report-pair.sh"
  production_status=0
  "$pair_producer" \
    --producer "$producer" \
    --lake-bin "$lake_bin" \
    --candidate-root "$repository" \
    --candidate-output "$report" >&2 || production_status=$?
  if [[ "$production_status" -ne 0 ]]; then
    printf 'SEGMENT_LEAN_INSPECT_SUBPROCESS_FAILED check=produce-canonical-lean-report exit=%s\n' \
      "$production_status" >&2
    finish 2 subprocess-infrastructure-failed
  fi
  if ! report_bundle_is_valid "$report"; then
    printf '%s\n' 'SEGMENT_LEAN_INSPECT_SUBPROCESS_FAILED check=verify-produced-report exit=2' >&2
    finish 2 subprocess-infrastructure-failed
  fi
fi

canonical_address_status=0
canonical_address="$(lean_report_bundle_validate \
  "$report" "$address_value" "$producer_value" "$producer_value" \
  "$sources_value" "$config_value")" || canonical_address_status=$?
if [[ "$canonical_address_status" -ne 0 || ! "$canonical_address" =~ ^[0-9a-f]{64}$ ]]; then
  printf 'SEGMENT_LEAN_INSPECT_ADDRESS_FAILED kind=canonical-lean-report exit=%s\n' \
    "$canonical_address_status" >&2
  finish 2 lean-report-address-verification-failed
fi
report_input_address="sha256:$canonical_address"

report_hash_status=0
report_hash="$(sha256sum "$report" | awk '{print $1}')" || report_hash_status=$?
if [[ "$report_hash_status" -ne 0 || ! "$report_hash" =~ ^[0-9a-f]{64}$ ]]; then
  finish 2 lean-report-address-verification-failed
fi
report_sha256="$report_hash"
record_check produce-canonical-lean-report

scribe_source_address="$expected_scribe_address"
record_check scribe-content-checks
scribe_status=0
/bin/bash "$repository/tools/scripts/workflow/scribe-content-checks.sh" \
  "$report" "$effective_scribe_dll" "$base" >&2 || scribe_status=$?
if [[ "$scribe_status" -eq 1 ]]; then
  finish 1 candidate-check-failed
elif [[ "$scribe_status" -ne 0 ]]; then
  printf 'SEGMENT_LEAN_INSPECT_SUBPROCESS_FAILED check=scribe-content-checks exit=%s\n' \
    "$scribe_status" >&2
  finish 2 subprocess-infrastructure-failed
fi

finish 0 passed
