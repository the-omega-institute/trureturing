#!/usr/bin/env bash
set -uo pipefail

schema_version=pfci-segment-evidence-v1
segment=admission
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
    encoded='{"schema_version":"pfci-segment-evidence-v1","segment":"admission","event":null,"merge_commit":null,"tree":null,"base":null,"source_head":null,"raw_rc":2,"outcome":"subprocess-infrastructure-failed","report_input_address":null,"report_sha256":null,"judge_source_address":null,"scribe_source_address":null,"selected_test_ids":null,"ordered_check_ids":[]}'
  fi
  evidence_line="$encoded"
}

emit_evidence() {
  local command_status="$?"
  local evidence_line=
  local process_rc
  trap - EXIT
  if [[ "$raw_rc" -eq 0 && "$command_status" -ne 0 ]]; then
    raw_rc=2
    outcome=subprocess-infrastructure-failed
  fi
  if [[ -n "$temporary_directory" && -d "$temporary_directory" ]]; then
    rm -rf -- "$temporary_directory"
  fi
  encode_evidence_line
  printf '%s\n' "$evidence_line"
  process_rc="$raw_rc"
  if [[ "$raw_rc" -eq 3 ]]; then
    process_rc=0
  fi
  exit "$process_rc"
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
    printf 'SEGMENT_ADMISSION_EVIDENCE_FAILED operation=record-check check=%s exit=2\n' \
      "$1" >&2
    finish 2 subprocess-infrastructure-failed
  fi
  ordered_check_ids_json="$updated_checks"
}

evidence_library="${BASH_SOURCE[0]%/*}/../lib/segment-evidence-lib.sh"
if [[ ! -f "$evidence_library" ]]; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=evidence-library path=%s reason=not-regular\n' \
    "$evidence_library" >&2
  outcome=subprocess-infrastructure-failed
  exit 2
fi
if ! source "$evidence_library"; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=evidence-library path=%s reason=source-failed\n' \
    "$evidence_library" >&2
  outcome=subprocess-infrastructure-failed
  exit 2
fi
if ! declare -F segment_evidence_emit >/dev/null \
  || ! declare -F segment_evidence_array_append >/dev/null; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=evidence-library path=%s reason=entrypoint-missing\n' \
    "$evidence_library" >&2
  outcome=subprocess-infrastructure-failed
  exit 2
fi

repository_input="${REPOSITORY-}"
report_input="${REPORT-}"
lean_evidence_input="${LEAN_INSPECT_EVIDENCE-}"
judge_dll_input="${JUDGE_DLL-}"
expected_judge_address="${JUDGE_SOURCE_ADDRESS-}"
test_map_cache_input="${TEST_MAP_CACHE_ROOT-}"

for required_name in REPOSITORY EVENT REPORT LEAN_INSPECT_EVIDENCE JUDGE_SOURCE_ADDRESS; do
  case "$required_name" in
    REPOSITORY) required_value="$repository_input" ;;
    EVENT) required_value="$event_input" ;;
    REPORT) required_value="$report_input" ;;
    LEAN_INSPECT_EVIDENCE) required_value="$lean_evidence_input" ;;
    JUDGE_SOURCE_ADDRESS) required_value="$expected_judge_address" ;;
  esac
  if [[ -z "$required_value" ]]; then
    printf 'SEGMENT_ADMISSION_INPUT_FAILED field=%s reason=missing\n' "$required_name" >&2
    finish 2 missing-required-input
  fi
done
if [[ "$event_input" != PR && "$event_input" != push ]]; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=EVENT value=%q reason=invalid\n' \
    "$event_input" >&2
  finish 2 missing-required-input
fi
event="$event_input"
if ! repository="$(cd "$repository_input" 2>/dev/null && pwd -P)"; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=REPOSITORY path=%s reason=unavailable\n' \
    "$repository_input" >&2
  finish 2 invalid-path
fi
if ! git -C "$repository" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=REPOSITORY path=%s reason=not-git-work-tree\n' \
    "$repository" >&2
  finish 2 invalid-path
fi
case "$report_input" in
  /*) ;;
  *) printf 'SEGMENT_ADMISSION_INPUT_FAILED field=REPORT reason=not-absolute\n' >&2; finish 2 invalid-path ;;
esac
case "$lean_evidence_input" in
  /*) ;;
  *) printf 'SEGMENT_ADMISSION_INPUT_FAILED field=LEAN_INSPECT_EVIDENCE reason=not-absolute\n' >&2; finish 2 invalid-path ;;
esac
report_parent_input="$(dirname "$report_input")"
if ! report_parent="$(cd "$report_parent_input" 2>/dev/null && pwd -P)"; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=REPORT path=%s reason=parent-unavailable\n' \
    "$report_input" >&2
  finish 2 invalid-path
fi
report="$report_parent/$(basename "$report_input")"
evidence_parent_input="$(dirname "$lean_evidence_input")"
if ! evidence_parent="$(cd "$evidence_parent_input" 2>/dev/null && pwd -P)"; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=LEAN_INSPECT_EVIDENCE path=%s reason=parent-unavailable\n' \
    "$lean_evidence_input" >&2
  finish 2 invalid-path
fi
lean_evidence="$evidence_parent/$(basename "$lean_evidence_input")"
if [[ "$lean_evidence" != "$report_parent/lean-inspect-segment-evidence.json" ]]; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=LEAN_INSPECT_EVIDENCE path=%s reason=noncanonical\n' \
    "$lean_evidence" >&2
  finish 2 invalid-path
fi
if [[ -n "$test_map_cache_input" && "$test_map_cache_input" != /* ]]; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=TEST_MAP_CACHE_ROOT path=%s reason=not-absolute\n' \
    "$test_map_cache_input" >&2
  finish 2 invalid-path
fi

input_helper="$repository/tools/scripts/report/lean-report-input.sh"
bundle_validator="$repository/tools/scripts/report/lean-report-bundle-lib.sh"
gate="$repository/.github/scripts/harness-gate.sh"
if [[ ! -f "$input_helper" ]]; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=required-input path=%s reason=not-regular\n' \
    "$input_helper" >&2
  finish 2 missing-required-input
fi
if [[ ! -f "$bundle_validator" || ! -r "$bundle_validator" ]]; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=bundle-validator path=%s reason=not-readable\n' \
    "$bundle_validator" >&2
  finish 2 missing-required-input
fi
# shellcheck source=/dev/null
if ! source "$bundle_validator" \
  || ! declare -F lean_report_bundle_validate >/dev/null; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=bundle-validator path=%s reason=source-failed\n' \
    "$bundle_validator" >&2
  finish 2 subprocess-infrastructure-failed
fi
if [[ ! -x "$gate" ]]; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=required-input path=%s reason=not-executable\n' \
    "$gate" >&2
  finish 2 missing-required-input
fi
if ! grep -qF -- '--candidate-lean-report' "$gate"; then
  printf '%s\n' 'SEGMENT_ADMISSION_INPUT_FAILED field=harness-gate reason=report-interface-missing' >&2
  finish 2 missing-required-input
fi
if [[ -n "$test_map_cache_input" ]] \
  && ! grep -qF -- '--test-map-cache-root' "$gate"; then
  printf '%s\n' 'SEGMENT_ADMISSION_INPUT_FAILED field=harness-gate reason=test-map-interface-missing' >&2
  finish 2 missing-required-input
fi

temporary_directory="$(mktemp -d "${TMPDIR:-/tmp}/segment-admission.XXXXXX")" ||
  finish 2 subprocess-infrastructure-failed
parents_log="$temporary_directory/parents.log"
parents_status=0
parents_line="$(git -C "$repository" rev-list --parents -n 1 HEAD 2>"$parents_log")" || parents_status=$?
cat "$parents_log" >&2
if [[ "$parents_status" -ne 0 ]]; then
  printf 'SEGMENT_ADMISSION_SUBPROCESS_FAILED check=resolve-parents exit=%s\n' \
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
  printf 'SEGMENT_ADMISSION_IDENTITY_FAILED event=%s parent-count=%s\n' \
    "$event" "$parent_count" >&2
  finish 2 parent-mismatch
fi
base="${parent_parts[1]}"
if [[ "$event" == PR && "$parent_count" -ne 2 ]]; then
  printf 'SEGMENT_ADMISSION_IDENTITY_FAILED event=PR parent-count=%s\n' "$parent_count" >&2
  finish 2 parent-mismatch
fi
if [[ "$parent_count" -eq 2 ]]; then
  source_head="${parent_parts[2]}"
fi

if [[ ! -s "$report" ]]; then
  printf 'SEGMENT_ADMISSION_INPUT_FAILED field=REPORT path=%s reason=missing\n' "$report" >&2
  finish 2 missing-required-input
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
  printf 'SEGMENT_ADMISSION_ADDRESS_FAILED kind=lean-report exit=%s\n' "$address_status" >&2
  finish 2 lean-report-address-verification-failed
fi
canonical_address_status=0
canonical_address="$(lean_report_bundle_validate \
  "$report" "$address_value" "$producer_value" "$producer_value" \
  "$sources_value" "$config_value")" || canonical_address_status=$?
if [[ "$canonical_address_status" -ne 0 || ! "$canonical_address" =~ ^[0-9a-f]{64}$ ]]; then
  printf 'SEGMENT_ADMISSION_ADDRESS_FAILED kind=canonical-lean-report exit=%s\n' \
    "$canonical_address_status" >&2
  finish 2 lean-report-address-verification-failed
fi
report_input_address="sha256:$canonical_address"
report_hash_status=0
actual_report_sha="$(sha256sum "$report" | awk '{print $1}')" || report_hash_status=$?
if [[ "$report_hash_status" -ne 0 || ! "$actual_report_sha" =~ ^[0-9a-f]{64}$ ]]; then
  finish 2 lean-report-address-verification-failed
fi
report_sha256="$actual_report_sha"

record_check verify-lean-inspect-evidence
if [[ ! -s "$lean_evidence" ]]; then
  printf 'SEGMENT_ADMISSION_EVIDENCE_FAILED reason=missing path=%s\n' "$lean_evidence" >&2
  finish 2 report-evidence-mismatch
fi
evidence_state="$temporary_directory/lean-evidence.state"
evidence_status=0
python3 - \
  "$lean_evidence" "$report" "$report_input_address" "$report_sha256" \
  "$event" "$merge_commit" "$tree" "$base" "$source_head" "$evidence_state" <<'PY' || evidence_status=$?
import json
import pathlib
import re
import sys

(
    evidence_path,
    report_path,
    report_input_address,
    report_sha256,
    event,
    merge_commit,
    tree,
    base,
    source_head,
    state_path,
) = sys.argv[1:]
keys = [
    "schema_version", "segment", "event", "merge_commit", "tree", "base",
    "source_head", "raw_rc", "outcome", "report_input_address", "report_sha256",
    "judge_source_address", "scribe_source_address", "selected_test_ids",
    "ordered_check_ids",
]
try:
    data = pathlib.Path(evidence_path).read_bytes()
    value = json.loads(data.decode("utf-8", errors="strict"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"SEGMENT_ADMISSION_EVIDENCE_FAILED reason=parse detail={error}", file=sys.stderr)
    raise SystemExit(2)
canonical = (json.dumps(value, ensure_ascii=True, separators=(",", ":")) + "\n").encode("ascii")
expected_source_head = None if source_head == "null" else source_head
expected_sidecar = f"{report_sha256}  {pathlib.Path(report_path).name}\n".encode("ascii")
try:
    sidecar = pathlib.Path(report_path + ".sha256").read_bytes()
except OSError as error:
    print(f"SEGMENT_ADMISSION_EVIDENCE_FAILED reason=report-sidecar detail={error}", file=sys.stderr)
    raise SystemExit(2)
valid = (
    isinstance(value, dict)
    and list(value) == keys
    and data == canonical
    and value["schema_version"] == "pfci-segment-evidence-v1"
    and value["segment"] == "lean-inspect"
    and value["event"] == event
    and value["merge_commit"] == merge_commit
    and value["tree"] == tree
    and value["base"] == base
    and value["source_head"] == expected_source_head
    and type(value["raw_rc"]) is int
    and value["raw_rc"] == 0
    and value["outcome"] == "passed"
    and value["report_input_address"] == report_input_address
    and value["report_sha256"] == report_sha256
    and value["judge_source_address"] is None
    and isinstance(value["scribe_source_address"], str)
    and re.fullmatch(r"[0-9a-f]{64}", value["scribe_source_address"]) is not None
    and value["selected_test_ids"] is None
    and value["ordered_check_ids"]
        == ["produce-canonical-lean-report", "scribe-content-checks"]
    and sidecar == expected_sidecar
)
if not valid:
    print("SEGMENT_ADMISSION_EVIDENCE_FAILED reason=mismatch", file=sys.stderr)
    raise SystemExit(2)
pathlib.Path(state_path).write_bytes(value["scribe_source_address"].encode("ascii"))
PY
if [[ "$evidence_status" -ne 0 || ! -s "$evidence_state" ]]; then
  finish 2 report-evidence-mismatch
fi
scribe_source_address="$(<"$evidence_state")"

if [[ ! "$expected_judge_address" =~ ^[0-9a-f]{64}$ ]]; then
  printf 'SEGMENT_ADMISSION_ADDRESS_FAILED kind=judge reason=invalid-expected-address\n' >&2
  finish 2 judge-address-verification-failed
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

effective_judge_dll=
if [[ -n "$judge_dll_input" ]]; then
  if [[ "$judge_dll_input" != /* ]]; then
    printf 'SEGMENT_ADMISSION_INPUT_FAILED field=JUDGE_DLL path=%s reason=not-absolute\n' \
      "$judge_dll_input" >&2
    finish 2 invalid-path
  fi
  if [[ ! -s "$judge_dll_input" ]]; then
    printf 'SEGMENT_ADMISSION_INPUT_FAILED field=JUDGE_DLL path=%s reason=missing\n' \
      "$judge_dll_input" >&2
    finish 2 missing-required-input
  fi
  attestation_status=0
  verify_binary_attestation "$judge_dll_input" "$expected_judge_address" || attestation_status=$?
  case "$attestation_status" in
    0) effective_judge_dll="$judge_dll_input" ;;
    1)
      printf 'SEGMENT_ADMISSION_CACHE_MISS kind=judge reason=source-address-mismatch\n' >&2
      ;;
    *)
      printf 'SEGMENT_ADMISSION_ADDRESS_FAILED kind=judge reason=malformed-attestation path=%s\n' \
        "$judge_dll_input.source-address" >&2
      finish 2 judge-address-verification-failed
      ;;
  esac
fi
judge_source_address="$expected_judge_address"

test_map_cache_root=
if [[ -n "$test_map_cache_input" ]]; then
  if ! mkdir -p -- "$test_map_cache_input" \
    || ! test_map_cache_root="$(cd "$test_map_cache_input" 2>/dev/null && pwd -P)"; then
    printf 'SEGMENT_ADMISSION_INPUT_FAILED field=TEST_MAP_CACHE_ROOT path=%s reason=unavailable\n' \
      "$test_map_cache_input" >&2
    finish 2 invalid-path
  fi
fi

gate_args=(
  --candidate "$repository"
  --base "$base"
  --candidate-lean-report "$report"
)
if [[ -n "$test_map_cache_root" ]]; then
  gate_args+=(--test-map-cache-root "$test_map_cache_root")
fi
if [[ -n "$effective_judge_dll" ]]; then
  gate_args+=(--judge-dll "$effective_judge_dll")
fi
record_check harness-gate
gate_status=0
"$gate" "${gate_args[@]}" >&2 || gate_status=$?
case "$gate_status" in
  0) finish 0 passed ;;
  1) finish 1 candidate-check-failed ;;
  2) finish 2 subprocess-infrastructure-failed ;;
  3) finish 3 protected-surface-change ;;
  *)
    printf 'SEGMENT_ADMISSION_SUBPROCESS_FAILED check=harness-gate exit=%s\n' \
      "$gate_status" >&2
    finish 2 subprocess-infrastructure-failed
    ;;
esac
