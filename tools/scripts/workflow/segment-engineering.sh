#!/usr/bin/env bash
set -uo pipefail

schema_version=pfci-segment-evidence-v1
segment=engineering
event="${EVENT-}"
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
selected = string_array(values[13], None)
ordered = string_array(values[14], [])
evidence = {
    "schema_version": values[0],
    "segment": values[1],
    "event": values[2],
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
    "selected_test_ids": selected,
    "ordered_check_ids": ordered,
}
sys.stdout.write(json.dumps(evidence, ensure_ascii=True, separators=(",", ":")) + "\n")
'
}

emit_evidence() {
  local command_status="$?"
  local evidence_line=
  local evidence_status=0
  trap - EXIT
  if [[ "$raw_rc" -eq 0 && "$command_status" -ne 0 ]]; then
    raw_rc=2
    outcome=subprocess-infrastructure-failed
  fi
  if [[ -n "$temporary_directory" && -d "$temporary_directory" ]]; then
    rm -rf -- "$temporary_directory"
  fi

  if declare -F segment_evidence_emit >/dev/null; then
    evidence_line="$(segment_evidence_emit \
      "$schema_version" "$segment" "$event" "$merge_commit" "$tree" "$base" \
      "$source_head" "$raw_rc" "$outcome" "$report_input_address" \
      "$report_sha256" "$judge_source_address" "$scribe_source_address" \
      "$selected_test_ids_json" "$ordered_check_ids_json")" || evidence_status=$?
  else
    evidence_status=2
  fi
  if [[ "$evidence_status" -ne 0 || -z "$evidence_line" || "$evidence_line" == *$'\n'* ]]; then
    raw_rc=2
    if [[ "$outcome" != evidence-library-unavailable ]]; then
      outcome=evidence-encoding-failed
    fi
    evidence_line="$(bootstrap_segment_evidence_emit \
      "$schema_version" "$segment" "$event" "$merge_commit" "$tree" "$base" \
      "$source_head" "$raw_rc" "$outcome" "$report_input_address" \
      "$report_sha256" "$judge_source_address" "$scribe_source_address" \
      "$selected_test_ids_json" "$ordered_check_ids_json")" || evidence_line=
  fi
  if [[ -z "$evidence_line" || "$evidence_line" == *$'\n'* ]]; then
    evidence_line='{"schema_version":"pfci-segment-evidence-v1","segment":"engineering","event":null,"merge_commit":null,"tree":null,"base":null,"source_head":null,"raw_rc":2,"outcome":"evidence-encoding-failed","report_input_address":null,"report_sha256":null,"judge_source_address":null,"scribe_source_address":null,"selected_test_ids":null,"ordered_check_ids":[]}'
    raw_rc=2
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
    printf 'SEGMENT_ENGINEERING_EVIDENCE_FAILED operation=record-check check=%s exit=2\n' "$1" >&2
    finish 2 evidence-encoding-failed
  fi
  ordered_check_ids_json="$updated_checks"
}

evidence_library="${BASH_SOURCE[0]%/*}/../lib/segment-evidence-lib.sh"
if [[ ! -f "$evidence_library" ]]; then
  printf 'SEGMENT_ENGINEERING_INPUT_FAILED field=evidence-library path=%s reason=not-regular\n' \
    "$evidence_library" >&2
  outcome=evidence-library-unavailable
  exit 2
fi
if ! source "$evidence_library"; then
  printf 'SEGMENT_ENGINEERING_INPUT_FAILED field=evidence-library path=%s reason=source-failed\n' \
    "$evidence_library" >&2
  outcome=evidence-library-unavailable
  exit 2
fi
if ! declare -F segment_evidence_emit >/dev/null \
  || ! declare -F segment_evidence_array_append >/dev/null; then
  printf 'SEGMENT_ENGINEERING_INPUT_FAILED field=evidence-library path=%s reason=entrypoint-missing\n' \
    "$evidence_library" >&2
  outcome=evidence-library-unavailable
  exit 2
fi

repository_input="${REPOSITORY-}"
if [[ -z "$repository_input" ]]; then
  printf '%s\n' 'SEGMENT_ENGINEERING_INPUT_FAILED field=REPOSITORY reason=missing' >&2
  finish 2 missing-required-input
fi
if [[ -z "$event" ]]; then
  printf '%s\n' 'SEGMENT_ENGINEERING_INPUT_FAILED field=EVENT reason=missing' >&2
  finish 2 missing-required-input
fi
if [[ "$event" != PR && "$event" != push ]]; then
  printf 'SEGMENT_ENGINEERING_INPUT_FAILED field=EVENT value=%q reason=invalid\n' "$event" >&2
  finish 2 invalid-event
fi
if ! repository="$(cd "$repository_input" 2>/dev/null && pwd -P)"; then
  printf 'SEGMENT_ENGINEERING_INPUT_FAILED field=REPOSITORY path=%s reason=unavailable\n' \
    "$repository_input" >&2
  finish 2 invalid-path
fi
if ! git -C "$repository" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
  printf 'SEGMENT_ENGINEERING_INPUT_FAILED field=REPOSITORY path=%s reason=not-git-work-tree\n' \
    "$repository" >&2
  finish 2 invalid-path
fi

required_inputs=(
  tools/tests/CompileFailProof/CompileFailProof.csproj
  tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj
  tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs
  tools/StrataLint.sln
  tools/scripts/dotnet-build.sh
  tools/scripts/engineering-tests.sh
  tools/scripts/stratalint-selftest.sh
  tools/scripts/workflow/engineering-test-execution-harness.sh
)
for required_input in "${required_inputs[@]}"; do
  if [[ ! -f "$repository/$required_input" ]]; then
    printf 'SEGMENT_ENGINEERING_INPUT_FAILED field=required-input path=%s reason=not-regular\n' \
      "$repository/$required_input" >&2
    finish 2 missing-required-input
  fi
done

temporary_directory="$(mktemp -d "${TMPDIR:-/tmp}/segment-engineering.XXXXXX")" ||
  finish 2 subprocess-infrastructure-failed
parents_log="$temporary_directory/parents.log"
parents_status=0
parents_line="$(git -C "$repository" rev-list --parents -n 1 HEAD 2>"$parents_log")" || parents_status=$?
if [[ "$parents_status" -ne 0 ]]; then
  cat "$parents_log" >&2
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=resolve-parents exit=%s\n' \
    "$parents_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
cat "$parents_log" >&2
read -r -a parent_parts <<< "$parents_line"
if [[ "${#parent_parts[@]}" -lt 1 || ! "${parent_parts[0]}" =~ ^[0-9a-f]{40}$ ]]; then
  finish 2 subprocess-infrastructure-failed
fi
merge_commit="${parent_parts[0]}"
tree_status=0
tree_value="$(git -C "$repository" rev-parse 'HEAD^{tree}' 2>"$parents_log")" || tree_status=$?
if [[ "$tree_status" -ne 0 ]]; then
  cat "$parents_log" >&2
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=resolve-tree exit=%s\n' \
    "$tree_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
cat "$parents_log" >&2
if [[ ! "$tree_value" =~ ^[0-9a-f]{40}$ ]]; then
  finish 2 subprocess-infrastructure-failed
fi
tree="$tree_value"
parent_count=$((${#parent_parts[@]} - 1))
if [[ "$parent_count" -ge 1 ]]; then
  base="${parent_parts[1]}"
fi
if [[ "$event" == PR && "$parent_count" -ne 2 ]]; then
  printf 'SEGMENT_ENGINEERING_IDENTITY_FAILED event=PR parent-count=%s\n' "$parent_count" >&2
  finish 2 parent-mismatch
fi
if [[ "$parent_count" -eq 2 ]]; then
  source_head="${parent_parts[2]}"
fi

record_check restore-compile-fail-proofs
restore_status=0
dotnet restore "$repository/tools/tests/CompileFailProof/CompileFailProof.csproj" --locked-mode >&2 || restore_status=$?
if [[ "$restore_status" -ne 0 ]]; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=restore-compile-fail-proof exit=%s\n' \
    "$restore_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
restore_status=0
dotnet restore "$repository/tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj" --locked-mode >&2 || restore_status=$?
if [[ "$restore_status" -ne 0 ]]; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=restore-banned-api-proof exit=%s\n' \
    "$restore_status" >&2
  finish 2 subprocess-infrastructure-failed
fi

record_check restore-engineering-solution
restore_status=0
dotnet restore "$repository/tools/StrataLint.sln" --locked-mode >&2 || restore_status=$?
if [[ "$restore_status" -ne 0 ]]; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=restore-engineering-solution exit=%s\n' \
    "$restore_status" >&2
  finish 2 subprocess-infrastructure-failed
fi

record_check build-candidate
build_status=0
/bin/bash "$repository/tools/scripts/dotnet-build.sh" >&2 || build_status=$?
if [[ "$build_status" -ne 0 ]]; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=build-candidate exit=%s\n' \
    "$build_status" >&2
  finish 2 subprocess-infrastructure-failed
fi

record_check engineering-tests
engineering_log="$temporary_directory/engineering-tests.log"
engineering_status=0
/bin/bash "$repository/tools/scripts/workflow/engineering-test-execution-harness.sh" \
  "$repository" >"$engineering_log" 2>&1 || engineering_status=$?
cat "$engineering_log" >&2
identity_json_candidate="$temporary_directory/selected-test-ids.json"
identity_state_file="$temporary_directory/selected-test-ids.state"
identity_parse_status=0
python3 - "$engineering_log" "$identity_json_candidate" "$identity_state_file" <<'PY' || identity_parse_status=$?
import json
import re
import sys

prefix = "TEST_EVIDENCE_IDENTITIES selected_test_ids="
identities = set()
identity_seen = False
plans = []
with open(sys.argv[1], "r", encoding="utf-8") as stream:
    for raw_line in stream:
        line = raw_line.rstrip("\n")
        if line.startswith("ENGINEERING_TEST_PLAN "):
            match = re.search(r"(?:^| )state=(full|selected|none)(?: |$).*(?:^| )selected=([0-9]+)(?: |$)", line)
            if match is None:
                raise ValueError("engineering test plan record is malformed")
            plans.append((match.group(1), int(match.group(2))))
        if not line.startswith(prefix):
            continue
        identity_seen = True
        values = json.loads(line[len(prefix):])
        if not isinstance(values, list) or any(not isinstance(value, str) for value in values):
            raise ValueError("executed test identity evidence is not a string array")
        identities.update(values)
ordered = sorted(identities, key=lambda value: value.encode("utf-8"))
if identity_seen:
    if any(selected > 0 for _, selected in plans) and not ordered:
        raise ValueError("selected engineering tests produced no executed identities")
    with open(sys.argv[2], "w", encoding="utf-8", newline="") as output:
        output.write(json.dumps(ordered, ensure_ascii=True, separators=(",", ":")))
    state = "identity"
elif plans and all(kind == "none" and selected == 0 for kind, selected in plans):
    state = "none"
else:
    state = "missing"
with open(sys.argv[3], "w", encoding="ascii", newline="") as output:
    output.write(state)
PY
if [[ "$identity_parse_status" -ne 0 ]]; then
  printf 'SEGMENT_ENGINEERING_EVIDENCE_FAILED operation=parse-identities exit=%s\n' \
    "$identity_parse_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
identity_state="$(<"$identity_state_file")"
if [[ "$identity_state" == identity ]]; then
  selected_candidate="$(<"$identity_json_candidate")"
  if [[ -z "$selected_candidate" ]]; then
    printf '%s\n' 'SEGMENT_ENGINEERING_EVIDENCE_FAILED operation=commit-identities exit=2' >&2
    finish 2 subprocess-infrastructure-failed
  fi
  selected_test_ids_json="$selected_candidate"
elif [[ "$identity_state" != none ]]; then
  printf 'SEGMENT_ENGINEERING_EVIDENCE_FAILED operation=require-identities engineering-exit=%s\n' \
    "$engineering_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
if [[ "$engineering_status" -eq 1 ]]; then
  finish 1 candidate-check-failed
elif [[ "$engineering_status" -ne 0 ]]; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=engineering-tests exit=%s\n' \
    "$engineering_status" >&2
  finish 2 subprocess-infrastructure-failed
fi

record_check stratalint-selftest
selftest_status=0
/bin/bash "$repository/tools/scripts/stratalint-selftest.sh" >&2 || selftest_status=$?
if [[ "$selftest_status" -eq 1 ]]; then
  finish 1 candidate-check-failed
elif [[ "$selftest_status" -ne 0 ]]; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=stratalint-selftest exit=%s\n' \
    "$selftest_status" >&2
  finish 2 subprocess-infrastructure-failed
fi

proof_log_has_infrastructure_failure() {
  grep -Eq '(^|[[:space:]:])(MSB[0-9]{4}|NETSDK[0-9]{4}|NU[0-9]{4})(:|[[:space:]])' "$1"
}

record_check compile-fail-proof
compile_fail_log="$temporary_directory/compile-fail-proof.log"
compile_fail_status=0
dotnet build "$repository/tools/tests/CompileFailProof/CompileFailProof.csproj" \
  --no-restore --configuration Release >"$compile_fail_log" 2>&1 || compile_fail_status=$?
cat "$compile_fail_log" >&2
if [[ "$compile_fail_status" -gt 1 ]]; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=compile-fail-proof exit=%s\n' \
    "$compile_fail_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
if [[ "$compile_fail_status" -ne 0 ]] \
  && proof_log_has_infrastructure_failure "$compile_fail_log"; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=compile-fail-proof exit=%s\n' \
    "$compile_fail_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
if [[ "$compile_fail_status" -eq 0 ]] \
  || ! grep -Fq 'CS7036' "$compile_fail_log" \
  || ! grep -Fq 'MetaClear' "$compile_fail_log"; then
  finish 1 candidate-check-failed
fi

record_check banned-api-compile-fail-proof
banned_api_log="$temporary_directory/banned-api-compile-fail-proof.log"
banned_api_status=0
dotnet build "$repository/tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj" \
  --no-restore --configuration Release >"$banned_api_log" 2>&1 || banned_api_status=$?
cat "$banned_api_log" >&2
if [[ "$banned_api_status" -gt 1 ]]; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=banned-api-compile-fail-proof exit=%s\n' \
    "$banned_api_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
if [[ "$banned_api_status" -ne 0 ]] \
  && proof_log_has_infrastructure_failure "$banned_api_log"; then
  printf 'SEGMENT_ENGINEERING_SUBPROCESS_FAILED check=banned-api-compile-fail-proof exit=%s\n' \
    "$banned_api_status" >&2
  finish 2 subprocess-infrastructure-failed
fi
if [[ "$banned_api_status" -eq 0 ]]; then
  finish 1 candidate-check-failed
fi

expected_lines=()
while IFS= read -r line; do
  [[ -n "$line" ]] && expected_lines+=("$line")
done < <(grep -nF '// banned-api-proof' \
  "$repository/tools/tests/BannedApiCompileFailProof/BannedApiViolations.cs" | cut -d: -f1)
actual_lines=()
while IFS= read -r line; do
  [[ -n "$line" ]] && actual_lines+=("$line")
done < <(sed -n 's#.*BannedApiViolations.cs(\([0-9][0-9]*\),[0-9][0-9]*): error RS0030:.*#\1#p' \
  "$banned_api_log" | sort -nu)

if [[ "${#expected_lines[@]}" -eq 0 \
  || "${#actual_lines[@]}" -ne "${#expected_lines[@]}" ]]; then
  finish 1 candidate-check-failed
fi
if grep -F ': error ' "$banned_api_log" | grep -vFq ': error RS0030:'; then
  finish 1 candidate-check-failed
fi
for ((index = 0; index < ${#expected_lines[@]}; index += 1)); do
  if [[ "${actual_lines[$index]}" != "${expected_lines[$index]}" ]]; then
    finish 1 candidate-check-failed
  fi
done

# Schema name retained from A22: selected_test_ids carries executed TRX identities.
# The terminology correction remains open at the specification boundary.
finish 0 passed
