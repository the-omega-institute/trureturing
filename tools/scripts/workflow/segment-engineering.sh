#!/usr/bin/env bash
set -uo pipefail

source "${BASH_SOURCE[0]%/*}/../lib/segment-evidence-lib.sh"

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

emit_evidence() {
  local command_status="$?"
  trap - EXIT
  if [[ "$raw_rc" -eq 0 && "$command_status" -ne 0 ]]; then
    raw_rc=2
    outcome=subprocess-infrastructure-failed
  fi
  if [[ -n "$temporary_directory" && -d "$temporary_directory" ]]; then
    rm -rf -- "$temporary_directory"
  fi
  segment_evidence_emit \
    "$schema_version" "$segment" "$event" "$merge_commit" "$tree" "$base" \
    "$source_head" "$raw_rc" "$outcome" "$report_input_address" \
    "$report_sha256" "$judge_source_address" "$scribe_source_address" \
    "$selected_test_ids_json" "$ordered_check_ids_json" || exit 2
  exit "$raw_rc"
}
trap emit_evidence EXIT

finish() {
  raw_rc="$1"
  outcome="$2"
  exit "$raw_rc"
}

record_check() {
  ordered_check_ids_json="$(python3 - "$ordered_check_ids_json" "$1" <<'PY'
import json
import sys
values = json.loads(sys.argv[1])
values.append(sys.argv[2])
sys.stdout.write(json.dumps(values, ensure_ascii=True, separators=(",", ":")))
PY
)" || finish 2 subprocess-infrastructure-failed
}

repository_input="${REPOSITORY-}"
if [[ -z "$repository_input" || -z "$event" ]]; then
  finish 2 missing-required-input
fi
if [[ "$event" != PR && "$event" != push ]]; then
  finish 2 missing-required-input
fi
if ! repository="$(cd "$repository_input" 2>/dev/null && pwd -P)"; then
  finish 2 invalid-path
fi
if ! git -C "$repository" rev-parse --is-inside-work-tree >/dev/null 2>&1; then
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
    finish 2 missing-required-input
  fi
done

judge_dll_input="${JUDGE_DLL-}"
judge_address_input="${JUDGE_SOURCE_ADDRESS-}"
if [[ -n "$judge_dll_input" ]]; then
  if [[ "$judge_dll_input" != /* ]]; then
    judge_dll_input="$repository/$judge_dll_input"
  fi
  if [[ ! -f "$judge_dll_input" ]]; then
    finish 2 invalid-path
  fi
  judge_dll="$(python3 - "$judge_dll_input" <<'PY'
import os
import sys
sys.stdout.write(os.path.realpath(sys.argv[1]))
PY
)" ||
    finish 2 invalid-path
  if [[ "$judge_dll" != "$repository/"* ]]; then
    finish 2 invalid-path
  fi
  if [[ ! "$judge_address_input" =~ ^[0-9a-f]{64}$ ]]; then
    finish 2 judge-address-verification-failed
  fi
  judge_source_address="$judge_address_input"
elif [[ -n "$judge_address_input" ]]; then
  finish 2 judge-address-verification-failed
fi

temporary_directory="$(mktemp -d "${TMPDIR:-/tmp}/segment-engineering.XXXXXX")" ||
  finish 2 subprocess-infrastructure-failed
parents_log="$temporary_directory/parents.log"
if ! parents_line="$(git -C "$repository" rev-list --parents -n 1 HEAD 2>"$parents_log")"; then
  cat "$parents_log" >&2
  finish 2 subprocess-infrastructure-failed
fi
cat "$parents_log" >&2
read -r -a parent_parts <<< "$parents_line"
if [[ "${#parent_parts[@]}" -lt 1 || ! "${parent_parts[0]}" =~ ^[0-9a-f]{40}$ ]]; then
  finish 2 subprocess-infrastructure-failed
fi
merge_commit="${parent_parts[0]}"
if ! tree_value="$(git -C "$repository" rev-parse 'HEAD^{tree}' 2>"$parents_log")"; then
  cat "$parents_log" >&2
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
  finish 2 parent-mismatch
fi
if [[ "$event" == push && "$parent_count" -lt 1 ]]; then
  finish 2 parent-mismatch
fi
if [[ "$parent_count" -eq 2 ]]; then
  source_head="${parent_parts[2]}"
fi

record_check restore-compile-fail-proofs
if ! dotnet restore "$repository/tools/tests/CompileFailProof/CompileFailProof.csproj" --locked-mode >&2; then
  finish 2 subprocess-infrastructure-failed
fi
if ! dotnet restore "$repository/tools/tests/BannedApiCompileFailProof/BannedApiCompileFailProof.csproj" --locked-mode >&2; then
  finish 2 subprocess-infrastructure-failed
fi

record_check restore-engineering-solution
if ! dotnet restore "$repository/tools/StrataLint.sln" --locked-mode >&2; then
  finish 2 subprocess-infrastructure-failed
fi

record_check build-candidate
if [[ -z "$judge_dll_input" ]]; then
  if ! /bin/bash "$repository/tools/scripts/dotnet-build.sh" >&2; then
    finish 2 subprocess-infrastructure-failed
  fi
else
  printf 'ENGINEERING_PREBUILT_JUDGE status=accepted address=%s path=%s\n' \
    "$judge_source_address" "$judge_dll" >&2
fi

record_check engineering-tests
engineering_log="$temporary_directory/engineering-tests.log"
engineering_status=0
/bin/bash "$repository/tools/scripts/workflow/engineering-test-execution-harness.sh" \
  "$repository" >"$engineering_log" 2>&1 || engineering_status=$?
cat "$engineering_log" >&2
if grep -Eq '^(ENGINEERING_TEST_PLAN |TEST_EVIDENCE_IDENTITIES selected_test_ids=)' \
  "$engineering_log"; then
  if ! selected_test_ids_json="$(python3 - "$engineering_log" <<'PY'
import json
import sys

prefix = "TEST_EVIDENCE_IDENTITIES selected_test_ids="
identities = set()
with open(sys.argv[1], "r", encoding="utf-8") as stream:
    for raw_line in stream:
        line = raw_line.rstrip("\n")
        if not line.startswith(prefix):
            continue
        values = json.loads(line[len(prefix):])
        if not isinstance(values, list) or any(not isinstance(value, str) for value in values):
            raise ValueError("executed test identity evidence is not a string array")
        identities.update(values)
ordered = sorted(identities, key=lambda value: value.encode("utf-8"))
sys.stdout.write(json.dumps(ordered, ensure_ascii=True, separators=(",", ":")))
PY
)"; then
    finish 2 subprocess-infrastructure-failed
  fi
fi
if [[ "$engineering_status" -eq 1 ]]; then
  finish 1 candidate-check-failed
elif [[ "$engineering_status" -ne 0 ]]; then
  finish 2 subprocess-infrastructure-failed
fi

record_check stratalint-selftest
selftest_status=0
/bin/bash "$repository/tools/scripts/stratalint-selftest.sh" >&2 || selftest_status=$?
if [[ "$selftest_status" -eq 1 ]]; then
  finish 1 candidate-check-failed
elif [[ "$selftest_status" -ne 0 ]]; then
  finish 2 subprocess-infrastructure-failed
fi

record_check compile-fail-proof
compile_fail_log="$temporary_directory/compile-fail-proof.log"
compile_fail_status=0
dotnet build "$repository/tools/tests/CompileFailProof/CompileFailProof.csproj" \
  --no-restore --configuration Release >"$compile_fail_log" 2>&1 || compile_fail_status=$?
cat "$compile_fail_log" >&2
if [[ "$compile_fail_status" -gt 1 ]]; then
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
