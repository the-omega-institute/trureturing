#!/usr/bin/env bash
set -euo pipefail

if [[ ("$#" -ne 3 && "$#" -ne 4) || -z "$1" || -z "$2" || -z "$3" ]]; then
  printf '%s\n' \
    'usage: engineering-test-plan-validator.sh <plan-file|-> <expected-head> <expected-base> [--artifact-fallback]' >&2
  exit 2
fi

plan_file="$1"
expected_head="$2"
expected_base="$3"
artifact_fallback=false
if [[ "$#" -eq 4 ]]; then
  if [[ "$4" != "--artifact-fallback" ]]; then
    printf '%s\n' \
      'usage: engineering-test-plan-validator.sh <plan-file|-> <expected-head> <expected-base> [--artifact-fallback]' >&2
    exit 2
  fi
  artifact_fallback=true
fi

invalid_plan() {
  printf 'ENGINEERING_TEST_PLAN_INVALID %s\n' "$1" >&2
  if [[ "$artifact_fallback" == "true" ]]; then
    printf 'invalid\t-1\t0\n'
    exit 0
  fi
  exit 1
}

if [[ "$plan_file" != "-" && ! -f "$plan_file" ]]; then
  invalid_plan "artifact is not a readable file: $plan_file"
fi

jq_path="$(command -v jq || true)"
if [[ -z "$jq_path" ]]; then
  printf '%s\n' 'ENGINEERING_TEST_PLAN_VALIDATOR_FAILURE jq is unavailable' >&2
  exit 70
fi

filter='
select(
    (type == "object" and (keys | sort) == ["base", "head", "plan", "version"])
    and .version == 2 and .head == env.PLAN_EXPECTED_HEAD and .base == env.PLAN_EXPECTED_BASE
    and (.plan | type == "object" and (keys | sort) == ["changed_paths", "kind", "reason", "tests"])
    and (.plan.kind == "full" or .plan.kind == "selected" or .plan.kind == "none")
    and (.plan.changed_paths | type == "array" and all(.[]; type == "string"))
    and (.plan.tests | type == "array" and all(.[];
      type == "object" and (keys | sort) == ["assembly", "detail", "id", "project_path", "reason"]
      and (.assembly | type == "string" and test("\\S"))
      and (.project_path | type == "string" and test("\\S"))
      and (.id | type == "string" and test("\\S"))
      and (.detail | type == "string" and test("\\S"))
      and (.reason == "base_baseline" or .reason == "unknown_input" or .reason == "declared_input" or .reason == "compiled_input")))
    and (.plan.reason | type == "string" and test("\\S"))
    and (.plan.kind != "selected" or (.plan.tests | length) != 0)
    and (.plan.kind != "none" or (.plan.tests | length) == 0)
)
| [.plan.kind, (.plan.changed_paths | length), (.plan.tests | length)] | @tsv
'

compile_status=0
"$jq_path" -n "def engineering_test_plan_summary: $filter; empty" >/dev/null || compile_status=$?
if [[ "$compile_status" -ne 0 ]]; then
  printf 'ENGINEERING_TEST_PLAN_VALIDATOR_FAILURE jq filter did not compile (exit=%s)\n' \
    "$compile_status" >&2
  exit 70
fi

validation_status=0
summary="$(
  PLAN_EXPECTED_HEAD="$expected_head" PLAN_EXPECTED_BASE="$expected_base" \
    "$jq_path" -er "$filter" "$plan_file"
)" || validation_status=$?

case "$validation_status" in
  0)
    printf '%s\n' "$summary"
    ;;
  1|2|4|5)
    invalid_plan "schema validation failed (jq exit=$validation_status)"
    ;;
  *)
    printf 'ENGINEERING_TEST_PLAN_VALIDATOR_FAILURE jq execution failed (exit=%s)\n' \
      "$validation_status" >&2
    exit 70
    ;;
esac
