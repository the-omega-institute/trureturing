#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf '%s\n' 'usage: engineering-test-report.sh <execute|summarize>' >&2
  exit 2
}

action="${1:-}"
[[ "$#" -eq 1 ]] || usage

case "$action" in
  execute)
    plan_file="$RUNNER_TEMP/engineering-test-plan.json"
    base_harness_root="$RUNNER_TEMP/protected-base-engineering-execution-harness"
    test ! -e "$base_harness_root"
    rm -f -- "$RUNNER_TEMP/engineering-test-plan.json"
    git -C candidate worktree add --detach "$base_harness_root" "$ENGINEERING_BASE"
    cleanup_base_harness() {
      status=$?
      trap - EXIT
      set +e
      git -C candidate worktree remove --force "$base_harness_root"
      cleanup_status=$?
      if [[ -e "$base_harness_root" ]]; then
        printf 'protected-base engineering harness still exists: %s\n' "$base_harness_root" >&2
        cleanup_status=1
      fi
      set -e
      if [[ "$status" -ne 0 ]]; then
        exit "$status"
      fi
      exit "$cleanup_status"
    }
    trap cleanup_base_harness EXIT
    test "$(git -C "$base_harness_root" rev-parse HEAD)" = "$ENGINEERING_BASE"
    test -z "$(git -C "$base_harness_root" status --short --untracked-files=no)"
    (
      cd "$base_harness_root"
      dotnet restore tools/StrataLint.sln --locked-mode
    )
    if [[ "$ENGINEERING_EXECUTION_FULL_REQUIRED" == "true" ]]; then
      FULL=1 make -C "$base_harness_root/tools" engineering-tests-base-cwd REPOSITORY="$GITHUB_WORKSPACE/candidate" MODE=plan HEAD="$ENGINEERING_HEAD" BASE="$ENGINEERING_BASE" PLAN_FILE="$plan_file"
    else
      make -C "$base_harness_root/tools" engineering-tests-base-cwd REPOSITORY="$GITHUB_WORKSPACE/candidate" MODE=plan HEAD="$ENGINEERING_HEAD" BASE="$ENGINEERING_BASE" PLAN_FILE="$plan_file"
    fi
    artifact_root="$RUNNER_TEMP/engineering-test-plan-artifact"
    execution_log="$artifact_root/engineering-test-execution.log"
    execution_record="$artifact_root/engineering-test-plan.json"
    mkdir -p "$artifact_root"
    set +e
    make -C "$base_harness_root/tools" engineering-tests-base-cwd REPOSITORY="$GITHUB_WORKSPACE/candidate" MODE=execute HEAD="$ENGINEERING_HEAD" BASE="$ENGINEERING_BASE" PLAN_FILE="$plan_file" 2>&1 | tee "$execution_log"
    pipeline_status=("${PIPESTATUS[@]}")
    set -e
    execute_status="${pipeline_status[0]}"
    tee_status="${pipeline_status[1]}"
    if [[ "$tee_status" -ne 0 ]]; then
      printf 'engineering test execution log capture returned nonzero exit=%s\n' "$tee_status" >&2
      exit "$tee_status"
    fi
    plan_diagnostic_prefix="$(jq -r '.resolution.plan_diagnostic_prefix' <<< "$ENGINEERING_REPORT_SCHEMA")"
    evidence_diagnostic_prefix="$(jq -r '.resolution.evidence_diagnostic_prefix' <<< "$ENGINEERING_REPORT_SCHEMA")"
    tail_field="$(jq -r '.resolution.tail_field' <<< "$ENGINEERING_REPORT_SCHEMA")"
    jq -Rsc \
      --arg repository "$GITHUB_REPOSITORY" \
      --arg run_id "$GITHUB_RUN_ID" \
      --arg head "$ENGINEERING_HEAD" \
      --arg base "$ENGINEERING_BASE" \
      --argjson execute_exit "$execute_status" \
      --arg plan_diagnostic_prefix "$plan_diagnostic_prefix" \
      --arg evidence_diagnostic_prefix "$evidence_diagnostic_prefix" \
      --arg tail_field "$tail_field" \
      '
        split("\n") | map(select(length > 0)) as $lines
        | ([$lines[] | select(startswith("ENGINEERING_TEST_PLAN_FALLBACK "))]) as $fallback
        | {
            version: 1,
            repository: $repository,
            run_id: $run_id,
            head: $head,
            base: $base,
            execute_exit: $execute_exit,
            plan_verdict: (
              if ($fallback | length) > 0 then "fallback"
              elif any($lines[]; startswith("ENGINEERING_TEST_PLAN ")) then "accepted"
              else "unavailable"
              end),
            diagnostics: [
              $lines[]
              | select(
                  startswith("ENGINEERING_TEST_PLAN_FALLBACK ")
                  or startswith($plan_diagnostic_prefix)
                  or startswith($evidence_diagnostic_prefix))
            ],
            plan: {
              summary: ([$lines[] | select(startswith("ENGINEERING_TEST_PLAN "))][0] // null),
              tests: [$lines[] | select(startswith("ENGINEERING_TEST_SELECTED "))]
            },
            ($tail_field): (if $execute_exit == 0 then [] else $lines[-40:] end)
          }
      ' "$execution_log" > "$execution_record.tmp"
    mv "$execution_record.tmp" "$execution_record"
    exit "$execute_status"
    ;;

  summarize)
    result="$SCOPE_STATE"
    if [[ -z "$result" ]]; then
      result="unavailable"
    fi
    fallback_count="$SCOPE_FALLBACK_COUNT"
    [[ -n "$fallback_count" ]] || fallback_count=0
    detail_dir="engineering-test-plan-$GITHUB_RUN_ID"
    tail_field="$(jq -r '.resolution.tail_field' <<< "$ENGINEERING_REPORT_SCHEMA")"
    detail_command="gh run download $GITHUB_RUN_ID --repo $GITHUB_REPOSITORY --name engineering-test-plan --dir $detail_dir && jq '{execute_exit, plan_verdict, diagnostics, plan, ${tail_field}}' $detail_dir/engineering-test-plan.json"
    {
      printf '%s\n' '## Candidate engineering scope'
      printf '\n'
      printf -- '- Event: %s\n' "$SCOPE_EVENT"
      printf -- '- Test plan: %s\n' "$result"
      printf -- '- Dev parent: %s\n' "$SCOPE_BASE"
      printf -- '- Changed paths: %s\n' "$SCOPE_CHANGED_COUNT"
      printf -- '- Selected tests: %s\n' "$SCOPE_SELECTED_COUNT"
      printf -- '- Planner fallback count: %s\n' "$fallback_count"
      printf -- '- Plan artifact upload: %s\n' "$PLAN_ARTIFACT_OUTCOME"
      printf -- '- Detail: `%s`.\n' "$detail_command"
    } >> "$GITHUB_STEP_SUMMARY"
    ;;

  *)
    usage
    ;;
esac
