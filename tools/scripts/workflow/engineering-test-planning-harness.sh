#!/usr/bin/env bash
set -euo pipefail

usage() {
  printf '%s\n' \
    'usage: engineering-test-planning-harness.sh materialize <candidate> <base-sha> <harness-root> <output-file>' \
    '       engineering-test-planning-harness.sh plan <candidate> <harness-root> <plan-file> <candidate-repository> <output-file> <event-name>' \
    '       engineering-test-planning-harness.sh remove <candidate> <harness-root>' >&2
  exit 2
}

action="${1:-}"
case "$action" in
  materialize)
    [[ "$#" -eq 5 ]] || usage
    candidate="$2"
    base_sha="$3"
    base_harness_root="$4"
    output_file="$5"

    test ! -e "$base_harness_root"
    cleanup_on_error() {
      status=$?
      if [[ "$status" -ne 0 && -e "$base_harness_root" ]]; then
        git -C "$candidate" worktree remove --force "$base_harness_root" || true
      fi
      return "$status"
    }
    trap cleanup_on_error EXIT
    git -C "$candidate" worktree add --detach "$base_harness_root" "$base_sha"
    printf 'root=%s\n' "$base_harness_root" >> "$output_file"
    trap - EXIT
    ;;

  plan)
    [[ "$#" -eq 7 ]] || usage
    candidate="$2"
    base_harness_root="$3"
    plan_file="$4"
    candidate_repository="$5"
    output_file="$6"
    event_name="$7"

    head_sha="$(git -C "$candidate" rev-parse HEAD)"
    base_sha="$(git -C "$candidate" rev-parse HEAD^1)"
    base_full_required=false
    changed_count=0
    path=""
    while IFS= read -r -d '' path; do
      changed_count="$((changed_count + 1))"
      case "$path" in
        tools|tools/*|.github/workflows/ci.yml) base_full_required=true ;;
        */*) ;;
        *) base_full_required=true ;;
      esac
    done < <(git -C "$candidate" diff --name-only -z --no-renames --diff-filter=ACDMRTUXB "$base_sha" "$head_sha" --)
    if [[ "$base_full_required" == "true" ]]; then
      base_full_required=true
      FULL=1 make -C "$base_harness_root/tools" engineering-tests-base-cwd REPOSITORY="$candidate_repository" MODE=plan HEAD="$head_sha" BASE="$base_sha" PLAN_FILE="$plan_file"
    else
      make -C "$base_harness_root/tools" engineering-tests-base-cwd REPOSITORY="$candidate_repository" MODE=plan HEAD="$head_sha" BASE="$base_sha" PLAN_FILE="$plan_file"
    fi
    fallback_count=0
    plan_summary=""
    plan_summary="$(
      /bin/bash "$base_harness_root/tools/scripts/workflow/engineering-test-plan-validator.sh" \
        "$plan_file" "$head_sha" "$base_sha" --artifact-fallback
    )"
    IFS=$'\t' read -r state artifact_changed_count selected_count <<< "$plan_summary"
    if [[ "$artifact_changed_count" -ne "$changed_count"
        || ("$base_full_required" == "true" && "$state" != "full") ]]; then
      printf '%s\n' 'ENGINEERING_TEST_PLAN_FALLBACK artifact unreadable or schema-invalid' >&2
      rm -f -- "$plan_file"
      state=full
      selected_count=0
      fallback_count=1
    fi
    execution_full_required="$base_full_required"
    if [[ "$fallback_count" -ne 0 ]]; then
      execution_full_required=true
    fi
    run_required=false
    if [[ "$state" != "none" || "$base_full_required" == "true" ]]; then
      run_required=true
    fi
    echo "state=$state" >> "$output_file"
    echo "execution_full_required=$execution_full_required" >> "$output_file"
    echo "run_required=$run_required" >> "$output_file"
    echo "event=$event_name" >> "$output_file"
    echo "head_sha=$head_sha" >> "$output_file"
    echo "base_sha=$base_sha" >> "$output_file"
    echo "changed_count=$changed_count" >> "$output_file"
    echo "selected_count=$selected_count" >> "$output_file"
    echo "fallback_count=$fallback_count" >> "$output_file"
    ;;

  remove)
    [[ "$#" -eq 3 ]] || usage
    candidate="$2"
    base_harness_root="$3"

    if [[ -d "$base_harness_root" && -d "$candidate" ]]; then
      git -C "$candidate" worktree remove --force "$base_harness_root"
    fi
    test ! -e "$base_harness_root"
    ;;

  *)
    usage
    ;;
esac
