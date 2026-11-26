#!/usr/bin/env bash
set -eo pipefail

find_checkpoint() {
  gh api --paginate "repos/$GITHUB_REPOSITORY/actions/runs/$1/artifacts?per_page=100" \
  | jq -rs --arg prefix "lean-release-checkpoint-$MODE-$1-" --argjson before "$2" '
      [.[].artifacts[] | select(.expired == false and (.name | startswith($prefix)))
       | select((.digest // "") | test("^sha256:[0-9a-f]{64}$"))
       | .attempt = (.name | ltrimstr($prefix))
       | select(.attempt | test("^[1-9][0-9]*$")) | .attempt |= tonumber
       | select(.attempt < $before)] | max_by(.attempt) // empty | [.id, .attempt] | @tsv'
}
select_checkpoint() {
  local source_run=$1 last_attempt=$2 selected=0 prior job artifact_name
  checkpoint=$(find_checkpoint "$source_run" "$((last_attempt + 1))")
  if [[ -n "$checkpoint" ]]; then
    read -r artifact selected <<< "$checkpoint"
  fi
  for ((prior=last_attempt; prior>selected; prior--)); do
    if ! job=$(gh api --paginate "repos/$GITHUB_REPOSITORY/actions/runs/$source_run/attempts/$prior/jobs?per_page=100" \
      --jq '.jobs[] | select(.name == "verify cache publication and restore")
        | select(any(.steps[]; .name == "Restore the selected Release build seeds" and (.conclusion == "failure" or .conclusion == "cancelled"))) | .id'); then
      history_unavailable="$source_run/$prior"
      echo "::warning::Cannot inspect checkpoint jobs from $history_unavailable"
      continue
    fi
    [[ -n "$job" ]] || continue
    if ! gh run view --repo "$GITHUB_REPOSITORY" "$source_run" --attempt "$prior" --job "$job" --log > "$RUNNER_TEMP/lean-release-prior.log"; then
      history_unavailable="$source_run/$prior"
      echo "::warning::Cannot inspect checkpoint log from $history_unavailable"
      continue
    fi
    artifact_name="lean-release-checkpoint-$MODE-$source_run-$prior"
    if grep -Fq "Z Artifact $artifact_name has been successfully uploaded!" "$RUNNER_TEMP/lean-release-prior.log" || {
      grep -Fq "Z LEAN_RELEASE_HANDOFF seed=$MODE " "$RUNNER_TEMP/lean-release-prior.log" &&
      grep -Eq 'Z LEAN_RELEASE_HANDOFF checkpoint=[1-9][0-9]*(;|$)' "$RUNNER_TEMP/lean-release-prior.log"
    }; then
      missing="$source_run/$prior"
      echo "::warning::Published $MODE checkpoint from $missing is unavailable"
    fi
  done
}
missing=""
history_unavailable=""
run="$GITHUB_RUN_ID"
select_checkpoint "$run" "$((GITHUB_RUN_ATTEMPT - 1))"
if [[ -z "$checkpoint" && -n "$CHECKPOINT_RUN" ]]; then
  [[ "$GITHUB_EVENT_NAME" == workflow_dispatch && "$GITHUB_REF_PROTECTED" == true ]]
  [[ "$CHECKPOINT_RUN" =~ ^[1-9][0-9]*$ && "$CHECKPOINT_RUN" != "$run" ]]
  run="$CHECKPOINT_RUN"
  prior_attempt="$(gh api "repos/$GITHUB_REPOSITORY/actions/runs/$run" | jq -er \
    --argjson run "$run" --arg sha "$GITHUB_SHA" --arg branch "$GITHUB_REF_NAME" --arg repository "$GITHUB_REPOSITORY" '
    select(.id == $run and .head_sha == $sha and .head_branch == $branch and .status == "completed"
      and .repository.full_name == $repository
      and .path == ".github/workflows/ci-publication-verify.yml"
      and (.event == "push" or .event == "workflow_dispatch")) | .run_attempt
    | select(type == "number" and . >= 1 and . == floor)')"
  select_checkpoint "$run" "$prior_attempt"
fi
if [[ -z "$checkpoint" ]]; then
  if [[ -n "$missing" || -n "$CHECKPOINT_RUN" || -n "$history_unavailable" ]]; then
    echo "LEAN_RELEASE_HANDOFF_ERROR no recoverable $MODE checkpoint for run $run" >&2
    exit 2
  fi
  echo "LEAN_RELEASE_HANDOFF no published checkpoint in prior attempts, retrying the initial seed"
  exit 0
fi
read -r artifact attempt <<< "$checkpoint"
[[ "$artifact" =~ ^[1-9][0-9]*$ && "$attempt" =~ ^[1-9][0-9]*$ ]]
echo "LEAN_RELEASE_HANDOFF selected checkpoint run=$run attempt=$attempt artifact=$artifact"
echo "artifact=$artifact" >> "$GITHUB_OUTPUT"
echo "attempt=$attempt" >> "$GITHUB_OUTPUT"
echo "run=$run" >> "$GITHUB_OUTPUT"
