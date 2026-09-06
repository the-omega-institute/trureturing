#!/usr/bin/env bash
set -u
set -o pipefail

usage() {
  printf '%s\n' 'usage: daily-full-test.sh run|report LOG_DIRECTORY' >&2
  exit 2
}

[[ $# -eq 2 && -n $1 && -n $2 ]] || usage
mode=$1
log_directory=$2
repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)" || exit 2

run_full_tests() {
  command -v make >/dev/null 2>&1 || exit 127
  command -v tee >/dev/null 2>&1 || exit 127
  command -v env >/dev/null 2>&1 || exit 127
  mkdir -p "$log_directory" || exit 2
  cd "$repo_root" || exit 2

  set +e
  # Match PR engineering's live-report environment before the content gate creates
  # a report. Tree and executor fidelity remain separate attribution prerequisites.
  env -u STRATALINT_REQUIRE_LIVE_REPORT -u STRATALINT_LEAN_REPORT \
    CI=true make -C tools test 2>&1 | tee "$log_directory/tools.log"
  tools_exit=${PIPESTATUS[0]}
  env -u STRATALINT_REQUIRE_LIVE_REPORT -u STRATALINT_LEAN_REPORT \
    CI=true make test 2>&1 | tee "$log_directory/content.log"
  content_exit=${PIPESTATUS[0]}
  set -e

  result_tmp="$log_directory/result.env.tmp"
  printf 'content_exit=%s\ntools_exit=%s\n' "$content_exit" "$tools_exit" > "$result_tmp"
  mv "$result_tmp" "$log_directory/result.env"
  printf 'DAILY_FULL_TEST_RESULT content_exit=%s tools_exit=%s\n' \
    "$content_exit" "$tools_exit"
  [[ $content_exit -eq 0 && $tools_exit -eq 0 ]]
}

report_failure() {
  command -v gh >/dev/null 2>&1 || exit 127
  : "${GH_TOKEN:?}"
  : "${GITHUB_REPOSITORY:?}"
  : "${GITHUB_SERVER_URL:?}"
  : "${GITHUB_RUN_ID:?}"
  : "${GITHUB_RUN_ATTEMPT:?}"
  : "${GITHUB_SHA:?}"
  : "${GITHUB_EVENT_NAME:?}"
  : "${DAILY_FAILURE_ASSIGNEE:?}"
  mkdir -p "$log_directory" || exit 2

  content_exit=not-produced
  tools_exit=not-produced
  if [[ -f $log_directory/result.env ]]; then
    while IFS='=' read -r key value; do
      case "$key" in
        content_exit) content_exit=$value ;;
        tools_exit) tools_exit=$value ;;
      esac
    done < "$log_directory/result.env"
  fi

  failures="$log_directory/failing-identities.txt"
  : > "$failures"
  for log in "$log_directory/content.log" "$log_directory/tools.log"; do
    [[ -f $log ]] || continue
    grep -E '\[FAIL\]|^[[:space:]]*Failed[[:space:]]|:[[:digit:]]+(:[[:digit:]]+)?:[[:space:]]+error(:|[[:space:]])' \
      "$log" >> "$failures" || true
  done
  if [[ ! -s $failures ]]; then
    printf '%s\n' \
      '[FAIL] workflow job Run both full test layers (test identity not produced)' \
      > "$failures"
  fi

  run_url="$GITHUB_SERVER_URL/$GITHUB_REPOSITORY/actions/runs/$GITHUB_RUN_ID"
  body="$log_directory/issue-body.md"
  {
    printf '%s\n\n' 'The non-required daily full-test backstop failed.'
    printf 'Owner: @%s\n\n' "$DAILY_FAILURE_ASSIGNEE"
    printf '%s\n' 'Provenance: no skill; GitHub Actions executed the repository-owned reporter.'
    printf '%s\n' 'Carrier and roles: the daily workflow ran both canonical test targets and this script reported their machine verdict.'
    printf '%s\n\n' 'Mixing: no model synthesis or review result participates in this incident signal.'
    printf 'Run: %s\n\n' "$run_url"
    printf "Commit: \`%s\`\n\n" "$GITHUB_SHA"
    printf "Trigger: \`%s\`; attempt: \`%s\`\n\n" "$GITHUB_EVENT_NAME" "$GITHUB_RUN_ATTEMPT"
    printf '%s\n\n' 'Full-target results:'
    printf -- "- \`make test\`: \`%s\`\n" "$content_exit"
    printf -- "- \`make -C tools test\`: \`%s\`\n\n" "$tools_exit"
    printf '%s\n\n' 'Named failing identities (first 40 matching log lines):'
    head -n 40 "$failures" | sed 's/^/    /'
    if [[ $content_exit == not-produced && $tools_exit == not-produced ]]; then
      printf '%s\n' 'Individual test identities were not produced before the workflow job failed.'
    fi
  } > "$body"

  title='Daily full-test backstop is failing'
  issues="$log_directory/open-issues.tsv"
  if ! gh issue list --repo "$GITHUB_REPOSITORY" --state open \
    --search "\"$title\" in:title" --limit 100 --json number,title,url \
    --jq '.[] | [.number, .title, .url] | @tsv' > "$issues"; then
    printf '%s\n' \
      'DAILY_FULL_TEST_DEDUP status=list-unavailable action=create-new-issue' >&2
    : > "$issues"
  fi

  existing_number=""
  existing_url=""
  while IFS=$'\t' read -r candidate_number candidate_title candidate_url; do
    if [[ $candidate_title == "$title" && -n $candidate_number && -n $candidate_url ]]; then
      existing_number=$candidate_number
      existing_url=$candidate_url
      break
    fi
  done < "$issues"
  if [[ -n $existing_number ]]; then
    gh issue edit "$existing_number" --repo "$GITHUB_REPOSITORY" \
      --add-assignee "$DAILY_FAILURE_ASSIGNEE" >/dev/null || exit $?
    gh issue comment "$existing_number" --repo "$GITHUB_REPOSITORY" \
      --body-file "$body" >/dev/null || exit $?
    printf 'DAILY_FULL_TEST_ISSUE status=commented url=%s\n' "$existing_url"
    return 0
  fi

  issue_url="$(gh issue create \
    --repo "$GITHUB_REPOSITORY" \
    --assignee "$DAILY_FAILURE_ASSIGNEE" \
    --title "$title" \
    --body-file "$body")" || exit $?
  [[ -n $issue_url ]] || exit 1
  printf 'DAILY_FULL_TEST_ISSUE status=created url=%s\n' "$issue_url"
}

case "$mode" in
  run) run_full_tests ;;
  report) report_failure ;;
  *) usage ;;
esac
