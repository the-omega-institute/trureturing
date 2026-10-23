#!/usr/bin/env bash
# Mirror dev PR landings serially; GitHub checks supply every verdict.
# Usage: integration-mirror.sh --integration BRANCH [--since DEV_COMMIT_SHA]
#          [--max N] [--state FILE] [--dry-run] [--required-checks-under-test REF]
# The integration branch must require exactly dev's required checks. When the
# integration branch is testing a change of the required checks themselves,
# --required-checks-under-test names the open issue or PR of this repository
# that declares that change (#N); both sets are then logged and mirrors are
# judged by the integration set.
# First invocation requires --since. Later invocations resume from JSONL state
# (default: <git-common-dir>/integration-mirror/<URL-encoded-branch>.jsonl).
# Failed/conflicted entries are retried, never treated as completed cursors.
# --dry-run fetches and reads GitHub, but creates no branches, PRs or state.
# --max bounds successful merges; pending counts the remaining fetched plan.
# Exit: 0 complete/bounded/dry-run; 64 invalid input/precondition; 65 conflict;
# 66 red checks (PR left open); 69 transport/incomplete checks/unsafe recovery;
# 130 interrupted; 143 terminated.
# Before required checks register, wait on pull_request runs for the exact head.
# Native watchers own CI lifetimes; only discovery and transport retries are
# bounded. A completed run without a terminal required verdict is incomplete.
# Existing mirror PRs/branches are reused, never force-pushed or recreated.
# One OS-held operation scope per integration follower; descendants inherit it.
# Example: tools/scripts/agent/integration-mirror.sh \
#   --integration integration-regprog-0912 --since 748360e3dd32 --dry-run
# This transport does not certify workflow versions, performance, push runs or
# a stability count; those analyses and delivery to dev belong to the caller.
set -Eeuo pipefail

VERSION=7
PROTOCOL="$(cd "$(dirname "${BASH_SOURCE[0]}")/../worktree" && pwd -P)/worktree_protocol.py"
# GitHub discovery/transport retries and merge-request retries.
RETRY_ATTEMPTS=30 RETRY_INTERVAL=15
original_arguments=("$@")
integration='' since='' state='' max=0 dry_run=0 checks_under_test=''
mirrored=0 pending=0 scratch='' worktree='' lock=''
merge='' original_pr=0 mirror_pr=0 head='' base='' verdicts='[]'
repo='' output=''

log() { printf '%s merge=%s head=%s base=%s %s\n' "$(date -u +%FT%TZ)" "${merge:--}" "${head:--}" "${base:--}" "${*//$'\n'/ }"; }
die() { log "ERROR $2" >&2; exit "$1"; }
remove_worktree() {
  if [[ -n "$worktree" ]]; then
    python3 -B "$PROTOCOL" --source "$root" remove --path "$worktree" || return 1
    worktree=''
  fi
}
cleanup() {
  local rc=$?
  trap - EXIT ERR
  set +e
  if ! remove_worktree; then
    log "ERROR temporary worktree cleanup failed: $worktree" >&2
    rc=69
  elif [[ -n "$scratch" ]]; then
    rm -f "$scratch/command.log" "$scratch/first-parent" "$scratch/landings" "$scratch/plan" || rc=69
    rmdir "$scratch" 2>/dev/null || log "retained additional scratch material: $scratch"
  fi
  printf 'MIRROR_RESULT mirrored=%s pending=%s exit=%s\n' "$mirrored" "$pending" "$rc"
  exit "$rc"
}
trap cleanup EXIT
trap 'die 69 "unexpected command failure at line $LINENO"' ERR
trap 'exit 130' INT
trap 'exit 143' TERM

# Keep command output out of machine-readable step lines; preserve errors in
# one timestamped line. The native watcher remains the sole waiting primitive.
run() {
  local step=$1 rc=0
  shift
  log "$step"
  "$@" >"$scratch/command.log" 2>&1 || rc=$?
  output=$(cat "$scratch/command.log")
  if (( rc != 0 )); then log "$step exit=$rc $output" >&2; fi
  return "$rc"
}
record() {
  local status=$1 merged_at=${2:-} conflicts=${3:-'[]'}
  jq -cn --arg integration "$integration" --arg merge "$merge" \
    --argjson original_pr "$original_pr" --argjson mirror_pr "$mirror_pr" \
    --arg head "$head" --arg base "$base" --argjson verdicts "$verdicts" \
    --arg status "$status" --arg merged_at "$merged_at" --arg version "$VERSION" \
    --argjson conflict_paths "$conflicts" \
    '{integration:$integration,merge:$merge,original_pr:$original_pr,
      mirror_pr:(if $mirror_pr == 0 then null else $mirror_pr end),head:$head,
      base:$base,verdicts:$verdicts,status:$status,version:$version,
      merged_at:(if $merged_at == "" then null else $merged_at end),
      conflict_paths:$conflict_paths}' >>"$state" || die 69 "cannot append state: $state"
}
read_verdicts() {
  local rc=0 parsed
  verdicts='[]'
  run verdicts gh pr checks "$mirror_pr" --repo "$repo" --required \
    --json name,state,bucket,link,workflow,event,startedAt,completedAt || rc=$?
  # gh returns 1 for failed checks and 8 for pending checks even with --json.
  case $rc in 0|1|8) ;; *) return 1 ;; esac
  parsed=$(jq -cse 'select(length == 1 and (.[0] | type == "array")) | .[0]' <<<"$output" 2>/dev/null) || return 1
  verdicts=$parsed
}
terminal_verdict() {
  jq -e --argjson required "$integration_required" '
    any(.[]; .bucket == "fail" or .bucket == "cancel") or
    (([.[].name] | unique | sort) == ($required | sort) and all(.[]; .bucket == "pass"))
  ' <<<"$verdicts" >/dev/null
}
watch_checks() {
  local attempt=0 runs active run_id failed
  while :; do
    run watch gh pr checks "$mirror_pr" --repo "$repo" --required --watch --fail-fast || true
    if read_verdicts && terminal_verdict; then return 0; fi
    # The aggregate required job need not exist while its unit jobs are running.
    # Run association uses the exact head and event, including runs whose PR list
    # is empty. Workflow conclusions never authorize a merge.
    if run discover-runs gh run list --repo "$repo" --commit "$head" --event pull_request \
      --json databaseId,headSha,event,status --limit 100 &&
      runs=$(jq -ce --arg head "$head" 'select(type == "array") |
        map(select(.headSha == $head and .event == "pull_request")) | select(length > 0)
      ' <<<"$output"); then
      active=$(jq -r '.[] | select(.status != "completed") | .databaseId' <<<"$runs")
      [[ -n "$active" ]] || return 1
      failed=0
      while IFS= read -r run_id; do
        run watch-run gh run watch "$run_id" --repo "$repo" || failed=1
        if read_verdicts && terminal_verdict; then return 0; fi
      done <<<"$active"
      if (( failed == 0 )); then
        attempt=0
        continue
      fi
    fi
    attempt=$((attempt + 1))
    (( attempt < RETRY_ATTEMPTS )) || return 1
    sleep "$RETRY_INTERVAL"
  done
}
validate_head() {
  run validate-mirror python3 -B "$PROTOCOL" --source "$root" validate-mirror \
    --commit "$head" --base "$integration_tip" --merge "$merge" \
    --message "mirror: #$original_pr $original_subject" \
    || die 69 "existing mirror head violates the producer contract"
  base=$(jq -er '.base' <<<"$output") || die 69 "missing validated mirror base"
}

while (( $# )); do
  case $1 in
    --integration|--since|--max|--state|--required-checks-under-test)
      (( $# >= 2 )) && [[ -n "$2" && "$2" != --* ]] || die 64 "missing value for $1"
      case $1 in
        --required-checks-under-test) checks_under_test=$2
          [[ "$checks_under_test" =~ ^#[1-9][0-9]*$ ]] || die 64 "--required-checks-under-test must be an issue or PR reference #N" ;;
        --integration) integration=$2 ;;
        --since) since=$2 ;;
        --max) max=$2
          [[ "$max" =~ ^[1-9][0-9]*$ && ${#max} -le 9 ]] || die 64 "--max must be a positive integer (at most 999999999)" ;;
        --state) state=$2 ;;
      esac
      shift 2 ;;
    --dry-run) dry_run=1; shift ;;
    *) die 64 "unknown argument: $1" ;;
  esac
done
for tool in git gh jq; do command -v "$tool" >/dev/null || die 64 "missing tool: $tool"; done
[[ -n "$integration" && "$integration" != -* && "$integration" != dev ]] || die 64 "invalid integration branch"
git check-ref-format "refs/heads/$integration" || die 64 "invalid integration branch"
[[ -z "$since" || "$since" =~ ^[0-9a-fA-F]{7,40}$ ]] || die 64 "--since must be a commit SHA"
root=$(git rev-parse --show-toplevel) || die 64 "not a git worktree"
common=$(git rev-parse --git-common-dir) || die 64 "cannot locate common git directory"
common=$(cd "$common" && pwd -P) || die 64 "cannot resolve common git directory"
main_root=$(cd "$common/.." && pwd -P)
root=$(cd "$root" && pwd -P)
[[ "$root" != "$main_root" && -f "$root/.git" ]] || die 64 "main checkout is forbidden"
[[ $(git symbolic-ref --quiet --short HEAD || true) != dev ]] || die 64 "dev checkout is forbidden"
cd "$root"
branch_key=$(jq -nr --arg branch "$integration" '$branch | @uri')
state=${state:-"$common/integration-mirror/$branch_key.jsonl"}
[[ "$state" == /* ]] || state="$root/$state"
if [[ -e "$state" ]]; then
  [[ -f "$state" && -r "$state" && -w "$state" ]] || die 64 "state must be a readable, writable regular file"
fi
if (( dry_run == 0 )); then
  if [[ -z "${MIRROR_OPERATION_HELD:-}" ]]; then
    exec python3 -B "$PROTOCOL" --source "$root" with --path "$root" \
      --operation "integration-mirror:$integration" -- env MIRROR_OPERATION_HELD=1 \
      /bin/bash "${BASH_SOURCE[0]}" "${original_arguments[@]}"
  fi
fi
scratch=$(mktemp -d "${TMPDIR:-/tmp}/integration-mirror.XXXXXX") || die 64 "cannot create temporary directory"
if (( dry_run == 0 )); then
  mkdir -p "$common/integration-mirror" || die 64 "cannot create local state directory"

fi
[[ -d "${state%/*}" && -w "${state%/*}" ]] \
  || { (( dry_run )) && [[ "$state" == "$common/integration-mirror/$branch_key.jsonl" ]]; } \
  || die 64 "state parent must exist and be writable"
state_data='[]'
if [[ -s "$state" ]]; then
  state_data=$(jq -sce --arg integration "$integration" '
    select(all(.[]; type == "object" and .integration == $integration and
      (.merge | type == "string" and test("^[0-9a-f]{40}$")) and
      (.original_pr | type == "number" and . > 0 and floor == .) and
      (.merged_at == null or (.merged_at | type == "string" and length > 0))))
  ' "$state") || die 64 "invalid JSONL state or state belongs to another integration branch"
fi
run auth gh auth status || die 64 "gh authentication failed"
run fetch git fetch origin dev "$integration" || die 64 "cannot fetch dev and integration"
dev_tip=$(git rev-parse --verify 'refs/remotes/origin/dev^{commit}') || die 64 "missing origin/dev"
integration_tip=$(git rev-parse --verify "refs/remotes/origin/$integration^{commit}") || die 64 "missing integration branch"
base=$integration_tip
origin_url=$(git remote get-url origin) || die 64 "missing origin remote"
repo=$(gh repo view "$origin_url" --json nameWithOwner --jq .nameWithOwner) || die 64 "cannot resolve origin GitHub repository"
run protection-dev gh api "repos/$repo/branches/dev" || die 64 "cannot read dev protection"
dev_required=$(jq -ce 'select(.protected == true) | .protection.required_status_checks |
  ((.contexts // []) + [(.checks // [])[] | .context]) | unique |
  select(length > 0 and all(.[]; type == "string" and length > 0))' <<<"$output") \
  || die 64 "dev must declare a nonempty required-check set"
log "dev required checks=$dev_required"
run protection-integration gh api "repos/$repo/branches/$branch_key" || die 64 "cannot read integration protection"
integration_required=$(jq -ce 'select(.protected == true) | .protection.required_status_checks |
  ((.contexts // []) + [(.checks // [])[] | .context]) | unique |
  select(length > 0 and all(.[]; type == "string" and length > 0))' <<<"$output") \
  || die 64 "integration must declare a nonempty required-check set"
if [[ "$integration_required" != "$dev_required" ]]; then
  [[ -n "$checks_under_test" ]] \
    || die 64 "integration must require the same checks as dev unless --required-checks-under-test names the declaring issue or PR"
  ref_number=${checks_under_test#\#}
  run declaring-ref gh api "repos/$repo/issues/$ref_number" || die 64 "cannot read $checks_under_test in $repo"
  ref_state=$(jq -er --argjson n "$ref_number" 'select(.number == $n) | .state' <<<"$output") \
    || die 64 "$checks_under_test is not an issue or PR of $repo"
  [[ "$ref_state" == open ]] || die 64 "$checks_under_test is $ref_state; the declaring issue or PR must be open"
  log "required checks under test ($checks_under_test open): dev=$dev_required integration=$integration_required"
fi
required="$integration_required"
git rev-list --first-parent "$dev_tip" >"$scratch/first-parent"
last=$(jq -r 'last.merge // empty' <<<"$state_data")
if [[ -n "$last" ]]; then
  grep -Fxq "$last" "$scratch/first-parent" || die 64 "last state SHA is not on dev first-parent history"
fi
if [[ -z "$since" ]]; then
  [[ -n "$last" ]] || die 64 "first invocation requires --since (or non-empty state)"
  since=$last
  # The most recent attempt might be red/conflicted. Include it again.
  if ! jq -e 'last.merged_at != null' <<<"$state_data" >/dev/null; then
    since=$(git rev-parse "$last^1")
  fi
fi
since=$(git rev-parse --verify "$since^{commit}") || die 64 "unknown --since commit"
grep -Fxq "$since" "$scratch/first-parent" || die 64 "--since is not on dev first-parent history"
git rev-list --first-parent --reverse "$since..$dev_tip" >"$scratch/landings"
completed=$(jq -c '[.[] | select(.merged_at != null) | .merge] | unique' <<<"$state_data")
: >"$scratch/plan"
while IFS= read -r merge; do
  if jq -e --arg merge "$merge" 'index($merge) != null' <<<"$completed" >/dev/null; then
    log 'skip recorded mirror'
    continue
  fi
  original_subject=$(git show -s --format=%s "$merge")
  # Association and subject numbers are candidates; only the PR record is
  # authoritative about this repository's merged dev landing. The merge prefix
  # and squash suffix label PRs; other subject numbers can refer to issues.
  run associated-prs gh api "repos/$repo/commits/$merge/pulls" --paginate \
    || die 64 "cannot discover original PR for commit $merge"
  candidates=$(jq -sr --arg subject "$original_subject" '
    if all(.[]; type == "array") then
      ([.[][] | .number] + [$subject |
        (capture("^Merge pull request #(?<n>[1-9][0-9]*)(?: |$)"),
         capture("\\(#(?<n>[1-9][0-9]*)\\)$")) | .n | tonumber]) | unique |
      if all(.[]; type == "number" and . > 0 and floor == .) then .[]
      else error("invalid PR candidates") end
    else error("invalid PR association") end
  ' <<<"$output") || die 64 "invalid PR association for commit $merge"
  verified=()
  while IFS= read -r candidate; do
    [[ -n "$candidate" ]] || continue
    run original-pr gh api "repos/$repo/pulls/$candidate" \
      || die 64 "cannot verify PR #$candidate for commit $merge"
    if jq -e --arg repo "$repo" --arg merge "$merge" --argjson number "$candidate" '
      .number == $number and .merged == true and .base.ref == "dev" and
      .base.repo.full_name == $repo and .merge_commit_sha == $merge
    ' <<<"$output" >/dev/null; then
      verified+=("$candidate")
    fi
  done <<<"$candidates"
  (( ${#verified[@]} == 1 )) \
    || die 64 "commit $merge must identify exactly one verified merged dev PR (found ${#verified[@]})"
  original_pr=${verified[0]}
  git check-ref-format "refs/heads/mirror/$integration/$original_pr" || die 64 "invalid mirror branch"
  printf '%s %s\n' "$merge" "$original_pr" >>"$scratch/plan"
  pending=$((pending + 1))
done <"$scratch/landings"
merge=''
log "plan dev=$dev_tip since=$since integration=$integration count=$pending required=$required version=$VERSION"
if (( dry_run )); then
  order=0
  while read -r merge original_pr; do
    order=$((order + 1))
    log "PLAN order=$order original_pr=$original_pr branch=mirror/$integration/$original_pr"
    if (( max > 0 && order >= max )); then break; fi
  done <"$scratch/plan"
  exit 0
fi

while read -r merge original_pr; do
  head='' mirror_pr=0 verdicts='[]'
  original_subject=$(git show -s --format=%s "$merge")
  branch="mirror/$integration/$original_pr"
  run refresh git fetch origin "$integration" || die 69 "cannot refresh integration"
  integration_tip=$(git rev-parse "refs/remotes/origin/$integration")
  base=$integration_tip
  run find-pr gh pr list --repo "$repo" --base "$integration" --head "$branch" \
    --state all --json number,state,headRefOid,mergedAt,mergeCommit --limit 100 || die 69 "cannot find existing mirror PR"
  # A closed, unmerged mirror is never a cursor: ignore it. Its branch, if it
  # still exists, is recovered below like any pushed mirror branch.
  prs=$(jq -c 'map(select(.state != "CLOSED"))' <<<"$output")
  count=$(jq 'length' <<<"$prs")
  (( count <= 1 )) || die 69 "multiple PRs already use $branch"
  if (( count == 1 )); then
    mirror_pr=$(jq -r '.[0].number' <<<"$prs")
    pr_state=$(jq -r '.[0].state' <<<"$prs")
    run fetch-pr git fetch origin "refs/pull/$mirror_pr/head" || die 69 "cannot fetch mirror PR head"
    head=$(git rev-parse FETCH_HEAD)
    [[ "$head" == "$(jq -r '.[0].headRefOid' <<<"$prs")" ]] || die 69 "mirror PR head changed during recovery"
    validate_head
    if [[ "$pr_state" == MERGED ]]; then
      landed=$(jq -r '.[0].mergeCommit.oid' <<<"$prs")
      git merge-base --is-ancestor "$landed" "$integration_tip" || die 69 "merged PR is outside integration history"
      read_verdicts || die 69 "cannot recover merged PR verdicts"
      record merged "$(jq -r '.[0].mergedAt' <<<"$prs")"
      pending=$((pending - 1))
      log "recovered merged mirror_pr=$mirror_pr"
      continue
    fi
  fi
  if (( mirror_pr == 0 )); then
    run find-branch git ls-remote --heads origin "refs/heads/$branch" || die 69 "cannot query mirror branch"
    remote_head=${output%%$'\t'*}
    if [[ -n "$remote_head" ]]; then
      run fetch-branch git fetch origin "refs/heads/$branch" || die 69 "cannot fetch existing mirror branch"
      head=$(git rev-parse FETCH_HEAD)
      validate_head
    else
      worktree="$scratch/tree"
      if git show-ref --verify --quiet "refs/heads/$branch"; then
        head=$(git rev-parse "refs/heads/$branch")
        if [[ "$head" != "$base" ]]; then validate_head; fi
      fi
      if ! run worktree python3 -B "$PROTOCOL" --source "$root" prepare-mirror \
        --path "$worktree" --branch "$branch" --base "$base" --merge "$merge" \
        --message "mirror: #$original_pr $original_subject"; then
        conflicts=$(git -C "$worktree" diff --name-only --diff-filter=U -z 2>/dev/null | jq -Rsc 'split("\u0000") | map(select(length > 0))') || conflicts='[]'
        if [[ "$conflicts" != '[]' ]]; then
          record conflict '' "$conflicts"
          die 65 "merge conflict paths=$conflicts; checkout retained"
        fi
        die 69 "mirror creation/publication failed; checkout retained"
      fi
      head=$(jq -er '.commit' <<<"$output") || die 69 "missing confirmed mirror commit"
      validate_head
      remove_worktree || die 69 "cannot remove mirror worktree"
    fi
    run original gh pr view "$original_pr" --repo "$repo" --json title,url || die 69 "cannot read original PR"
    title=$(jq -er '.title' <<<"$output")
    original_url=$(jq -er '.url' <<<"$output")
    body="Provenance: integration-mirror.sh v$VERSION; automated git/gh transport, no review seats or consensus; GitHub required checks supply verdicts.

Original PR: $original_url
Original dev landing: $merge
Integration base: $base
Mirror head: $head
Script version: $VERSION"
    run create gh pr create --repo "$repo" --base "$integration" --head "$branch" \
      --title "mirror #$original_pr: $title" --body "$body" || die 69 "cannot create mirror PR; rerun to recover pushed branch"
    mirror_pr=${output##*/}
    [[ "$mirror_pr" =~ ^[1-9][0-9]*$ ]] || die 69 "gh returned no mirror PR number"
  fi
  watch_checks || { record incomplete; die 69 "verdicts not settled for mirror_pr=$mirror_pr after native waits/discovery; PR left open"; }
  log "checks mirror_pr=$mirror_pr verdicts=$verdicts"
  if jq -e 'any(.[]; .bucket == "fail" or .bucket == "cancel")' <<<"$verdicts" >/dev/null; then
    record red
    die 66 "red mirror_pr=$mirror_pr left open"
  fi
  if ! jq -e --argjson required "$required" '
    ([.[].name] | unique | sort) == ($required | sort) and all(.[]; .bucket == "pass")
  ' <<<"$verdicts" >/dev/null; then
    record incomplete
    die 69 "required checks incomplete; mirror_pr=$mirror_pr left open"
  fi
  merge_attempt=0
  until run merge-pr gh pr merge "$mirror_pr" --repo "$repo" --merge --delete-branch \
    --match-head-commit "$head"; do
    merge_attempt=$((merge_attempt + 1))
    (( merge_attempt < RETRY_ATTEMPTS )) || die 69 "merge request failed after $merge_attempt attempts; rerun to recover PR state"
    # A fresh check run registered after the last watch (e.g. on PR creation):
    # wait for the verdict set to settle again before retrying the merge.
    log "merge-pr retry=$merge_attempt: re-entering the watcher"
    sleep "$RETRY_INTERVAL"
    watch_checks || { record incomplete; die 69 "verdicts not settled for mirror_pr=$mirror_pr after native waits/discovery; PR left open"; }
    if jq -e 'any(.[]; .bucket == "fail" or .bucket == "cancel")' <<<"$verdicts" >/dev/null; then
      record red
      die 66 "red mirror_pr=$mirror_pr left open"
    fi
  done
  run confirm gh pr view "$mirror_pr" --repo "$repo" --json state,mergedAt || die 69 "cannot confirm merge"
  [[ $(jq -r '.state' <<<"$output") == MERGED ]] || die 69 "mirror PR is not MERGED"
  record merged "$(jq -er '.mergedAt' <<<"$output")"
  mirrored=$((mirrored + 1))
  pending=$((pending - 1))
  log "merged original_pr=$original_pr mirror_pr=$mirror_pr"
  if (( max > 0 && mirrored >= max )); then break; fi
done <"$scratch/plan"
