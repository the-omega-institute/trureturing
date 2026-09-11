#!/usr/bin/env bash
# Mirror dev merges serially; GitHub checks supply every verdict.
# Usage: integration-mirror.sh --integration BRANCH [--since DEV_MERGE_SHA]
#          [--max N] [--state FILE] [--dry-run]
# First invocation requires --since. Later invocations resume from JSONL state
# (default: <git-common-dir>/integration-mirror/<URL-encoded-branch>.jsonl).
# Failed/conflicted entries are retried, never treated as completed cursors.
# --dry-run fetches and reads GitHub, but creates no branches, PRs or state.
# --max bounds successful merges; pending counts the remaining fetched plan.
# Exit: 0 complete/bounded/dry-run; 64 invalid input/precondition; 65 conflict;
# 66 red checks (PR left open); 69 transport/incomplete checks/unsafe recovery;
# 130 interrupted; 143 terminated (69 also when GitHub never registers checks).
# GitHub registers a new PR's check runs asynchronously; the follower polls that
# registration only (bounded), then the native watcher does all the waiting.
# Existing mirror PRs/branches are reused, never force-pushed or recreated.
# Run one follower per integration branch from a dedicated worktree. A local
# mkdir lock refuses concurrent invocations; after SIGKILL remove the stale lock
# only after confirming its recorded PID is no longer running on this host.
# Example: tools/scripts/agent/integration-mirror.sh \
#   --integration integration-regprog-0912 --since 748360e3dd32 --dry-run
# This transport does not certify workflow versions, performance, push runs or
# a stability count; those analyses and delivery to dev belong to the caller.
set -Eeuo pipefail

VERSION=2
# Check-registration wait: GitHub check-run registration latency, not capacity.
REGISTER_ATTEMPTS=20 REGISTER_INTERVAL=15
integration='' since='' state='' max=0 dry_run=0
mirrored=0 pending=0 scratch='' worktree='' lock=''
merge='' original_pr=0 mirror_pr=0 head='' base='' verdicts='[]'
repo='' output=''

log() { printf '%s merge=%s head=%s base=%s %s\n' "$(date -u +%FT%TZ)" "${merge:--}" "${head:--}" "${base:--}" "${*//$'\n'/ }"; }
die() { log "ERROR $2" >&2; exit "$1"; }
remove_worktree() {
  if [[ -n "$worktree" ]]; then
    git worktree remove --force "$worktree" >/dev/null 2>&1 || return 1
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
    rm -rf "$scratch" || rc=69
  fi
  if [[ -n "$lock" ]]; then
    rm -f "$lock/pid"
    rmdir "$lock" || rc=69
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
  local rc=0
  run verdicts gh pr checks "$mirror_pr" --repo "$repo" --required \
    --json name,state,bucket,link,workflow,event,startedAt,completedAt || rc=$?
  # gh returns 1 for failed checks and 8 for pending checks even with --json.
  case $rc in 0|1|8) ;; *) return 1 ;; esac
  verdicts=$(jq -ce 'select(type == "array")' <<<"$output") || return 1
}
wait_for_checks() {
  # No event exists for "check runs registered"; gh pr checks reports "no checks
  # reported" until then. Poll registration only, bounded, and log every probe.
  local attempt=0
  while :; do
    attempt=$((attempt + 1))
    run registered gh pr checks "$mirror_pr" --repo "$repo" --required --json name,bucket || true
    if jq -e 'type == "array" and length > 0' <<<"$output" >/dev/null 2>&1; then
      log "registered mirror_pr=$mirror_pr attempt=$attempt"
      return 0
    fi
    (( attempt < REGISTER_ATTEMPTS )) || return 1
    sleep "$REGISTER_INTERVAL"
  done
}
validate_head() {
  # Recover only a merge produced for this exact original merge, never an
  # unrelated branch that happens to occupy the deterministic branch name.
  local parents subject
  parents=$(git show -s --format=%P "$head")
  subject=$(git show -s --format=%s "$head")
  base=${parents%% *}
  [[ "$parents" == "$base $merge" && "$subject" == "mirror: #$original_pr $original_subject" ]] \
    || die 69 "existing mirror head has unexpected parents or subject"
  git merge-base --is-ancestor "$base" "$integration_tip" \
    || die 69 "existing mirror base is outside integration history"
}

while (( $# )); do
  case $1 in
    --integration|--since|--max|--state)
      (( $# >= 2 )) && [[ -n "$2" && "$2" != --* ]] || die 64 "missing value for $1"
      case $1 in
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
scratch=$(mktemp -d "${TMPDIR:-/tmp}/integration-mirror.XXXXXX") || die 64 "cannot create temporary directory"
if (( dry_run == 0 )); then
  mkdir -p "$common/integration-mirror" || die 64 "cannot create local state directory"
  lock_path="$common/integration-mirror/$branch_key.lock"
  mkdir "$lock_path" 2>/dev/null || die 64 "follower already running or stale lock: $lock_path"
  lock=$lock_path
  printf '%s\n' "$$" >"$lock/pid"
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
required=$(jq -ce 'select(.protected == true) | .protection.required_status_checks |
  ((.contexts // []) + [(.checks // [])[] | .context]) | unique |
  select(length == 3 and all(.[]; type == "string" and length > 0))' <<<"$output") \
  || die 64 "dev must require three checks"
run protection-integration gh api "repos/$repo/branches/$branch_key" || die 64 "cannot read integration protection"
jq -e --argjson required "$required" 'select(.protected == true) |
  .protection.required_status_checks |
  ((.contexts // []) + [(.checks // [])[] | .context]) | unique | . == $required' \
  <<<"$output" >/dev/null || die 64 "integration must be protected with the same three required checks as dev"
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
git rev-list --first-parent --reverse --merges "$since..$dev_tip" >"$scratch/merges"
completed=$(jq -c '[.[] | select(.merged_at != null) | .merge] | unique' <<<"$state_data")
: >"$scratch/plan"
while IFS= read -r merge; do
  if jq -e --arg merge "$merge" 'index($merge) != null' <<<"$completed" >/dev/null; then
    log 'skip recorded mirror'
    continue
  fi
  original_subject=$(git show -s --format=%s "$merge")
  [[ "$original_subject" =~ ^Merge\ pull\ request\ \#([1-9][0-9]*)\  ]] \
    || die 64 "merge subject does not identify an original PR: $original_subject"
  original_pr=${BASH_REMATCH[1]}
  git check-ref-format "refs/heads/mirror/$integration/$original_pr" || die 64 "invalid mirror branch"
  printf '%s %s\n' "$merge" "$original_pr" >>"$scratch/plan"
  pending=$((pending + 1))
done <"$scratch/merges"
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
  prs=$output
  count=$(jq 'length' <<<"$prs")
  (( count <= 1 )) || die 69 "multiple PRs already use $branch"
  if (( count == 1 )); then
    mirror_pr=$(jq -r '.[0].number' <<<"$prs")
    pr_state=$(jq -r '.[0].state' <<<"$prs")
    [[ "$pr_state" != CLOSED ]] || die 69 "mirror PR #$mirror_pr was closed without merging"
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
  else
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
        run worktree git worktree add "$worktree" "$branch" || die 69 "cannot reuse local mirror branch"
      else
        run worktree git worktree add -b "$branch" "$worktree" "origin/$integration" || die 69 "cannot create mirror worktree"
      fi
      if [[ -z "$head" || "$head" == "$base" ]]; then
        if ! run merge git -C "$worktree" merge --no-ff -m "mirror: #$original_pr $original_subject" "$merge"; then
          conflicts=$(git -C "$worktree" diff --name-only --diff-filter=U -z | jq -Rsc 'split("\u0000") | map(select(length > 0))')
          if [[ "$conflicts" != '[]' ]]; then
            git -C "$worktree" merge --abort || die 69 "cannot abort conflicted merge"
            record conflict '' "$conflicts"
            die 65 "merge conflict paths=$conflicts"
          fi
          die 69 "git merge failed without conflict paths"
        fi
        head=$(git -C "$worktree" rev-parse HEAD)
        validate_head
      fi
      run push git push origin "$head:refs/heads/$branch" || die 69 "cannot push mirror branch"
      remove_worktree || die 69 "cannot remove mirror worktree"
    fi
    run original gh pr view "$original_pr" --repo "$repo" --json title,url || die 69 "cannot read original PR"
    title=$(jq -er '.title' <<<"$output")
    original_url=$(jq -er '.url' <<<"$output")
    body="Provenance: integration-mirror.sh v$VERSION; automated git/gh transport, no review seats or consensus; GitHub required checks supply verdicts.

Original PR: $original_url
Original dev merge: $merge
Integration base: $base
Mirror head: $head
Script version: $VERSION"
    run create gh pr create --repo "$repo" --base "$integration" --head "$branch" \
      --title "mirror #$original_pr: $title" --body "$body" || die 69 "cannot create mirror PR; rerun to recover pushed branch"
    mirror_pr=${output##*/}
    [[ "$mirror_pr" =~ ^[1-9][0-9]*$ ]] || die 69 "gh returned no mirror PR number"
  fi
  wait_for_checks || { record incomplete; die 69 "no checks registered for mirror_pr=$mirror_pr within $((REGISTER_ATTEMPTS * REGISTER_INTERVAL))s; PR left open"; }
  watch_rc=0
  run watch gh pr checks "$mirror_pr" --repo "$repo" --required --watch --fail-fast || watch_rc=$?
  read_verdicts || die 69 "cannot retrieve check verdicts"
  log "checks mirror_pr=$mirror_pr watch_exit=$watch_rc verdicts=$verdicts"
  if jq -e 'any(.[]; .bucket == "fail" or .bucket == "cancel")' <<<"$verdicts" >/dev/null; then
    record red
    die 66 "red mirror_pr=$mirror_pr left open"
  fi
  if (( watch_rc != 0 )) || ! jq -e --argjson required "$required" '
    ([.[].name] | unique | sort) == ($required | sort) and all(.[]; .bucket == "pass")
  ' <<<"$verdicts" >/dev/null; then
    record incomplete
    die 69 "required checks incomplete; mirror_pr=$mirror_pr left open"
  fi
  run merge-pr gh pr merge "$mirror_pr" --repo "$repo" --merge --delete-branch \
    --match-head-commit "$head" || die 69 "merge request failed; rerun to recover PR state"
  run confirm gh pr view "$mirror_pr" --repo "$repo" --json state,mergedAt || die 69 "cannot confirm merge"
  [[ $(jq -r '.state' <<<"$output") == MERGED ]] || die 69 "mirror PR is not MERGED"
  record merged "$(jq -er '.mergedAt' <<<"$output")"
  mirrored=$((mirrored + 1))
  pending=$((pending - 1))
  log "merged original_pr=$original_pr mirror_pr=$mirror_pr"
  if (( max > 0 && mirrored >= max )); then break; fi
done <"$scratch/plan"
