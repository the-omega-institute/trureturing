#!/usr/bin/env bash
# pr-shepherd —— PR 一门器(一器一门,第Ⅵ节·器之四律①)
#
# 职责:开 PR 到 dev 并挂 auto-merge;轮询在飞 PR。BEHIND 且最新 admission
# 仅因 dev 前进导致派生物过期时,在持久 worktree 合并并走 canonical 重算链;
# 其余 BEHIND 仍由本地 gh 身份 update-branch。CONFLICTING 由本地冲突集分类。
#
# 用法:
#   pr-shepherd.sh open <head-branch> <title> [body-file]   开 PR + 挂 auto-merge
#   pr-shepherd.sh watch [interval] [max_cycles]            轮询(默认 60s × 360)
#   pr-shepherd.sh sweep                                    单轮扫描(供人工/调试)
#
# 判定只看机器字段(mergeable/mergeStateStatus/autoMergeRequest),不看输出散文。
set -euo pipefail
LOADED_SCRIPT_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)/${BASH_SOURCE[0]##*/}"
SCRIPT_PATH="${PR_SHEPHERD_CANONICAL_SCRIPT:-$LOADED_SCRIPT_PATH}"
ROOT="${PR_SHEPHERD_ROOT:-$(cd "$(dirname "$SCRIPT_PATH")/../../.." && pwd -P)}"
REMOTE="${PR_SHEPHERD_REMOTE:-origin}"
REPO="${PR_SHEPHERD_REPO:-the-omega-institute/trureturing}"
LOG="${PR_SHEPHERD_LOG:-$HOME/.pr-shepherd.log}"
PIDFILE="${PR_SHEPHERD_PID:-$HOME/.pr-shepherd.pid}"
PIDFILE_PARENT="$(cd "$(dirname "$PIDFILE")" 2>/dev/null && pwd -P)" \
  || { printf 'pr-shepherd: state directory is unavailable: %s\n' "$(dirname "$PIDFILE")" >&2; exit 1; }
PIDFILE="$PIDFILE_PARENT/${PIDFILE##*/}"
STATE_DIR="${PR_SHEPHERD_STATE:-$HOME/.pr-shepherd-state}"
CACHE_ROOT="${PR_SHEPHERD_CACHE:-$HOME/.cache/trureturing-shepherd}"
DRYRUN="${SHEPHERD_DRYRUN:-0}"
DERIVED_LEASE_TTL="${PR_SHEPHERD_LEASE_TTL_SECONDS:-14400}"
DERIVED_LEASE_TOKEN=""
DERIVED_LEASE_PR=""
DERIVED_LEASE_ACQUIRED_AT=""
COMMIT_SUBJECT="recompute derivations after dev advance (auto, pr-shepherd)"
ORIGINAL_HOME="${HOME:-/tmp}"
WATCH_LOADED_BLOB="${PR_SHEPHERD_WATCH_LOADED_BLOB:-}"
WATCH_PREVIOUS_SCRIPT="${PR_SHEPHERD_WATCH_PREVIOUS_SCRIPT:-}"
WATCH_PROCESS_START="${PR_SHEPHERD_WATCH_PROCESS_START:-}"
WATCH_OWNS_LEASE=0
WATCH_LOCK_CANDIDATE=""
WATCH_RECLAIM_REPOSITORY=""
WATCH_RECLAIM_REF=""
WATCH_RECLAIM_OID=""

GH() { LEAN4_GUARDRAILS_BYPASS=1 gh "$@"; }
log() { printf '%s %s\n' "$(date '+%F %T')" "$*" | tee -a "$LOG" >&2; }
credentialless() {
  local isolated_home="$1"
  shift
  env \
    -u GH_TOKEN \
    -u GITHUB_TOKEN \
    -u GITHUB_PAT \
    -u SSH_AUTH_SOCK \
    -u SSH_AGENT_PID \
    -u GIT_ASKPASS \
    HOME="$isolated_home" \
    GH_CONFIG_DIR="$isolated_home/gh" \
    XDG_CONFIG_HOME="$isolated_home/config" \
    XDG_CACHE_HOME="$isolated_home/cache" \
    DOTNET_CLI_HOME="$isolated_home/dotnet" \
    NUGET_PACKAGES="${NUGET_PACKAGES:-$ORIGINAL_HOME/.nuget/packages}" \
    ELAN_HOME="${ELAN_HOME:-$ORIGINAL_HOME/.elan}" \
    GIT_CONFIG_GLOBAL=/dev/null \
    GIT_CONFIG_NOSYSTEM=1 \
    GIT_TERMINAL_PROMPT=0 \
    GCM_INTERACTIVE=Never \
    "$@"
}
has_expiry_fingerprint() {
  local conclusion="$1" details_url="$2" run_id job_id tail out
  [[ "$conclusion" == "FAILURE" ]] || return 1
  case "$details_url" in
    */actions/runs/*/job/*)
      tail="${details_url#*/actions/runs/}"
      run_id="${tail%%/*}"
      job_id="${tail#*/job/}"
      job_id="${job_id%%\?*}"
      job_id="${job_id%%\#*}"
      ;;
    *) return 1 ;;
  esac
  [[ "$run_id" =~ ^[1-9][0-9]*$ ]] || return 1
  [[ "$job_id" =~ ^[1-9][0-9]*$ ]] || return 1
  if ! out="$(GH run view "$run_id" --repo "$REPO" \
    --job "$job_id" --log-failed 2>&1)"; then
    log "SWEEP admission run=$run_id job=$job_id 失败日志不可读,按普通 BEHIND 处理"
    return 1
  fi
  [[ "$out" == *"DIGEST_STATUS_INVALID"* \
    && "$out" == *"scribe-emissions"* \
    && "$out" == *"ECHO_VERIFY_INFRASTRUCTURE"* \
    && "$out" == *"residual"* ]]
}
# Conflicts a machine can settle by rebuilding rather than by reading intent. The frozen
# ledger belongs here even though it is append-only source: two lanes that each freeze a
# module always collide textually, yet the correct result is never a hand-merge of the two
# tails -- it is the dev tail plus this branch's freeze re-attested from its own Lean report,
# which run_derivation_chain does below. Without this, every D5 delivery whose sibling merges
# first stalls as "needs a semantic merge" and waits for a human that this harness has none of.
is_derived_conflict() {
  case "$1" in
    Meta/StrataLint/Generated/*|Generated/*|Evidence/D5/values.json) return 0 ;;
    Meta/StrataLint/Golden/Frozen/events.jsonl) return 0 ;;
    *) return 1 ;;
  esac
}
pr_has_derived_changes() {
  local num="$1" out path
  if ! out="$(GH pr diff "$num" --repo "$REPO" --name-only 2>&1)"; then
    log "ALERT #$num PR file classification=UNKNOWN; skip this sweep: $(printf '%s' "$out" | head -c 100)"
    return 2
  fi
  while IFS= read -r path || [[ -n "$path" ]]; do
    is_derived_conflict "$path" && return 0
  done <<< "$out"
  return 1
}

derived_lease_mtime() {
  stat -f '%m' "$1" 2>/dev/null || stat -c '%Y' "$1" 2>/dev/null
}
load_derived_lease() {
  local directory="$1" line schema="" pr="" acquired_at="" token=""
  while IFS= read -r line || [[ -n "$line" ]]; do
    case "$line" in
      schema=*) schema="${line#schema=}" ;;
      pr=*) pr="${line#pr=}" ;;
      acquired_at=*) acquired_at="${line#acquired_at=}" ;;
      token=*) token="${line#token=}" ;;
      *) return 1 ;;
    esac
  done < "$directory/owner" 2>/dev/null || return 1
  [[ "$schema" == "derived-fifo-lease-v1" \
      && "$pr" =~ ^[1-9][0-9]*$ \
      && "$acquired_at" =~ ^[0-9]+$ \
      && -n "$token" ]] || return 1
  DERIVED_LEASE_PR="$pr"
  DERIVED_LEASE_ACQUIRED_AT="$acquired_at"
  DERIVED_LEASE_TOKEN="$token"
}
create_derived_lease() {
  local num="$1" acquired_at="$2" directory="$STATE_DIR/derived-fifo.lease"
  local token="$$-$acquired_at-$RANDOM" temporary="$directory/owner.next.$$.$RANDOM"
  mkdir "$directory" 2>/dev/null || return 1
  if ! (umask 077; {
      printf 'schema=derived-fifo-lease-v1\n'
      printf 'pr=%s\n' "$num"
      printf 'acquired_at=%s\n' "$acquired_at"
      printf 'token=%s\n' "$token"
    } > "$temporary") \
      || ! mv "$temporary" "$directory/owner"; then
    rm -f "$temporary" "$directory/owner" 2>/dev/null || true
    rmdir "$directory" 2>/dev/null || true
    return 1
  fi
  DERIVED_LEASE_PR="$num"
  DERIVED_LEASE_ACQUIRED_AT="$acquired_at"
  DERIVED_LEASE_TOKEN="$token"
  log "FIFO LEASE acquired pr=#$num acquired_at=$acquired_at ttl=${DERIVED_LEASE_TTL}s"
}
acquire_derived_lease() {
  local num="$1" directory="$STATE_DIR/derived-fifo.lease" now acquired_at age
  local observed_pr observed_at observed_token stale moved_at changed=0 observed_valid=0
  [[ "$DERIVED_LEASE_TTL" =~ ^[1-9][0-9]*$ ]] \
    || { log "FIFO LEASE invalid ttl=$DERIVED_LEASE_TTL"; return 1; }
  now="$(date '+%s')"
  [[ "$now" =~ ^[0-9]+$ ]] || { log "FIFO LEASE clock unavailable"; return 1; }
  if [[ "$DRYRUN" == "1" ]]; then
    DERIVED_LEASE_PR="$num"
    DERIVED_LEASE_ACQUIRED_AT="$now"
    DERIVED_LEASE_TOKEN="dry-run"
    log "FIFO LEASE acquired pr=#$num acquired_at=$now ttl=${DERIVED_LEASE_TTL}s dry-run"
    return 0
  fi
  mkdir -p "$STATE_DIR"
  create_derived_lease "$num" "$now" && return 0

  DERIVED_LEASE_PR=""
  DERIVED_LEASE_ACQUIRED_AT=""
  DERIVED_LEASE_TOKEN=""
  if load_derived_lease "$directory"; then
    observed_valid=1
    acquired_at="$DERIVED_LEASE_ACQUIRED_AT"
  else
    acquired_at="$(derived_lease_mtime "$directory" || true)"
    [[ "$acquired_at" =~ ^[0-9]+$ ]] || {
      log "FIFO LEASE unreadable path=$directory"
      return 1
    }
    DERIVED_LEASE_PR="unknown"
    DERIVED_LEASE_ACQUIRED_AT="$acquired_at"
    DERIVED_LEASE_TOKEN="invalid"
  fi
  age=$((now - acquired_at))
  [[ "$age" -ge "$DERIVED_LEASE_TTL" ]] || return 1

  observed_pr="$DERIVED_LEASE_PR"
  observed_at="$DERIVED_LEASE_ACQUIRED_AT"
  observed_token="$DERIVED_LEASE_TOKEN"
  log "FIFO LEASE expired pr=#$observed_pr acquired_at=$observed_at ttl=${DERIVED_LEASE_TTL}s"
  stale="$directory.stale.$$.$RANDOM"
  if ! mv "$directory" "$stale" 2>/dev/null; then
    load_derived_lease "$directory" 2>/dev/null || true
    return 1
  fi
  DERIVED_LEASE_PR=""
  DERIVED_LEASE_ACQUIRED_AT=""
  DERIVED_LEASE_TOKEN=""
  if [[ "$observed_valid" == "1" ]]; then
    if ! load_derived_lease "$stale" \
        || [[ "$DERIVED_LEASE_PR" != "$observed_pr" \
            || "$DERIVED_LEASE_ACQUIRED_AT" != "$observed_at" \
            || "$DERIVED_LEASE_TOKEN" != "$observed_token" ]]; then
      changed=1
    fi
  else
    moved_at="$(derived_lease_mtime "$stale" || true)"
    if load_derived_lease "$stale" || [[ "$moved_at" != "$observed_at" ]]; then
      changed=1
    fi
  fi
  if [[ "$changed" == "1" ]]; then
    [[ -e "$directory" ]] || mv "$stale" "$directory" 2>/dev/null || true
    load_derived_lease "$directory" 2>/dev/null || true
    return 1
  fi
  rm -f "$stale/owner" "$stale"/owner.next.*
  if ! rmdir "$stale" 2>/dev/null; then
    log "FIFO LEASE stale state cannot be removed path=$stale"
    return 1
  fi
  create_derived_lease "$num" "$now" || {
    load_derived_lease "$directory" 2>/dev/null || true
    return 1
  }
}
release_derived_lease() {
  local directory="$STATE_DIR/derived-fifo.lease" token="$DERIVED_LEASE_TOKEN"
  local pr="$DERIVED_LEASE_PR"
  [[ "$DRYRUN" != "1" && -n "$token" ]] || return 0
  load_derived_lease "$directory" 2>/dev/null || return 0
  [[ "$DERIVED_LEASE_TOKEN" == "$token" ]] || return 0
  rm -f "$directory/owner"
  if ! rmdir "$directory" 2>/dev/null; then
    log "FIFO LEASE release incomplete pr=#$pr path=$directory"
  fi
  DERIVED_LEASE_TOKEN=""
}
branch_slug() {
  local branch="$1" slug digest
  slug="$(printf '%s' "$branch" | sed 's#[^A-Za-z0-9._-]#-#g')"
  digest="$(printf '%s' "$branch" | git hash-object --stdin | cut -c 1-12)"
  printf '%s-%s' "${slug:0:80}" "$digest"
}
dryrun_recalculation() {
  local num="$1" head="$2" workspace="$3"
  log "DRYRUN #$num RECALCULATE -> ensure worktree path=$workspace"
  log "DRYRUN #$num fetch origin/dev and origin/$head; verify observed OIDs"
  log "DRYRUN #$num checkout $head; merge origin/dev (derived conflicts take dev)"
  log "DRYRUN #$num run make lean-report"
  log "DRYRUN #$num run make emit"
  log "DRYRUN #$num run make ingest BASE=origin/dev"
  log "DRYRUN #$num run echo-verify --emit --base origin/dev (atomic install)"
  log "DRYRUN #$num run make emit-check BASE=origin/dev"
  log "DRYRUN #$num commit: $COMMIT_SUBJECT"
  log "DRYRUN #$num push HEAD:refs/heads/$head (non-force)"
}
prepare_worktree() {
  local num="$1" head="$2" expected_head="$3" workspace="$4" slug="$5"
  if [[ ! -e "$workspace/.git" ]]; then
    mkdir -p "$CACHE_ROOT"
    if ! make -C "$ROOT" --no-print-directory worktree \
      NAME="shepherd-$slug" PATH="$workspace" BASE="$REMOTE/dev"; then
      log "SWEEP #$num worktree 首建失败 path=$workspace"
      return 1
    fi
  fi
  if [[ "$(git -C "$workspace" rev-parse --is-inside-work-tree 2>/dev/null || true)" != "true" ]]; then
    log "SWEEP #$num cache path 不是已注册 worktree: $workspace"
    return 1
  fi
  local observed_base
  observed_base="$(git -C "$workspace" rev-parse "refs/remotes/$REMOTE/dev")"
  git -C "$workspace" merge --abort >/dev/null 2>&1 || true
  git -C "$workspace" reset --hard HEAD >/dev/null
  git -C "$workspace" clean -fd >/dev/null
  if ! git -C "$workspace" fetch --no-tags "$REMOTE" \
    "+refs/heads/dev:refs/remotes/$REMOTE/dev" \
    "+refs/heads/$head:refs/remotes/$REMOTE/$head"; then
    log "SWEEP #$num fetch 失败,放弃本轮"
    return 1
  fi
  local fetched_head fetched_base drifted=0
  fetched_head="$(git -C "$workspace" rev-parse "refs/remotes/$REMOTE/$head")"
  fetched_base="$(git -C "$workspace" rev-parse "refs/remotes/$REMOTE/dev")"
  if [[ "$fetched_head" != "$expected_head" ]]; then
    log "SWEEP #$num head 已漂移 expected=${expected_head:0:12} actual=${fetched_head:0:12},放弃本轮(下轮重试)"
    drifted=1
  fi
  if [[ "$fetched_base" != "$observed_base" ]]; then
    log "SWEEP #$num base 已漂移 expected=${observed_base:0:12} actual=${fetched_base:0:12},放弃本轮(下轮重试)"
    drifted=1
  fi
  if [[ "$drifted" -ne 0 ]]; then
    return 1
  fi
  git -C "$workspace" checkout --detach "$fetched_head" >/dev/null
}
merge_dev() {
  local num="$1" head="$2" workspace="$3" merge_rc path source_conflict=0 conflict_count=0
  set +e
  git -C "$workspace" \
    -c core.hooksPath=/dev/null \
    -c user.name=pr-shepherd \
    -c user.email=pr-shepherd@users.noreply.github.com \
    merge --no-commit --no-ff "$REMOTE/dev"
  merge_rc=$?
  set -e
  if [[ "$merge_rc" -ne 0 ]]; then
    while IFS= read -r -d '' path; do
      conflict_count=$((conflict_count + 1))
      if is_derived_conflict "$path"; then
        if git -C "$workspace" cat-file -e ":3:$path" 2>/dev/null; then
          git -C "$workspace" checkout --theirs -- "$path" \
            && git -C "$workspace" add -- "$path" || {
              git -C "$workspace" merge --abort >/dev/null 2>&1 || true
              log "SWEEP #$num 派生物冲突取 dev 侧失败 path=$path,不 push"
              return 1
            }
        elif ! git -C "$workspace" rm -f -- "$path"; then
          git -C "$workspace" merge --abort >/dev/null 2>&1 || true
          log "SWEEP #$num 派生物冲突取 dev 侧失败 path=$path,不 push"
          return 1
        fi
      else
        source_conflict=1
      fi
    done < <(git -C "$workspace" diff --name-only --diff-filter=U -z)
    if [[ "$conflict_count" -eq 0 ]]; then
      git -C "$workspace" merge --abort >/dev/null 2>&1 || true
      log "SWEEP #$num merge $REMOTE/dev 失败,不 push"
      return 1
    fi
    if [[ "$source_conflict" -ne 0 ]] \
      || git -C "$workspace" diff --name-only --diff-filter=U | grep -q .; then
      git -C "$workspace" merge --abort >/dev/null 2>&1 || true
      log "ALERT #$num CONFLICTING head=$head 需语义合并(派 shepherd lane,本器不代解)"
      return 1
    fi
  fi
  if git -C "$workspace" rev-parse -q --verify MERGE_HEAD >/dev/null; then
    git -C "$workspace" \
      -c core.hooksPath=/dev/null \
      -c user.name=pr-shepherd \
      -c user.email=pr-shepherd@users.noreply.github.com \
      commit -m "Merge $REMOTE/dev into $head (pr-shepherd)" >/dev/null
  fi
}
run_derivation_chain() {
  local num="$1" workspace="$2" projection isolated_home
  isolated_home="$(mktemp -d "${TMPDIR:-/tmp}/pr-shepherd-derivation.XXXXXXXX")"
  if ! credentialless "$isolated_home" \
    make -C "$workspace" --no-print-directory lean-report; then
    rm -rf "$isolated_home"
    log "SWEEP #$num lean-report 失败,不 push"; return 1
  fi
  if ! credentialless "$isolated_home" \
    make -C "$workspace" --no-print-directory emit; then
    rm -rf "$isolated_home"
    log "SWEEP #$num emit 失败,不 push"; return 1
  fi
  if ! credentialless "$isolated_home" \
    make -C "$workspace" --no-print-directory ingest BASE="$REMOTE/dev"; then
    rm -rf "$isolated_home"
    log "SWEEP #$num ingest 失败,不 push"; return 1
  fi
  mkdir -p "$workspace/Generated"
  projection="$workspace/Generated/.echo-residual-summary.md.pr-shepherd.$$"
  if ! (cd "$workspace" && credentialless "$isolated_home" dotnet run \
    --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj \
    --configuration Release -- echo-verify --emit --base "$REMOTE/dev") > "$projection"; then
    rm -f "$projection"
    rm -rf "$isolated_home"
    log "SWEEP #$num echo-verify --emit 失败,不 push"
    return 1
  fi
  mv "$projection" "$workspace/Generated/echo-residual-summary.md"
  # Freeze last: every step above rewrites tracked bytes, and an attestation taken before
  # them binds a blob that no longer exists. Appending here also repairs a branch that
  # produced a closed module without ever freezing it, which SL-008 otherwise rejects.
  if ! (cd "$workspace" && credentialless "$isolated_home" dotnet run \
    --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj \
    --configuration Release -- ledger-append \
    --candidate-lean-report .lake/build/stratalint/raw-lean-report.json); then
    rm -rf "$isolated_home"
    log "SWEEP #$num ledger-append 失败,不 push"; return 1
  fi
  if ! credentialless "$isolated_home" \
    make -C "$workspace" --no-print-directory emit-check BASE="$REMOTE/dev"; then
    rm -rf "$isolated_home"
    log "SWEEP #$num emit-check 失败,不 push"; return 1
  fi
  rm -rf "$isolated_home"
}
acquire_branch_lock() {
  local num="$1" lock="$2" owner="" reap="$2.reap" stale="$2.stale.$$"
  if mkdir "$lock" 2>/dev/null; then
    printf '%s' "$$" > "$lock/pid"
    return 0
  fi
  if [[ -f "$lock/pid" ]]; then owner="$(cat "$lock/pid" 2>/dev/null || true)"; fi
  if [[ "$owner" =~ ^[1-9][0-9]*$ ]] && kill -0 "$owner" 2>/dev/null; then
    log "SWEEP #$num 已有重算实例,跳过本轮 pid=$owner"
    return 1
  fi
  if [[ -z "$owner" ]]; then
    log "SWEEP #$num 重算锁无有效 owner,跳过本轮 lock=$lock"
    return 1
  fi
  if ! mkdir "$reap" 2>/dev/null; then
    log "SWEEP #$num stale 重算锁已有回收实例,跳过本轮 lock=$lock"
    return 1
  fi
  printf '%s' "$$" > "$reap/pid"
  owner=""
  if [[ -f "$lock/pid" ]]; then owner="$(cat "$lock/pid" 2>/dev/null || true)"; fi
  if [[ "$owner" =~ ^[1-9][0-9]*$ ]] && kill -0 "$owner" 2>/dev/null; then
    rm -f "$reap/pid"
    rmdir "$reap" 2>/dev/null || true
    log "SWEEP #$num 重算锁已被活跃实例接管,跳过本轮 pid=$owner"
    return 1
  fi
  if [[ -z "$owner" ]] || ! mv "$lock" "$stale" 2>/dev/null; then
    rm -f "$reap/pid"
    rmdir "$reap" 2>/dev/null || true
    log "SWEEP #$num stale 重算锁状态已变,跳过本轮 lock=$lock"
    return 1
  fi
  if ! mkdir "$lock" 2>/dev/null; then
    rm -f "$stale/pid" "$reap/pid"
    rmdir "$stale" "$reap" 2>/dev/null || true
    log "SWEEP #$num 重算锁已被另一实例接管,跳过本轮 lock=$lock"
    return 1
  fi
  printf '%s' "$$" > "$lock/pid"
  rm -f "$stale/pid" "$reap/pid"
  rmdir "$stale" "$reap" 2>/dev/null \
    || log "SWEEP #$num stale 重算锁留痕清理失败 stale=$stale reap=$reap"
}
release_branch_lock() {
  local lock="$1" owner=""
  if [[ -f "$lock/pid" ]]; then owner="$(cat "$lock/pid" 2>/dev/null || true)"; fi
  [[ "$owner" == "$$" ]] || return 0
  rm -f "$lock/pid"
  rmdir "$lock" 2>/dev/null || true
}
recalculate_pr_locked() {
  local num="$1" head="$2" expected_head="$3" workspace="$4" slug="$5"
  prepare_worktree "$num" "$head" "$expected_head" "$workspace" "$slug" \
    || return 1
  merge_dev "$num" "$head" "$workspace" || return 1
  run_derivation_chain "$num" "$workspace" || return 1
  git -C "$workspace" add -A
  if ! git -C "$workspace" \
    -c core.hooksPath=/dev/null \
    -c user.name=pr-shepherd \
    -c user.email=pr-shepherd@users.noreply.github.com \
    commit --allow-empty -m "$COMMIT_SUBJECT" >/dev/null; then
    log "SWEEP #$num 派生物 commit 失败,不 push"
    return 1
  fi
  if ! git -C "$workspace" -c core.hooksPath=/dev/null push \
    "$REMOTE" "HEAD:refs/heads/$head"; then
    log "SWEEP #$num push 非 FF 被拒,放弃本轮(下轮重试)"
    return 1
  fi
  log "SWEEP #$num RECALCULATE -> 本地 merge+regen+push 完成 head=$head"
}
recalculate_pr() {
  local num="$1" head="$2" expected_head="$3" slug workspace lock rc=0
  git check-ref-format --branch "$head" >/dev/null \
    || { log "SWEEP #$num 非法 head branch=$head,放弃本轮"; return 1; }
  slug="$(branch_slug "$head")"
  [[ -n "$slug" ]] || { log "SWEEP #$num head slug 为空,放弃本轮"; return 1; }
  workspace="$CACHE_ROOT/wt-$slug"
  if [[ "$DRYRUN" == "1" ]]; then
    dryrun_recalculation "$num" "$head" "$workspace"
    return 0
  fi
  mkdir -p "$CACHE_ROOT"
  lock="$CACHE_ROOT/lock-$slug"
  acquire_branch_lock "$num" "$lock" || return 1
  recalculate_pr_locked \
    "$num" "$head" "$expected_head" "$workspace" "$slug" || rc=$?
  release_branch_lock "$lock"
  return "$rc"
}
open_pr() {
  local head="$1" title="$2" body_file="${3:-}"
  if [[ "$DRYRUN" == "1" ]]; then
    log "DRYRUN OPEN head=$head title=$title -> create PR + arm auto-merge"
    printf '%s\n' "dry-run"
    return 0
  fi
  local args=(--repo "$REPO" --base dev --head "$head" --title "$title")
  if [[ -n "$body_file" ]]; then args+=(--body-file "$body_file"); else args+=(--fill-first); fi
  local url num
  url="$(GH pr create "${args[@]}")"
  num="${url##*/}"
  GH pr merge "$num" --repo "$REPO" --auto --merge
  log "OPEN #$num head=$head auto-merge=armed $url"
  printf '%s\n' "$num"
}
# 唤醒:armed 但 head 上无任何 check 的 PR(bot 以 GITHUB_TOKEN push 不触发
# workflow 的防递归缺口,见 retire-auto-update 尸检)。本地身份 close→reopen
# 重铸触发事件;close 会撤 auto-merge,故唤醒后必须重挂。
wake_pr() {
  local num="$1"
  GH pr close "$num" --repo "$REPO" || { log "WAKE #$num close 失败"; return 1; }
  sleep 3
  if ! GH pr reopen "$num" --repo "$REPO"; then
    sleep 5
    GH pr reopen "$num" --repo "$REPO" \
      || { log "ALERT #$num reopen 两次失败,PR 留在 closed,须立即恢复"; return 1; }
  fi
  GH pr merge "$num" --repo "$REPO" --auto --merge \
    || log "WAKE #$num re-arm auto-merge 失败(需会话补挂)"
  log "WAKE #$num close/reopen 完成,auto-merge 重挂"
}
# GitHub's rate_limit endpoint is itself exempt from rate limiting, so reading the
# remaining budget costs nothing. A sweep does not: the PR listing alone is a GraphQL
# query over up to a thousand pull requests, and a long-running watch repeats it every
# interval. Burning the last of the budget here starves the engine that shares this
# account, which is how it died repeatedly on this host.
graphql_remaining() {
  gh api rate_limit --jq '.resources.graphql.remaining' 2>/dev/null
}
update_pr_branch() {
  local num="$1" out
  if [[ "$DRYRUN" == "1" ]]; then
    log "DRYRUN #$num BEHIND -> update-branch(本地身份,checks 会触发)"
  elif out="$(GH api -X PUT "repos/$REPO/pulls/$num/update-branch" 2>&1)"; then
    log "SWEEP #$num BEHIND -> update-branch(本地身份,checks 会触发)"
  else
    log "SWEEP #$num update-branch 失败: $(printf '%s' "$out" | head -c 100)"
    return 1
  fi
}
sweep() {
  local remaining floor="${PR_SHEPHERD_GRAPHQL_FLOOR:-200}"
  remaining="$(graphql_remaining)" || remaining=""
  # An unreadable budget must not stall the shepherd: if gh is broken the sweep will
  # report that on its own, and a guard that fails closed here would lock the very
  # recalculation that unblocks the queue.
  if [[ "$remaining" =~ ^[0-9]+$ && "$floor" =~ ^[0-9]+$ && "$remaining" -lt "$floor" ]]; then
    log "SWEEP 跳过:GraphQL 余额 $remaining 低于下限 $floor,让配额恢复"
    return 0
  fi
  [[ "$DRYRUN" == "1" ]] || mkdir -p "$STATE_DIR"
  local recalculated=" " derived_queue_head="" derived="UNKNOWN" expired=0
  GH pr list --repo "$REPO" --state open --limit 1000 \
    --json number,mergeable,mergeStateStatus,autoMergeRequest,headRefName,headRefOid,baseRefOid,statusCheckRollup \
    --jq '.[] | select(.autoMergeRequest != null) | ((.statusCheckRollup | map(select(.__typename == "CheckRun" and .name == "Content-addressed dev baseline admission")) | sort_by(.startedAt // .completedAt // "") | last) // {}) as $admission | [.number,.mergeable,.mergeStateStatus,.headRefName,.headRefOid,.baseRefOid,(.statusCheckRollup|length),($admission.conclusion // "-"),($admission.detailsUrl // "-")] | @tsv' |
  LC_ALL=C sort -t $'\t' -k1,1n |
  while IFS=$'\t' read -r num mergeable mstate head head_oid base_oid checks admission_conclusion admission_url; do
    case "$mergeable:$mstate" in
      MERGEABLE:BEHIND|CONFLICTING:*)
        derived="UNKNOWN"
        expired=0
        if pr_has_derived_changes "$num"; then
          derived=1
        elif [[ "$?" == "1" ]]; then
          derived=0
        else
          continue
        fi
        if [[ "$mergeable" == "MERGEABLE" ]] \
          && has_expiry_fingerprint "$admission_conclusion" "$admission_url"; then
          expired=1
        fi
        if [[ "$derived" == "1" && ( "$mergeable" == "MERGEABLE" || "$mstate" == "DIRTY" ) ]]; then
          if [[ -n "$derived_queue_head" ]]; then
            log "SWEEP #$num derived FIFO waiting head=#$derived_queue_head"
            continue
          fi
          derived_queue_head="$num"
          if ! acquire_derived_lease "$num"; then
            log "SWEEP #$num derived FIFO waiting lease_pr=#${DERIVED_LEASE_PR:-unknown} acquired_at=${DERIVED_LEASE_ACQUIRED_AT:-unknown}"
            continue
          fi
          if [[ "$mergeable" == "CONFLICTING" || "$expired" == "1" ]]; then
            recalculated+="$num "
            recalculate_pr "$num" "$head" "$head_oid" || true
          else
            update_pr_branch "$num" || true
          fi
          release_derived_lease
        elif [[ "$mergeable" == "CONFLICTING" || "$expired" == "1" ]]; then
          if [[ "$recalculated" == *" $num "* ]]; then
            log "SWEEP #$num 本轮已重算一次,跳过重复项"
            continue
          fi
          recalculated+="$num "
          recalculate_pr "$num" "$head" "$head_oid" || true
        else
          update_pr_branch "$num" || true
        fi
        ;;
      *)
        # BLOCKED/UNKNOWN 且 head 无任何 check:多为 bot push 死锁。
        # 同一 head 连续两轮观察为空才唤醒,防 checks 挂载延迟误触。
        if [[ "$DRYRUN" == "1" ]]; then
          if [[ "$checks" == "0" && ( "$mstate" == "BLOCKED" || "$mstate" == "UNKNOWN" ) ]]; then
            log "DRYRUN #$num head=$head_oid 无 checks -> 观察/唤醒均抑制"
          fi
          continue
        fi
        marker="$STATE_DIR/nochecks-$num"
        if [[ "$checks" == "0" && ( "$mstate" == "BLOCKED" || "$mstate" == "UNKNOWN" ) ]]; then
          if [[ -f "$marker" && "$(cat "$marker")" == "$head_oid" ]]; then
            wake_pr "$num" && rm -f "$marker"
          else
            printf '%s' "$head_oid" > "$marker"
            log "SWEEP #$num head=$head_oid 无 checks,标记观察(下轮仍空即唤醒)"
          fi
        else
          rm -f "$marker" 2>/dev/null || true
        fi
        ;;
    esac
  done
}
armed_pr_count() {
  local out
  if ! out="$(GH pr list --repo "$REPO" --state open --limit 1000 \
    --json autoMergeRequest \
    --jq '[.[] | select(.autoMergeRequest != null)] | length' 2>&1)"; then
    log "WATCH open auto-merge armed PR 查询失败: $(printf '%s' "$out" | head -c 100)"
    return 1
  fi
  if [[ ! "$out" =~ ^[0-9]+$ ]]; then
    log "WATCH open auto-merge armed PR 计数非法: $(printf '%s' "$out" | head -c 100)"
    return 1
  fi
  printf '%s\n' "$out"
}

watch_process_start() {
  LC_ALL=C ps -p "$1" -o lstart= 2>/dev/null \
    | sed 's/^[[:space:]]*//;s/[[:space:]]*$//'
}
# 0=live owner, 1=recorded owner is provably gone, 2=identity cannot be verified.
watch_lease_owner_status() {
  local owner_file="${1:-$PIDFILE.lock}" line pid process_start canonical_script
  local actual_start="" process_status
  local -a lines=()
  WATCH_OWNER_PID=""
  WATCH_OWNER_PROCESS_START=""
  WATCH_OWNER_CANONICAL_SCRIPT=""
  [[ -f "$owner_file" && -r "$owner_file" ]] || return 2
  while IFS= read -r line || [[ -n "$line" ]]; do
    lines+=("$line")
  done < "$owner_file"
  [[ "${#lines[@]}" -eq 4 \
      && "${lines[0]}" == "schema=pr-watch-owner-v1" \
      && "${lines[1]}" =~ ^pid=([1-9][0-9]*)$ \
      && "${lines[2]}" == process_start=* \
      && "${lines[3]}" == canonical_script=/* ]] || return 2
  pid="${BASH_REMATCH[1]}"
  process_start="${lines[2]#process_start=}"
  canonical_script="${lines[3]#canonical_script=}"
  [[ -n "$process_start" && -n "$canonical_script" ]] || return 2
  WATCH_OWNER_PID="$pid"
  WATCH_OWNER_PROCESS_START="$process_start"
  WATCH_OWNER_CANONICAL_SCRIPT="$canonical_script"
  if actual_start="$(watch_process_start "$pid")"; then
    process_status=0
  else
    process_status=$?
    actual_start=""
  fi
  if kill -0 "$pid" 2>/dev/null; then
    [[ "$process_status" == "0" && "$actual_start" == "$process_start" ]] \
      && return 0
    return 2
  fi
  if [[ "$process_status" == "1" && -z "$actual_start" ]]; then
    return 1
  fi
  if [[ "$process_status" == "0" && -n "$actual_start" \
      && "$actual_start" != "$process_start" ]]; then
    return 1
  fi
  return 2
}
write_watch_owner() {
  local target="$1"
  (set -o noclobber; {
      printf 'schema=pr-watch-owner-v1\n'
      printf 'pid=%s\n' "$$"
      printf 'process_start=%s\n' "$WATCH_PROCESS_START"
      printf 'canonical_script=%s\n' "$SCRIPT_PATH"
    } > "$target") 2>/dev/null
}
clear_watch_reclaim() {
  local rc=0
  if [[ -n "$WATCH_RECLAIM_REF" && -n "$WATCH_RECLAIM_OID" ]]; then
    if ! git -C "$WATCH_RECLAIM_REPOSITORY" update-ref -d \
        "$WATCH_RECLAIM_REF" "$WATCH_RECLAIM_OID" 2>/dev/null; then
      log "WATCH lease unavailable: reclaim claim release failed"
      rc=1
    fi
  fi
  WATCH_RECLAIM_REPOSITORY=""
  WATCH_RECLAIM_REF=""
  WATCH_RECLAIM_OID=""
  return "$rc"
}
acquire_watch_reclaim_claim() {
  local candidate="$1" repository candidate_oid observed_oid observed_status attempt rc observed
  local zero=0000000000000000000000000000000000000000
  repository="$PIDFILE.reclaim.git"
  if ! git init --bare -q "$repository" 2>/dev/null; then
    log "WATCH lease unavailable: reclaim repository cannot be initialized"; return 1
  fi
  [[ "$(git -C "$repository" rev-parse --is-bare-repository 2>/dev/null)" == "true" ]] \
    || { log "WATCH lease unavailable: reclaim repository is invalid"; return 1; }
  candidate_oid="$(git -C "$repository" hash-object -w "$candidate" 2>/dev/null)" \
    || candidate_oid=""
  [[ "$candidate_oid" =~ ^[0-9a-f]{40}$ ]] \
    || { log "WATCH lease unavailable: reclaim identity cannot be stored"; return 1; }
  WATCH_RECLAIM_REF="refs/trureturing/pr-watch-reclaim"
  for attempt in 1 2 3; do
    if observed_oid="$(git -C "$repository" rev-parse --verify --quiet \
        "$WATCH_RECLAIM_REF" 2>/dev/null)"; then
      observed="$candidate.observed"
      if ! git -C "$repository" cat-file blob "$observed_oid" \
          > "$observed" 2>/dev/null; then
        rm -f "$observed"
        log "WATCH lease unavailable: reclaim identity is unverifiable"
        return 1
      fi
      watch_lease_owner_status "$observed" && observed_status=0 || observed_status=$?
      rm -f "$observed"
      case "$observed_status" in
        0) log "WATCH lease unavailable: ownership reclamation already in progress"; return 1 ;;
        2) log "WATCH lease unavailable: reclaim identity is unverifiable"; return 1 ;;
      esac
    else
      rc=$?
      [[ "$rc" == "1" ]] \
        || { log "WATCH lease unavailable: reclaim claim cannot be read"; return 1; }
      observed_oid="$zero"
    fi
    if git -C "$repository" update-ref "$WATCH_RECLAIM_REF" \
        "$candidate_oid" "$observed_oid" 2>/dev/null; then
      WATCH_RECLAIM_REPOSITORY="$repository"
      WATCH_RECLAIM_OID="$candidate_oid"
      return 0
    fi
  done
  log "WATCH lease unavailable: reclaim claim changed repeatedly"
  return 1
}

acquire_watch_lease() {
  local lock="$PIDFILE.lock" status replacement
  WATCH_PROCESS_START="$(watch_process_start "$$")" || WATCH_PROCESS_START=""
  [[ -n "$WATCH_PROCESS_START" ]] \
    || { log "WATCH identity unavailable: process start cannot be read"; return 1; }
  if [[ -e "$PIDFILE" && ! -f "$lock" ]]; then
    log "WATCH lease unavailable: state exists without ownership lease path=$PIDFILE"
    return 1
  fi
  WATCH_LOCK_CANDIDATE="$lock.next.$$.$RANDOM"
  if ! write_watch_owner "$WATCH_LOCK_CANDIDATE"; then
    WATCH_LOCK_CANDIDATE=""
    log "WATCH lease unavailable: owner identity cannot be written"
    return 1
  fi
  if ln "$WATCH_LOCK_CANDIDATE" "$lock" 2>/dev/null; then
    rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
    WATCH_LOCK_CANDIDATE=""
    WATCH_OWNS_LEASE=1
    rm -f "$PIDFILE" 2>/dev/null || true
    return 0
  fi
  [[ -f "$lock" ]] \
    || { log "WATCH lease unavailable: owner identity is absent"; return 1; }
  acquire_watch_reclaim_claim "$WATCH_LOCK_CANDIDATE" || return 1
  rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
  WATCH_LOCK_CANDIDATE="$lock.observed.$$.$RANDOM"
  if ! cp "$lock" "$WATCH_LOCK_CANDIDATE" 2>/dev/null \
      || ! cmp -s "$lock" "$WATCH_LOCK_CANDIDATE"; then
    clear_watch_reclaim || true
    log "WATCH lease unavailable: ownership changed during reclamation"
    return 1
  fi
  if watch_lease_owner_status "$WATCH_LOCK_CANDIDATE"; then
    status=0
  else
    status=$?
  fi
  case "$status" in
    0)
      clear_watch_reclaim || true
      log "WATCH already running with a verified lease"
      return 1
      ;;
    2)
      clear_watch_reclaim || true
      log "WATCH lease unavailable: ownership identity is unverifiable"
      return 1
      ;;
  esac
  rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
  WATCH_LOCK_CANDIDATE=""
  replacement="$lock.next.$$.$RANDOM"
  WATCH_LOCK_CANDIDATE="$replacement"
  if ! write_watch_owner "$replacement" || ! mv "$replacement" "$lock"; then
    rm -f "$replacement" 2>/dev/null || true
    WATCH_LOCK_CANDIDATE=""
    clear_watch_reclaim || true
    log "WATCH lease unavailable: reclaimed owner identity cannot be written"
    return 1
  fi
  WATCH_LOCK_CANDIDATE=""
  WATCH_OWNS_LEASE=1
  rm -f "$PIDFILE" 2>/dev/null || true
  clear_watch_reclaim || return 1
  return 0
}
watch_lease_belongs_to_current_process() {
  watch_lease_owner_status "$PIDFILE.lock" || return 1
  [[ "$WATCH_OWNER_PID" == "$$" && -n "$WATCH_PROCESS_START" \
      && "$WATCH_OWNER_PROCESS_START" == "$WATCH_PROCESS_START" \
      && "$WATCH_OWNER_CANONICAL_SCRIPT" == "$SCRIPT_PATH" ]]
}

publish_watch_identity() {
  local interval="$1" max="$2" cycle="$3" actual_blob temporary
  actual_blob="$(git hash-object "$LOADED_SCRIPT_PATH" 2>/dev/null)" || actual_blob=""
  if [[ ! "$WATCH_LOADED_BLOB" =~ ^[0-9a-f]{40}$ \
      || "$actual_blob" != "$WATCH_LOADED_BLOB" ]]; then
    log "WATCH identity mismatch expected=${WATCH_LOADED_BLOB:-missing} actual=${actual_blob:-unreadable}"
    return 1
  fi
  watch_lease_belongs_to_current_process \
    || { log "WATCH lease lost before identity publication"; return 1; }
  temporary="$PIDFILE.next.$$.$RANDOM"
  umask 077
  if ! {
      printf 'schema=pr-watch-state-v1\n'
      printf 'pid=%s\n' "$$"
      printf 'process_start=%s\n' "$WATCH_PROCESS_START"
      printf 'canonical_script=%s\n' "$SCRIPT_PATH"
      printf 'loaded_script=%s\n' "$LOADED_SCRIPT_PATH"
      printf 'loaded_blob=%s\n' "$WATCH_LOADED_BLOB"
      printf 'interval=%s\n' "$interval"
      printf 'max_cycles=%s\n' "$max"
      printf 'cycle=%s\n' "$cycle"
    } > "$temporary" \
      || ! mv "$temporary" "$PIDFILE"; then
    rm -f "$temporary" 2>/dev/null || true
    log "WATCH identity publication failed path=$PIDFILE"
    return 1
  fi
  log "WATCH cycle=$cycle loaded_script_blob=$WATCH_LOADED_BLOB"
}
remove_watch_snapshot() {
  local snapshot="$1" snapshot_directory temporary_directory
  [[ "${snapshot##*/}" == pr-shepherd-watch.* ]] || return 0
  snapshot_directory="$(cd "$(dirname "$snapshot")" 2>/dev/null && pwd -P)" || return 0
  temporary_directory="$(cd "${TMPDIR:-/tmp}" 2>/dev/null && pwd -P)" || return 0
  [[ "$snapshot_directory" == "$temporary_directory" ]] \
    && rm -f "$snapshot" 2>/dev/null || true
}
reload_watch() {
  local interval="$1" max="$2" next_cycle="$3" snapshot blob rc
  local script_repository script_relative tracked_blob
  if ! snapshot="$(mktemp "${TMPDIR:-/tmp}/pr-shepherd-watch.XXXXXXXX")"; then
    log "WATCH reload unavailable: immutable snapshot cannot be allocated"
    return 1
  fi
  if ! cp "$SCRIPT_PATH" "$snapshot" 2>/dev/null \
      || ! chmod 0400 "$snapshot" \
      || ! /bin/bash -n "$snapshot" \
      || ! blob="$(git hash-object "$snapshot" 2>/dev/null)"; then
    rm -f "$snapshot" 2>/dev/null || true
    log "WATCH reload unavailable path=$SCRIPT_PATH"
    return 1
  fi
  script_repository="$(git -C "$(dirname "$SCRIPT_PATH")" rev-parse --show-toplevel 2>/dev/null)" \
    || script_repository=""
  script_relative="$(git -C "$script_repository" ls-files --full-name \
    --error-unmatch -- "$SCRIPT_PATH" 2>/dev/null)" || script_relative=""
  tracked_blob="$(git -C "$script_repository" \
    rev-parse "HEAD:$script_relative" 2>/dev/null)" || tracked_blob=""
  if [[ -z "$script_repository" || -z "$script_relative" \
      || ! "$tracked_blob" =~ ^[0-9a-f]{40}$ || "$blob" != "$tracked_blob" ]]; then
    rm -f "$snapshot" 2>/dev/null || true
    log "WATCH reload blocked: canonical script does not match tracked HEAD path=$SCRIPT_PATH"
    return 1
  fi
  if [[ -n "$WATCH_LOADED_BLOB" && "$WATCH_LOADED_BLOB" != "$blob" ]]; then
    log "WATCH SCRIPT CHANGED previous_blob=$WATCH_LOADED_BLOB current_blob=$blob"
  fi
  export PR_SHEPHERD_CANONICAL_SCRIPT="$SCRIPT_PATH"
  export PR_SHEPHERD_ROOT="$ROOT"
  export PR_SHEPHERD_WATCH_LOADED_BLOB="$blob"
  export PR_SHEPHERD_WATCH_PREVIOUS_SCRIPT="$LOADED_SCRIPT_PATH"
  export PR_SHEPHERD_WATCH_PROCESS_START="$WATCH_PROCESS_START"
  export PR_SHEPHERD_WATCH_CYCLE="$next_cycle"
  if exec /bin/bash "$snapshot" watch "$interval" "$max"; then
    return 0
  else
    rc=$?
  fi
  rm -f "$snapshot" 2>/dev/null || true
  log "WATCH reload exec failed path=$snapshot exit=$rc"
  return "$rc"
}
cleanup_watch() {
  [[ -z "$WATCH_LOCK_CANDIDATE" ]] \
    || rm -f "$WATCH_LOCK_CANDIDATE" 2>/dev/null || true
  clear_watch_reclaim || true
  remove_watch_snapshot "$LOADED_SCRIPT_PATH"
}
watch() {
  local interval="${1:-60}" max="${2:-360}" cycle armed
  [[ "$interval" =~ ^(0|[1-9][0-9]*)$ && "$max" =~ ^[1-9][0-9]*$ ]] \
    || { log "WATCH invalid interval or max_cycles (interval=$interval max_cycles=$max)"; return 2; }
  if [[ -z "$WATCH_LOADED_BLOB" ]]; then
    trap cleanup_watch EXIT
    trap 'exit 143' TERM
    trap 'exit 130' INT
    acquire_watch_lease || return
    reload_watch "$interval" "$max" 1
    return
  fi
  WATCH_OWNS_LEASE=1
  trap cleanup_watch EXIT
  trap 'exit 143' TERM
  trap 'exit 130' INT
  cycle="${PR_SHEPHERD_WATCH_CYCLE:-}"
  [[ "$cycle" =~ ^[1-9][0-9]*$ && "$cycle" -le "$max" ]] \
    || { log "WATCH reload rejected invalid cycle=${cycle:-missing}"; return 2; }
  watch_lease_belongs_to_current_process \
    || { log "WATCH reload rejected: verified lease is absent"; return 1; }
  publish_watch_identity "$interval" "$max" "$cycle" || return
  remove_watch_snapshot "$WATCH_PREVIOUS_SCRIPT"
  WATCH_PREVIOUS_SCRIPT=""
  if [[ "$cycle" == "1" ]]; then
    log "WATCH start interval=${interval}s max_cycles=${max} pid=$$"
  else
    log "WATCH reloaded cycle=$cycle interval=${interval}s max_cycles=${max} pid=$$"
  fi
  sweep || log "SWEEP cycle=$cycle error (continuing)"
  sleep "$interval"
  if [[ "$cycle" -lt "$max" ]]; then
    reload_watch "$interval" "$max" "$((cycle + 1))"
    return
  fi
  if ! armed="$(armed_pr_count)"; then
    log "WATCH renew(${max} 轮耗尽,armed PR 状态不可判,保守重启计数)"
    reload_watch "$interval" "$max" 1
    return
  fi
  if [[ "$armed" -gt 0 ]]; then
    log "WATCH renew(${max} 轮耗尽,仍有 open 且 auto-merge armed PR,重启计数)"
    reload_watch "$interval" "$max" 1
    return
  fi
  log "WATCH end(${max} 轮耗尽,无 open auto-merge armed PR)"
}

case "${1:-}" in
  open)  shift; open_pr "$@" ;;
  watch) shift; watch "$@" ;;
  sweep) sweep ;;
  *) sed -n '2,15p' "$0"; exit 2 ;;
esac
