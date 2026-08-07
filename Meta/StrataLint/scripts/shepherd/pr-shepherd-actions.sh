# PR open/recalculation actions sourced only by the canonical pr-shepherd entrypoint.
run_credentialless_bounded() {
  local step="$1" isolated_home="$2"
  shift 2
  run_bounded build "$step" "$BUILD_TIMEOUT_SECONDS" env \
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
set_bounded_failure() {
  local step="$1"
  LAST_FAILURE_CLASS="$step.${LAST_BOUNDED_RESULT:-exit}"
  LAST_FAILURE_EXIT="${LAST_BOUNDED_EXIT:-1}"
}
set_exit_failure() {
  LAST_FAILURE_CLASS="$1.exit"
  LAST_FAILURE_EXIT="${2:-1}"
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
  if ! GH_CAPTURE out run-view run view "$run_id" --repo "$REPO" \
      --job "$job_id" --log-failed; then
    set_bounded_failure run-view
    log "SWEEP admission run=$run_id job=$job_id 失败日志不可读,按普通 BEHIND 处理"
    return 2
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
    if ! run_bounded build worktree "$BUILD_TIMEOUT_SECONDS" \
      make -C "$ROOT" --no-print-directory worktree \
        NAME="shepherd-$slug" PATH="$workspace" BASE="$REMOTE/dev"; then
      set_bounded_failure worktree
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
  if ! run_bounded git fetch "$GIT_TIMEOUT_SECONDS" \
    git -C "$workspace" fetch --no-tags "$REMOTE" \
    "+refs/heads/dev:refs/remotes/$REMOTE/dev" \
  "+refs/heads/$head:refs/remotes/$REMOTE/$head"; then
    set_bounded_failure fetch
    LAST_FAILURE_DISPOSITION=infra
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
    LAST_FAILURE_DISPOSITION=retry
    LAST_FAILURE_CLASS=""
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
  if ! run_credentialless_bounded lean-report "$isolated_home" \
    make -C "$workspace" --no-print-directory lean-report; then
    set_bounded_failure lean-report
    rm -rf "$isolated_home"
    log "SWEEP #$num lean-report 失败,不 push"; return 1
  fi
  if ! run_credentialless_bounded emit "$isolated_home" \
    make -C "$workspace" --no-print-directory emit; then
    set_bounded_failure emit
    rm -rf "$isolated_home"
    log "SWEEP #$num emit 失败,不 push"; return 1
  fi
  if ! run_credentialless_bounded ingest "$isolated_home" \
    make -C "$workspace" --no-print-directory ingest BASE="$REMOTE/dev"; then
    set_bounded_failure ingest
    rm -rf "$isolated_home"
    log "SWEEP #$num ingest 失败,不 push"; return 1
  fi
  mkdir -p "$workspace/Generated"
  projection="$(mktemp "${TMPDIR:-/tmp}/pr-shepherd-projection.XXXXXXXX")"
  if ! run_credentialless_bounded echo-verify "$isolated_home" \
    /bin/bash -c 'cd "$1"; shift; exec "$@"' pr-shepherd-workspace "$workspace" \
      dotnet run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj \
      --configuration Release -- echo-verify --emit --base "$REMOTE/dev" \
      > "$projection"; then
    set_bounded_failure echo-verify
    rm -f "$projection"
    rm -rf "$isolated_home"
    log "SWEEP #$num echo-verify --emit 失败,不 push"
    return 1
  fi
  mv "$projection" "$workspace/Generated/echo-residual-summary.md"
  # Freeze last: every step above rewrites tracked bytes, and an attestation taken before
  # them binds a blob that no longer exists. Appending here also repairs a branch that
  # produced a closed module without ever freezing it, which SL-008 otherwise rejects.
  if ! run_credentialless_bounded ledger-append "$isolated_home" \
    /bin/bash -c 'cd "$1"; shift; exec "$@"' pr-shepherd-workspace "$workspace" \
      dotnet run --project Meta/StrataLint/StrataLint.Cli/StrataLint.Cli.csproj \
      --configuration Release -- ledger-append \
      --candidate-lean-report .lake/build/stratalint/raw-lean-report.json; then
    set_bounded_failure ledger-append
    rm -rf "$isolated_home"
    log "SWEEP #$num ledger-append 失败,不 push"; return 1
  fi
  if ! run_credentialless_bounded emit-check "$isolated_home" \
    make -C "$workspace" --no-print-directory emit-check BASE="$REMOTE/dev"; then
    set_bounded_failure emit-check
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
    || { [[ "$LAST_FAILURE_DISPOSITION" != poison || -n "$LAST_FAILURE_CLASS" ]] \
      || set_exit_failure prepare-worktree; return 1; }
  merge_dev "$num" "$head" "$workspace" \
    || { [[ -n "$LAST_FAILURE_CLASS" ]] || set_exit_failure merge-dev; return 1; }
  run_derivation_chain "$num" "$workspace" || return 1
  git -C "$workspace" add -A
  if ! git -C "$workspace" \
    -c core.hooksPath=/dev/null \
    -c user.name=pr-shepherd \
    -c user.email=pr-shepherd@users.noreply.github.com \
    commit --allow-empty -m "$COMMIT_SUBJECT" >/dev/null; then
    set_exit_failure commit
    log "SWEEP #$num 派生物 commit 失败,不 push"
    return 1
  fi
  if ! run_bounded git push "$GIT_TIMEOUT_SECONDS" \
    git -C "$workspace" -c core.hooksPath=/dev/null push \
  "$REMOTE" "HEAD:refs/heads/$head"; then
    set_bounded_failure push
    LAST_FAILURE_DISPOSITION=retry
    log "SWEEP #$num push 非 FF 被拒,放弃本轮(下轮重试)"
    return 1
  fi
  log "SWEEP #$num RECALCULATE -> 本地 merge+regen+push 完成 head=$head"
}
recalculate_pr() {
  local num="$1" head="$2" expected_head="$3" slug workspace lock rc=0
  LAST_FAILURE_CLASS=""
  LAST_FAILURE_EXIT=""
  LAST_FAILURE_DISPOSITION=poison
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
  acquire_branch_lock "$num" "$lock" \
    || { LAST_FAILURE_DISPOSITION=retry; return 1; }
  ACTIVE_BRANCH_LOCK="$lock"
  recalculate_pr_locked \
    "$num" "$head" "$expected_head" "$workspace" "$slug" || rc=$?
  release_branch_lock "$lock"
  ACTIVE_BRANCH_LOCK=""
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
  GH_AS_APP_CAPTURE url pr-create pr create "${args[@]}"
  num="${url##*/}"
  GH pr-auto-merge pr merge "$num" --repo "$REPO" --auto --merge
  log "OPEN #$num head=$head auto-merge=armed $url"
  printf '%s\n' "$num"
}
# 唤醒:armed 但 head 上无任何 check 的 PR(bot 以 GITHUB_TOKEN push 不触发
# workflow 的防递归缺口,见 retire-auto-update 尸检)。本地身份 close→reopen
# 重铸触发事件;close 会撤 auto-merge,故唤醒后必须重挂。
wake_pr() {
  local num="$1"
  GH wake-close pr close "$num" --repo "$REPO" || { log "WAKE #$num close 失败"; return 1; }
  sleep "$WAKE_SLEEP_SECONDS"
  if ! GH wake-reopen pr reopen "$num" --repo "$REPO"; then
    sleep "$WAKE_REOPEN_RETRY_SLEEP_SECONDS"
    GH wake-reopen pr reopen "$num" --repo "$REPO" \
      || { log "ALERT #$num reopen 两次失败,PR 留在 closed,须立即恢复"; return 1; }
  fi
  GH wake-rearm pr merge "$num" --repo "$REPO" --auto --merge \
    || log "WAKE #$num re-arm auto-merge 失败(需会话补挂)"
  log "WAKE #$num close/reopen 完成,auto-merge 重挂"
}
# GitHub's rate_limit endpoint is itself exempt from rate limiting, so reading the
# remaining budget costs nothing. A sweep does not: the PR listing alone is a GraphQL
# query over up to a thousand pull requests, and a long-running watch repeats it every
# interval. Burning the last of the budget here starves the engine that shares this
# account, which is how it died repeatedly on this host.
graphql_remaining() {
  local out
  GH_CAPTURE out graphql-remaining api rate_limit --jq '.resources.graphql.remaining' \
    || return 1
  printf '%s\n' "$out"
}
armed_pr_count() {
  local out
  if ! GH_CAPTURE out armed-pr-count pr list --repo "$REPO" --state open --limit 1000 \
    --json autoMergeRequest \
    --jq '[.[] | select(.autoMergeRequest != null)] | length'; then
    log "WATCH open auto-merge armed PR 查询失败: $(printf '%s' "$out" | head -c 100)"
    return 1
  fi
  if [[ ! "$out" =~ ^[0-9]+$ ]]; then
    log "WATCH open auto-merge armed PR 计数非法: $(printf '%s' "$out" | head -c 100)"
    return 1
  fi
  printf '%s\n' "$out"
}
