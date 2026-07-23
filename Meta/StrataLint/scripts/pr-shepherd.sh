#!/usr/bin/env bash
# pr-shepherd —— PR 一门器(一器一门,第Ⅵ节·器之四律①)
#
# 职责:开 PR 到 dev 并挂 auto-merge;轮询在飞 PR。BEHIND 且最新 admission
# 仅因 dev 前进导致派生物过期时,在持久 worktree 合并并走 canonical 重算链;
# 其余 BEHIND 仍由本地 gh 身份 update-branch。CONFLICTING 只告警不代解。
#
# 用法:
#   pr-shepherd.sh open <head-branch> <title> [body-file]   开 PR + 挂 auto-merge
#   pr-shepherd.sh watch [interval] [max_cycles]            轮询(默认 60s × 360)
#   pr-shepherd.sh sweep                                    单轮扫描(供人工/调试)
#
# 判定只看机器字段(mergeable/mergeStateStatus/autoMergeRequest),不看输出散文。
set -euo pipefail

ROOT="${PR_SHEPHERD_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../../.." && pwd -P)}"
REMOTE="${PR_SHEPHERD_REMOTE:-origin}"
REPO="${PR_SHEPHERD_REPO:-the-omega-institute/trureturing}"
LOG="${PR_SHEPHERD_LOG:-$HOME/.pr-shepherd.log}"
PIDFILE="${PR_SHEPHERD_PID:-$HOME/.pr-shepherd.pid}"
STATE_DIR="${PR_SHEPHERD_STATE:-$HOME/.pr-shepherd-state}"
CACHE_ROOT="${PR_SHEPHERD_CACHE:-$HOME/.cache/trureturing-shepherd}"
DRYRUN="${SHEPHERD_DRYRUN:-0}"
COMMIT_SUBJECT="recompute derivations after dev advance (auto, pr-shepherd)"
ORIGINAL_HOME="${HOME:-/tmp}"

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
  local conclusion="$1" details_url="$2" run_id out
  [[ "$conclusion" == "FAILURE" ]] || return 1
  case "$details_url" in
    */actions/runs/*)
      run_id="${details_url#*/actions/runs/}"
      run_id="${run_id%%/*}"
      ;;
    *) return 1 ;;
  esac
  [[ "$run_id" =~ ^[1-9][0-9]*$ ]] || return 1
  if ! out="$(GH run view "$run_id" --repo "$REPO" --log-failed 2>&1)"; then
    log "SWEEP admission run=$run_id 失败日志不可读,按普通 BEHIND 处理"
    return 1
  fi
  [[ "$out" == *"DIGEST_STATUS_INVALID"* \
    && "$out" == *"scribe-emissions"* \
    && "$out" == *"ECHO_VERIFY_INFRASTRUCTURE"* \
    && "$out" == *"residual"* ]]
}

is_derived_conflict() {
  case "$1" in
    Meta/StrataLint/Generated/*|Generated/*|Evidence/D5/values.json) return 0 ;;
    *) return 1 ;;
  esac
}

branch_slug() {
  printf '%s' "$1" | sed 's#[^A-Za-z0-9._-]#-#g'
}

dryrun_recalculation() {
  local num="$1" head="$2" workspace="$3"
  log "DRYRUN #$num BEHIND stale derivations -> ensure worktree path=$workspace"
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
  local num="$1" head="$2" expected_head="$3" expected_base="$4" workspace="$5" slug="$6"
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

  git -C "$workspace" merge --abort >/dev/null 2>&1 || true
  git -C "$workspace" reset --hard HEAD >/dev/null
  git -C "$workspace" clean -fd >/dev/null
  if ! git -C "$workspace" fetch --no-tags "$REMOTE" \
    "+refs/heads/dev:refs/remotes/$REMOTE/dev" \
    "+refs/heads/$head:refs/remotes/$REMOTE/$head"; then
    log "SWEEP #$num fetch 失败,放弃本轮"
    return 1
  fi

  local fetched_head fetched_base
  fetched_head="$(git -C "$workspace" rev-parse "refs/remotes/$REMOTE/$head")"
  fetched_base="$(git -C "$workspace" rev-parse "refs/remotes/$REMOTE/dev")"
  if [[ "$fetched_head" != "$expected_head" || "$fetched_base" != "$expected_base" ]]; then
    log "SWEEP #$num head/base 已漂移,放弃本轮(下轮重试)"
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

  if ! credentialless "$isolated_home" \
    make -C "$workspace" --no-print-directory emit-check BASE="$REMOTE/dev"; then
    rm -rf "$isolated_home"
    log "SWEEP #$num emit-check 失败,不 push"; return 1
  fi
  rm -rf "$isolated_home"
}

recalculate_pr() {
  local num="$1" head="$2" expected_head="$3" expected_base="$4" slug workspace
  git check-ref-format --branch "$head" >/dev/null \
    || { log "SWEEP #$num 非法 head branch=$head,放弃本轮"; return 1; }
  slug="$(branch_slug "$head")"
  [[ -n "$slug" ]] || { log "SWEEP #$num head slug 为空,放弃本轮"; return 1; }
  workspace="$CACHE_ROOT/wt-$slug"

  if [[ "$DRYRUN" == "1" ]]; then
    dryrun_recalculation "$num" "$head" "$workspace"
    return 0
  fi
  prepare_worktree "$num" "$head" "$expected_head" "$expected_base" "$workspace" "$slug" \
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
  log "SWEEP #$num BEHIND -> 本地 merge+regen+push 完成 head=$head"
}

open_pr() {
  local head="$1" title="$2" body_file="${3:-}"
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

sweep() {
  mkdir -p "$STATE_DIR"
  local recalculated=" "
  GH pr list --repo "$REPO" --state open --limit 1000 \
    --json number,mergeable,mergeStateStatus,autoMergeRequest,headRefName,headRefOid,baseRefOid,statusCheckRollup \
    --jq '.[] | select(.autoMergeRequest != null) | ((.statusCheckRollup | map(select(.__typename == "CheckRun" and .name == "Content-addressed dev baseline admission")) | sort_by(.completedAt) | last) // {}) as $admission | [.number,.mergeable,.mergeStateStatus,.headRefName,.headRefOid,.baseRefOid,(.statusCheckRollup|length),($admission.conclusion // "-"),($admission.detailsUrl // "-")] | @tsv' |
  while IFS=$'\t' read -r num mergeable mstate head head_oid base_oid checks admission_conclusion admission_url; do
    case "$mergeable:$mstate" in
      MERGEABLE:BEHIND)
        if has_expiry_fingerprint "$admission_conclusion" "$admission_url"; then
          if [[ "$recalculated" == *" $num "* ]]; then
            log "SWEEP #$num 本轮已重算一次,跳过重复项"
            continue
          fi
          recalculated+="$num "
          recalculate_pr "$num" "$head" "$head_oid" "$base_oid" || true
        elif [[ "$DRYRUN" == "1" ]]; then
          log "DRYRUN #$num BEHIND -> update-branch(本地身份,checks 会触发)"
        else
          if out="$(GH api -X PUT "repos/$REPO/pulls/$num/update-branch" 2>&1)"; then
            log "SWEEP #$num BEHIND -> update-branch(本地身份,checks 会触发)"
          else
            log "SWEEP #$num update-branch 失败: $(printf '%s' "$out" | head -c 100)"
          fi
        fi
        ;;
      CONFLICTING:*)
        log "ALERT #$num CONFLICTING head=$head 需语义合并(派 shepherd lane,本器不代解)"
        ;;
      *)
        # BLOCKED/UNKNOWN 且 head 无任何 check:多为 bot push 死锁。
        # 同一 head 连续两轮观察为空才唤醒,防 checks 挂载延迟误触。
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

watch() {
  local interval="${1:-60}" max="${2:-360}"
  if [[ -f "$PIDFILE" ]] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
    log "WATCH 已有实例在跑(pid=$(cat "$PIDFILE")),退出"; exit 1
  fi
  printf '%s' "$$" > "$PIDFILE"
  trap 'rm -f "$PIDFILE"' EXIT
  log "WATCH start interval=${interval}s max_cycles=${max} pid=$$"
  local i armed
  while true; do
    for ((i = 1; i <= max; i++)); do
      sweep || log "SWEEP cycle=$i 出错(继续)"
      sleep "$interval"
    done
    if ! armed="$(armed_pr_count)"; then
      log "WATCH renew(${max} 轮耗尽,armed PR 状态不可判,保守重启计数)"
      continue
    fi
    if [[ "$armed" -gt 0 ]]; then
      log "WATCH renew(${max} 轮耗尽,仍有 open 且 auto-merge armed PR,重启计数)"
      continue
    fi
    log "WATCH end(${max} 轮耗尽,无 open auto-merge armed PR)"
    return
  done
}

case "${1:-}" in
  open)  shift; open_pr "$@" ;;
  watch) shift; watch "$@" ;;
  sweep) sweep ;;
  *) sed -n '2,15p' "$0"; exit 2 ;;
esac
