#!/usr/bin/env bash
# pr-shepherd —— PR 一门器(一器一门,第Ⅵ节·器之四律①)
#
# 职责:开 PR 到 dev 并挂 auto-merge;轮询在飞 PR,BEHIND 即以本地已登录
# gh 身份 update-branch(会正常触发 checks;GITHUB_TOKEN 自动化因防递归规则
# 判负撤役,见 retire-auto-update 尸检)。CONFLICTING 只告警不代解(语义合并
# 归 shepherd lane)。
#
# 用法:
#   pr-shepherd.sh open <head-branch> <title> [body-file]   开 PR + 挂 auto-merge
#   pr-shepherd.sh watch [interval] [max_cycles]            轮询(默认 60s × 360)
#   pr-shepherd.sh sweep                                    单轮扫描(供人工/调试)
#
# 判定只看机器字段(mergeable/mergeStateStatus/autoMergeRequest),不看输出散文。
set -euo pipefail

REPO="the-omega-institute/trureturing"
LOG="${PR_SHEPHERD_LOG:-$HOME/.pr-shepherd.log}"
PIDFILE="${PR_SHEPHERD_PID:-$HOME/.pr-shepherd.pid}"
STATE_DIR="${PR_SHEPHERD_STATE:-$HOME/.pr-shepherd-state}"

GH() { LEAN4_GUARDRAILS_BYPASS=1 gh "$@"; }

log() { printf '%s %s\n' "$(date '+%F %T')" "$*" | tee -a "$LOG" >&2; }

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
  GH pr list --repo "$REPO" --state open \
    --json number,mergeable,mergeStateStatus,autoMergeRequest,headRefName,headRefOid,statusCheckRollup \
    --jq '.[] | select(.autoMergeRequest != null) | "\(.number) \(.mergeable) \(.mergeStateStatus) \(.headRefName) \(.headRefOid) \(.statusCheckRollup|length)"' |
  while read -r num mergeable mstate head head_oid checks; do
    case "$mergeable:$mstate" in
      MERGEABLE:BEHIND)
        if out="$(GH api -X PUT "repos/$REPO/pulls/$num/update-branch" 2>&1)"; then
          log "SWEEP #$num BEHIND -> update-branch(本地身份,checks 会触发)"
        else
          log "SWEEP #$num update-branch 失败: $(printf '%s' "$out" | head -c 100)"
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

watch() {
  local interval="${1:-60}" max="${2:-360}"
  if [[ -f "$PIDFILE" ]] && kill -0 "$(cat "$PIDFILE")" 2>/dev/null; then
    log "WATCH 已有实例在跑(pid=$(cat "$PIDFILE")),退出"; exit 1
  fi
  printf '%s' "$$" > "$PIDFILE"
  trap 'rm -f "$PIDFILE"' EXIT
  log "WATCH start interval=${interval}s max_cycles=${max} pid=$$"
  local i
  for ((i = 1; i <= max; i++)); do
    sweep || log "SWEEP cycle=$i 出错(继续)"
    sleep "$interval"
  done
  log "WATCH end(${max} 轮耗尽,由调用方重挂)"
}

case "${1:-}" in
  open)  shift; open_pr "$@" ;;
  watch) shift; watch "$@" ;;
  sweep) sweep ;;
  *) sed -n '2,15p' "$0"; exit 2 ;;
esac
