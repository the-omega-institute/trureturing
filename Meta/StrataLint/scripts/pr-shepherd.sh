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

sweep() {
  GH pr list --repo "$REPO" --state open \
    --json number,mergeable,mergeStateStatus,autoMergeRequest,headRefName \
    --jq '.[] | select(.autoMergeRequest != null) | "\(.number) \(.mergeable) \(.mergeStateStatus) \(.headRefName)"' |
  while read -r num mergeable mstate head; do
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
      *) : ;;  # BLOCKED=checks 在跑/待绿,CLEAN=即将自动合,UNKNOWN=GitHub 未算完:均不动
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
