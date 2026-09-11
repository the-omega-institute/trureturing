#!/usr/bin/env bash
# await.sh — 一条同步阻塞调用,替代手搓挂钟(CLAUDE.md 器律⑥′)
#
# 立条依据(2026-09-03 用户直问「不是用脚本么, 为何挂钟」):
#   sshx runner 的**完成通知会早报**(本会话实测 5 次:w32-B / u-fix4 / w-rev-cx / w36 cover-batch / aa),
#   于是我退回了 `sleep N; 查` 的手搓轮询——每轮一个 turn、间隔靠猜、判据每次重写。
#   ⑥′ 的正解不是「别等」,是**把等待封进器**:一次调用阻塞到条件成立,判据写死在器里。
#
# 用法:
#   await.sh seat <flight-id> [attempt]     阻塞到 run_dir 出现 result.json(即席位真交回)
#   await.sh nyx  <task-id>                 阻塞到 nyxid 任务不再 waiting_response
#   await.sh make <logfile>                 阻塞到日志出现 EXIT= 哨兵行
#   await.sh vote <brief> <out> [max]        Submit and await a vote (default max 4).
#   退出码契约:seat/nyx/make —— 0 条件成立(make 只看哨兵出现,不看其值)、124 超 AWAIT_DEADLINE;
#   vote —— 0 settled(NYX_OK,答案已落 <out>.settled)、6 UNCERTAIN(不重投,打印 task id)、1 DELIVERY(不重投)、
#   2 参数/IO 错误、124 超时、125 重试耗尽(EXTRACTION/QUOTA/BUSY 各轮均失败)、其余=转发 nyx.sh 的失败/信号状态。
#   通用:缺必需参数(\${x:?})由 shell 以 1 退出;未知动词 usage 退出 2。
# 环境:AWAIT_DEADLINE(秒,默认 5400)、AWAIT_TICK(秒,默认 20)
#
# 为什么仍有内部轮询:这三样**都没有自带的同步原语**(runner 已返回、nyxid 只有查询式 API、
# make 跑在别的 job 里)。⑥′ 允许此时轮询,但要求:间隔与真实节奏对齐、有上限、每轮留时间戳与读数、
# **判据在开跑前写死**——这三条都在本器里,而不是每次现搓。
# 器律⑨:同目录解析同伴器,禁止指回宿主机 ~/.claude(那对其他驱动机不存在)。
__TOOLDIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

set -u
DEADLINE="${AWAIT_DEADLINE:-5400}"; TICK="${AWAIT_TICK:-20}"
kind="${1:-}"; shift || true
start=$(date +%s)
__deadline_hit() { [ $(( $(date +%s) - start )) -ge "$DEADLINE" ]; }
__stamp() { date +%H:%M:%S; }

case "$kind" in
  seat)
    fid="${1:?flight-id}"; att="${2:-1}"
    d="${TMPDIR%/}/consensus-rnd/sshx/$fid/attempt-$att"
    while :; do
      if [ -f "$d/result.json" ]; then
        printf 'AWAIT_SEAT flight=%s attempt=%s state=done at=%s elapsed=%ss\n' "$fid" "$att" "$(__stamp)" "$(( $(date +%s) - start ))"
        grep -o '"reason_code": *"[^"]*"' "$d/status.json" 2>/dev/null
        exit 0
      fi
      if __deadline_hit; then
        printf 'AWAIT_SEAT flight=%s attempt=%s state=deadline at=%s pid=%s\n' "$fid" "$att" "$(__stamp)" "$(pgrep -f "$fid" | head -1)"
        exit 124
      fi
      sleep "$TICK"
    done ;;
  nyx)
    tid="${1:?task-id}"
    while :; do
      out=$(nyxid oracle result "$tid" 2>&1)
      case "$out" in
        *waiting_response*|*"Task is dispatched"*|*"Task is queued"*|*"Queue position"*) : ;;
        *) printf 'AWAIT_NYX task=%s state=settled at=%s elapsed=%ss\n' "$tid" "$(__stamp)" "$(( $(date +%s) - start ))"
           printf '%s' "$out"; exit 0 ;;
      esac
      if __deadline_hit; then
        printf 'AWAIT_NYX task=%s state=deadline at=%s elapsed=%ss\n' "$tid" "$(__stamp)" "$(( $(date +%s) - start ))"; exit 124
      fi
      sleep "$TICK"
    done ;;
  make)
    log="${1:?logfile}"
    while :; do
      if grep -qE '^EXIT=' "$log" 2>/dev/null; then
        printf 'AWAIT_MAKE log=%s state=done at=%s elapsed=%ss\n' "$log" "$(__stamp)" "$(( $(date +%s) - start ))"
        grep -E '^EXIT=' "$log" | tail -1; exit 0
      fi
      if __deadline_hit; then
        printf 'AWAIT_MAKE log=%s state=deadline at=%s pid=%s\n' "$log" "$(__stamp)" "$(pgrep -f 'make (cover-batch|deposit)' | head -1)"; exit 124
      fi
      sleep "$TICK"
    done ;;
  vote)
    # Follow nyx's command verdict, including traversal. Only TIMEOUT needs fetch;
    # EXTRACTION/QUOTA/BUSY retry; UNCERTAIN/DELIVERY stop with recovery references.
    brief="${1:?brief}"; out="${2:?outfile}"; maxn="${3:-4}"
    [[ "$maxn" =~ ^[0-9]+$ ]] && [ "$maxn" -gt 0 ] && [ "$maxn" -le 2147483647 ] 2>/dev/null || exit 2
    rm -f "$out.settled" || exit 2
    n=0
    while [ "$n" -lt "$maxn" ]; do
      n=$(( n + 1 ))
      args=(ask "$brief" "$out")
      : > "$out.log" || exit 2
      while :; do
        bash "$__TOOLDIR/nyx.sh" "${args[@]}" >> "$out.log" 2>&1; rc=$?
        verdict=$(awk '/^NYX_(OK|EXTRACTION|QUOTA|BUSY|TIMEOUT|DELIVERY|UNCERTAIN|NOFILE|UNKNOWN|EXPIRED|NOPOOL|LOCKBUSY|ERR|IO|CANCELLED)( |$)/ {v=$1} END {print v}' "$out.log")
        [ "$rc" -eq 3 ] && [ "$verdict" = NYX_TIMEOUT ] || break
        tid=$(bash "$__TOOLDIR/nyx.sh" taskid "$out") || exit 2
        if __deadline_hit; then
          printf 'AWAIT_VOTE attempt=%s task=%s state=deadline at=%s\n' "$n" "$tid" "$(__stamp)"; exit 124
        fi
        args=(fetch "$tid" "$out")
      done
      if [ "$rc" -eq 0 ] && [ "$verdict" = NYX_OK ]; then
        tid=$(bash "$__TOOLDIR/nyx.sh" taskid "$out") || exit 2
        cat "$out" > "$out.settled" || exit 2
        printf 'AWAIT_VOTE attempt=%s task=%s state=settled at=%s\n' "$n" "$tid" "$(__stamp)"
        cat "$out.settled"; exit 0
      fi
      case "$verdict" in
        NYX_UNCERTAIN|NYX_DELIVERY)
          tid=$(bash "$__TOOLDIR/nyx.sh" taskid "$out") || exit 2
          printf 'AWAIT_VOTE attempt=%s task=%s state=stopped verdict=%s at=%s\n' "$n" "$tid" "$verdict" "$(__stamp)"
          [ "$verdict" != NYX_UNCERTAIN ] || exit 6
          exit 1 ;;
        NYX_EXTRACTION|NYX_QUOTA|NYX_BUSY)
          # Keep the existing minute-scale backoff between fresh submissions.
          back=$(( 60 * n ))
          printf 'AWAIT_VOTE attempt=%s state=retry verdict=%s at=%s backoff=%ss\n' "$n" "$verdict" "$(__stamp)" "$back"
          [ "$n" -lt "$maxn" ] && sleep "$back" ;;
        *)
          printf 'AWAIT_VOTE attempt=%s state=failed verdict=%s at=%s\n' "$n" "$verdict" "$(__stamp)"
          [ "$rc" -ne 0 ] || rc=1
          exit "$rc" ;;
      esac
    done
    printf 'AWAIT_VOTE state=exhausted attempts=%s at=%s\n' "$maxn" "$(__stamp)"; exit 125 ;;
  *) echo "usage: await.sh {seat <flight> [attempt] | nyx <task-id> | make <logfile> | vote <brief> <out> [max]}" >&2; exit 2 ;;
esac
