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
        *waiting_response*|*"Task is dispatched"*) : ;;
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
    # vote <brief> <outfile> [max_attempts] — nyxid 一票的完整闭环:派发 → 阻塞 → extraction_failure 自动重投
    # 立条依据(2026-09-03):extraction_failure 是**随机**故障(本会话实测 20+ 次),
    # 每次手搓「重投一次、再等一次」既费 turn 又常忘记上限。判据写死:只对 extraction_failure 重投,
    # 其它落定值(含 approve/reject/comment)一律直接返回。
    brief="${1:?brief}"; out="${2:?outfile}"; maxn="${3:-4}"
    n=0
    while [ "$n" -lt "$maxn" ]; do
      n=$(( n + 1 ))
      bash "$__TOOLDIR/nyx.sh" ask "$brief" "$out" >"${out}.log" 2>&1
      tid=$(grep -oE '[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}' "$out" 2>/dev/null | head -1)
      if [ -z "$tid" ]; then
        printf 'AWAIT_VOTE attempt=%s state=no-task-id at=%s\n' "$n" "$(__stamp)"; sleep "$TICK"; continue
      fi
      res=$(AWAIT_DEADLINE="$DEADLINE" AWAIT_TICK="$TICK" bash "$__TOOLDIR/await.sh" nyx "$tid")
      case "$res" in
        *extraction_failure*)
          # 退避(2026-09-03 立):extraction_failure 常是浏览器侧**瞬时**故障,失败在提交侧、秒级返回。
          # 实测:4 次重投落在 03:52:51/:54/:56/03:53:19 —— 30 秒烧光预算,全撞同一个故障窗;
          # 而同一天空闲池上成功的一票用了约 20 分钟才落定。故重投必须拉开到分钟级。
          back=$(( 60 * n ))
          printf 'AWAIT_VOTE attempt=%s task=%s state=extraction_failure at=%s backoff=%ss\n' "$n" "$tid" "$(__stamp)" "$back"
          [ "$n" -lt "$maxn" ] && sleep "$back" ;;
        *)
          printf 'AWAIT_VOTE attempt=%s task=%s state=settled at=%s\n' "$n" "$tid" "$(__stamp)"
          printf '%s' "$res" > "$out.settled"
          printf '%s' "$res"; exit 0 ;;
      esac
    done
    printf 'AWAIT_VOTE state=exhausted attempts=%s at=%s\n' "$maxn" "$(__stamp)"; exit 125 ;;
  *) echo "usage: await.sh {seat <flight> [attempt] | nyx <task-id> | make <logfile> | vote <brief> <out> [max]}" >&2; exit 2 ;;
esac
