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
#   await.sh make <logfile>                 阻塞到日志出现 EXIT= 哨兵行
#   退出码契约:0 条件成立(make 只看哨兵出现,不看其值)、124 超 AWAIT_DEADLINE。
#   通用:缺必需参数(\${x:?})由 shell 以 1 退出;未知动词 usage 退出 2。
# 环境:AWAIT_DEADLINE(秒,默认 5400)、AWAIT_TICK(秒,默认 20)
#
# 为什么仍有内部轮询:这两样**都没有自带的同步原语**(runner 已返回、make 跑在别的 job 里)。
# ⑥′ 允许此时轮询,但要求:间隔与真实节奏对齐、有上限、每轮留时间戳与读数、
# **判据在开跑前写死**——这三条都在本器里,而不是每次现搓。

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
  *) echo "usage: await.sh {seat <flight> [attempt] | make <logfile>}" >&2; exit 2 ;;
esac
