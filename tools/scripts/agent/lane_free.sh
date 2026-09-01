#!/bin/bash
# 派题前必须确认 lane 空闲 —— sshx 协议硬约束:flight 在飞时 caller 对该 work_target 只读。
# 2026-09-01 实测教训:批量派题时未检查,给正在跑「平衡场分层」的 C 又派了一条,
# 第二条 INTERRUPTED,且 `git checkout -B` 差点切走正被 codex 使用的分支。
# usage: lane_free.sh <a|b|c>   exit 0=空闲 / 1=在飞
set -uo pipefail
[ $# -eq 1 ] || { echo "LANE_FREE_USAGE: lane_free.sh <a|b|c>" >&2; exit 64; }
W="/Users/chronoai/trureturing-prime-$1"
[ -d "$W" ] || { echo "LANE_FREE_BAD_LANE=$1" >&2; exit 65; }
n=$(ps -eo args | grep "codex exec" | grep -c -- "-C $W" || true)
if [ "$n" -gt 0 ]; then
  br=$(cd "$W" && git branch --show-current 2>/dev/null)
  echo "LANE_BUSY lane=$1 procs=$n branch=${br:-?}"; exit 1
fi
echo "LANE_FREE lane=$1"; exit 0
