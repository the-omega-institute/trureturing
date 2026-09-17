#!/bin/bash
# 派题前必须确认 lane 空闲 —— sshx 协议硬约束:flight 在飞时 caller 对该 work_target 只读。
# 2026-09-01 实测教训:批量派题时未检查,给正在跑「平衡场分层」的 C 又派了一条,
# 第二条 INTERRUPTED,且 `git checkout -B` 差点切走正被 codex 使用的分支。
#
# 2026-09-12: 本器此前写死 `/Users/chronoai/trureturing-prime-$1`,那是另一台驱动机的路径。
# 在本机该目录不存在,故它对**每个**参数都走 `LANE_FREE_BAD_LANE` 退 65 —— 既不报空闲也不报在飞,
# 提供零保护,而调用方若只看「不是 1」就会把 65 当成放行。全仓 grep 显示它零调用者,
# 所以这个静默失效从未变红(第 9.2 条:无检测的引用是断链)。
# 修法是取 lane 目录本身作参数:判据本来就与目录布局无关,写死某台机的命名才是 bug。
#
# usage: lane_free.sh <lane-dir>   exit 0=空闲 / 1=在飞 / 64=用法错 / 65=目录不存在
# 哨兵: LANE_FREE lane=<dir> / LANE_BUSY lane=<dir> procs=<n> branch=<br>
set -uo pipefail
[ $# -eq 1 ] || { echo "LANE_FREE_USAGE: lane_free.sh <lane-dir>" >&2; exit 64; }
W="$1"
[ -d "$W" ] || { echo "LANE_FREE_BAD_LANE=$W" >&2; exit 65; }
# 规范化:ps 里记的是 codex 收到的 -C 实参,调用方可能传相对路径或带尾斜杠。
W=$(cd "$W" && pwd -P)
n=$(ps -eo args | grep "codex exec" | grep -c -- "-C $W\( \|$\)" || true)
if [ "$n" -gt 0 ]; then
  br=$(cd "$W" && git branch --show-current 2>/dev/null)
  echo "LANE_BUSY lane=$W procs=$n branch=${br:-?}"; exit 1
fi
echo "LANE_FREE lane=$W"; exit 0
