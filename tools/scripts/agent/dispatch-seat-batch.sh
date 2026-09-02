#!/usr/bin/env bash
# 一次宿主作业内并发派多个 codex 席位,join 后才返回。
#
# 用法: dispatch-seat-batch.sh <lockdir> <brief>:<worktree>:<log> [更多...]
#
# 为什么存在:
#   宿主的每条后台作业都是一个可被中断的单位;派 N 席若开 N 条宿主作业,
#   一次中断即损失 N 席。本器把 N 席收进**一条**宿主作业:内部用 `&` 并发、
#   `wait` 收拢,启动器在全部子进程结束前不返回 —— 这正是器律⑥ 明许的合法形
#   (禁的是让「启动器」先于「任务」返回),也是 sshx 的 batch 形态。
#   代价如实记:完成通知从「每席一条」降为「每批一条」。
#
# 退出码:非零 = 至少一席未以 0 结束;逐席退出码见报告行。
set -u

LOCKDIR=${1:?用法: dispatch-seat-batch.sh <lockdir> <brief>:<tree>:<log> ...}
shift
[ $# -ge 1 ] || { echo "dispatch-seat-batch: 至少要一席" >&2; exit 2; }

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
seat_script="$here/dispatch-seat.sh"
[ -x "$seat_script" ] || { echo "dispatch-seat-batch: 缺 dispatch-seat.sh" >&2; exit 2; }

pids=(); names=()
for spec in "$@"; do
  brief=${spec%%:*}; rest=${spec#*:}
  tree=${rest%%:*}; log=${rest#*:}
  "$seat_script" "$brief" "$tree" "$log" "$LOCKDIR" &
  pids+=("$!"); names+=("$(basename "$brief")")
done

rc=0
for i in "${!pids[@]}"; do
  if wait "${pids[$i]}"; then
    echo "BATCH_SEAT name=${names[$i]} exit=0"
  else
    seat_rc=$?
    echo "BATCH_SEAT name=${names[$i]} exit=$seat_rc"
    rc=1
  fi
done
echo "BATCH_RESULT seats=${#pids[@]} outcome=$([ $rc -eq 0 ] && echo all-ok || echo partial)"
exit $rc
