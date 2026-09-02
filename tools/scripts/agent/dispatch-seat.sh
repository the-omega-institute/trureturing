#!/usr/bin/env bash
# 派一个 codex 席位到指定 worktree,开头 fail-fast 断言全部输入(退出码可辨)。
#
# 用法: dispatch-seat.sh <brief 文件> <worktree 绝对路径> <日志文件> <lock 目录>
#
# 为什么存在(器律④「修产生处让它一出手就是好原材料」):
#   codex 的 cwd **不是**它实际工作的树 —— brief 可以让席位自己 `cd` 到别处。
#   2026-08-31 实测:一次派席脚本的 sed 未命中(替换串不在文件里,静默零替换),
#   三席的 -C 全指向同一棵树;其后行为不一致 —— 一席读 brief 切走了,一席没切。
#   故「lsof 读 cwd 判树上有无在飞席位」这个判据**结构上恒假**。
#   本器改为由派席方写 lock(内含 codex pid),占用判定读 lock 而非 cwd。
#
# 退出码:
#   2 worktree 不存在 / 无法进入
#   3 brief 不存在
#   4 brief 未指名该 worktree(防 sed 零匹配一类的静默错派)
#   5 brief 仍含 __ATOM__ 占位符(未填 atom 即派发)
#   6 该 worktree 已有活席位
set -u

BRIEF=${1:?用法: dispatch-seat.sh <brief> <worktree> <log> <lockdir>}
TREE=${2:?worktree 绝对路径必填}
LOG=${3:?日志文件必填}
LOCKDIR=${4:?lock 目录必填}

[ -d "$TREE" ] || { echo "dispatch-seat: worktree 不存在: $TREE" >&2; exit 2; }
[ -f "$BRIEF" ] || { echo "dispatch-seat: brief 不存在: $BRIEF" >&2; exit 3; }
grep -qF "$TREE" "$BRIEF" \
  || { echo "dispatch-seat: brief 未指名该 worktree: $TREE" >&2; exit 4; }
grep -q '__ATOM__' "$BRIEF" \
  && { echo "dispatch-seat: brief 的 __ATOM__ 占位符未替换" >&2; exit 5; }

mkdir -p "$LOCKDIR"
LOCK="$LOCKDIR/$(basename "$TREE").lock"
if [ -f "$LOCK" ] && kill -0 "$(cat "$LOCK")" 2>/dev/null; then
  echo "dispatch-seat: 该树已有活席位 pid=$(cat "$LOCK")" >&2
  exit 6
fi

cd "$TREE" || exit 2
{
  echo "=== dispatch-seat $(basename "$BRIEF") -> $TREE ==="
  codex exec --skip-git-repo-check --dangerously-bypass-approvals-and-sandbox \
    -C "$TREE" < "$BRIEF" &
  seat=$!
  echo "$seat" > "$LOCK"
  wait "$seat"
  echo "CODEX_EXIT=$?"
  rm -f "$LOCK"
  echo "=== END ==="
  git status --porcelain
} >> "$LOG" 2>&1
