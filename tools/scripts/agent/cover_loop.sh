#!/bin/bash
# 逐条 cover, 失败即跳过并记录 —— cover-batch 是 fail-closed 停在第一个失败,
# 而失败原因(unresolved-subitem / unregistered-genre)在 residual-open yaml 里看不到,
# 只有真跑才知道。故用逐条循环最大化通过率, 失败入账不静默(第 1 条)。
# 失败时 make cover 有时自己提交一条 "record failed cover disposition"(树干净),
# 有时留下半截改动(residual-open 已删 / absorbed-closed 已建) —— 2026-09-01 实测两种都有,
# 故不能假设失败后树一定干净。留下半截时就地恢复:被删的从 HEAD 取回内容写回,
# 新建的未跟踪文件删掉。不用 git reset/restore/checkout —— 宿主 hook 拦截它们,
# 且它们会连带撤销本轮已成功的 cover 提交之外的东西。
# usage: cover_loop.sh WORKTREE TSV LOG   (sentinel: COVER_LOOP_OK ok=<n> skip=<n>)
set -uo pipefail
[ $# -eq 3 ] || { echo "COVER_LOOP_USAGE: cover_loop.sh WORKTREE TSV LOG" >&2; exit 64; }
W="$1"; TSV="$2"; LOG="$3"
[ -d "$W/.git" ] || [ -f "$W/.git" ] || { echo "COVER_LOOP_BAD_WT=$W" >&2; exit 65; }
[ -f "$TSV" ] || { echo "COVER_LOOP_NO_TSV=$TSV" >&2; exit 66; }
ok=0; skip=0
: > "$LOG"
while IFS=$'\t' read -r atom gid; do
  [ -n "${atom:-}" ] && [ -n "${gid:-}" ] || continue
  if ! ls "$W"/Meta/Digestion/backfill/*/residual-open/"$atom".yaml >/dev/null 2>&1; then
    echo "SKIP-NOTOPEN $atom" >> "$LOG"; skip=$((skip+1)); continue
  fi
  if ( cd "$W" && make cover ATOM_ID="$atom" GID="$gid" ) > /tmp/cover_one.log 2>&1; then
    echo "OK $atom" >> "$LOG"; ok=$((ok+1))
  else
    # 失败原因不一定出现在 gaps= 行 —— 2026-09-01 实测 24 条失败里 21 条被报成 unknown,
    # 掩盖了真实原因。故多路提取, 并把完整日志留档以便事后归因(第 1 条:不静默)。
    reason=$(grep -oE 'gaps=[a-z,-]+' /tmp/cover_one.log | tail -1)
    [ -n "$reason" ] || reason=$(grep -oE '(COVER|PLAYBOOK|ALIGN)_[A-Z_]+' /tmp/cover_one.log | tail -1)
    [ -n "$reason" ] || reason=$(grep -iE 'error|fatal|refus|invalid|missing' /tmp/cover_one.log | tail -1 | cut -c1-120)
    mkdir -p "${LOG%.log}-fails"
    cp /tmp/cover_one.log "${LOG%.log}-fails/$atom.log" 2>/dev/null || true
    echo "FAIL $atom ${reason:-unknown}" >> "$LOG"; skip=$((skip+1))
    # 就地恢复该 atom 留下的半截改动(只碰这个 atom 的两个路径, 不碰别的)
    ( cd "$W"
      for p in $(git status --porcelain | awk -v a="$atom" '"'"'$2 ~ a {print $2}'"'"'); do
        case "$(git status --porcelain -- "$p" | cut -c1-2)" in
          " D"|"D ") git show "HEAD:$p" > "$p" 2>/dev/null || true ;;
          "??")      rm -f "$p" ;;
        esac
      done ) || true
  fi
  dirty=$(cd "$W" && git status --porcelain | wc -l | tr -d ' ')
  if [ "$dirty" != "0" ]; then
    echo "COVER_LOOP_DIRTY_TREE after=$atom files=$dirty" >&2
    echo "COVER_LOOP_OK ok=$ok skip=$skip log=$LOG (halted: dirty tree)"; exit 70
  fi
done < "$TSV"
echo "COVER_LOOP_OK ok=$ok skip=$skip log=$LOG"
