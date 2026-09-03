#!/bin/bash
# 逐条 cover, 失败即跳过并记录 —— cover-batch 是 fail-closed 停在第一个失败,
# 而失败原因(unresolved-subitem / unregistered-genre)在 residual-open yaml 里看不到,
# 只有真跑才知道。故用逐条循环最大化通过率, 失败入账不静默(第 1 条)。
# make cover 只写工作树;成功行的改动在本轮内累积,由调用方统一提交。
# 失败行若留下半截改动,只就地恢复该 atom 路径,然后与该行执行前的状态逐字比较。
# 不用 git reset/restore/checkout —— 它们会连带撤销本轮先前已成功的 cover。
# usage: cover_loop.sh WORKTREE TSV LOG   (sentinel: COVER_LOOP_OK ok=<n> skip=<n>)
set -uo pipefail
[ $# -eq 3 ] || { echo "COVER_LOOP_USAGE: cover_loop.sh WORKTREE TSV LOG" >&2; exit 64; }
W="$1"; TSV="$2"; LOG="$3"
[ -d "$W/.git" ] || [ -f "$W/.git" ] || { echo "COVER_LOOP_BAD_WT=$W" >&2; exit 65; }
[ -f "$TSV" ] || { echo "COVER_LOOP_NO_TSV=$TSV" >&2; exit 66; }
if initial_status=$(cd "$W" && git -c status.renames=false status --porcelain --untracked-files=all); then
  :
else
  status_exit=$?
  echo "COVER_LOOP_FAILED reason=git-status exit=$status_exit"; exit 67
fi
if [ -n "$initial_status" ]; then
  initial_count=$(printf '%s\n' "$initial_status" | wc -l | tr -d ' ')
  echo "COVER_LOOP_FAILED reason=dirty-input-tree files=$initial_count"; exit 70
fi
ok=0; skip=0
: > "$LOG"
while IFS=$'\t' read -r atom gid; do
  [ -n "${atom:-}" ] && [ -n "${gid:-}" ] || continue
  if ! ls "$W"/Meta/Digestion/backfill/*/residual-open/"$atom".yaml >/dev/null 2>&1; then
    echo "SKIP-NOTOPEN $atom" >> "$LOG"; skip=$((skip+1)); continue
  fi
  before_status=$(cd "$W" && git -c status.renames=false status --porcelain --untracked-files=all)
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
      for p in $(git -c status.renames=false status --porcelain --untracked-files=all \
          | awk -v suffix="/$atom.yaml" '
              {p = substr($0, 4)}
              length(p) >= length(suffix) \
                && substr(p, length(p) - length(suffix) + 1) == suffix {print p}'); do
        if git cat-file -e "HEAD:$p" 2>/dev/null; then
          mkdir -p "$(dirname "$p")"
          git show "HEAD:$p" > "$p" || exit 1
        else
          rm -f -- "$p" || exit 1
        fi
      done ) || true
    after_status=$(cd "$W" && git -c status.renames=false status --porcelain --untracked-files=all)
    if [ "$after_status" != "$before_status" ]; then
      dirty=0; [ -z "$after_status" ] || dirty=$(printf '%s\n' "$after_status" | wc -l | tr -d ' ')
      echo "COVER_LOOP_DIRTY_TREE after=$atom files=$dirty" >&2
      echo "COVER_LOOP_FAILED reason=unexpected-dirty-tree after=$atom files=$dirty ok=$ok skip=$skip log=$LOG"
      exit 70
    fi
  fi
done < "$TSV"
echo "COVER_LOOP_OK ok=$ok skip=$skip log=$LOG"
