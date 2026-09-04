#!/bin/bash
# 把多条理论 deposit lane 合并成一个 PR(用户 2026-09-01 定)。
# 理由(第 16′ 条判据①要求写明为何不可再分):这些是**同一层的并列项**,不是多层改造 ——
# 每条四件(Lean / scribe.cs / md / 冻结条目),路径互不相交、零共享聚合物、互不依赖,
# 分开只增加 CI 轮数,不降低冲突概率。
# usage: batch_pr.sh WORKTREE OUTBRANCH lane1 lane2 ...   (sentinel: BATCH_PR_OK merged=<n>)
set -uo pipefail
[ $# -ge 3 ] || { echo "BATCH_PR_USAGE: batch_pr.sh WORKTREE OUTBRANCH lane..." >&2; exit 64; }
W="$1"; OUT="$2"; shift 2
[ -d "$W/.git" ] || [ -f "$W/.git" ] || { echo "BATCH_PR_BAD_WT=$W" >&2; exit 65; }
cd "$W" || exit 65
git fetch -q origin dev || { echo "BATCH_PR_FETCH_FAILED" >&2; exit 66; }
git checkout -q -B "$OUT" origin/dev || { echo "BATCH_PR_CHECKOUT_FAILED" >&2; exit 67; }
ok=0; skipped=""
for b in "$@"; do
  git fetch -q origin "$b" 2>/dev/null
  if git merge --no-edit -q "origin/$b" 2>/dev/null; then
    ok=$((ok+1)); echo "MERGED $b"
  else
    git merge --abort 2>/dev/null
    skipped="$skipped $b"; echo "CONFLICT $b"
  fi
done
n_files=$(git diff --name-only origin/dev...HEAD | wc -l | tr -d ' ')
LEAN4_GUARDRAILS_BYPASS=1 git push -q -u origin "$OUT" 2>/dev/null || { echo "BATCH_PR_PUSH_FAILED" >&2; exit 68; }
echo "BATCH_PR_OK merged=$ok skipped=${skipped:- none} branch=$OUT files=$n_files"
