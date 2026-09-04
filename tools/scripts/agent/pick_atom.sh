#!/bin/bash
# 选题:从基于 origin/dev 生成的 pool 取候选,排除在飞账目 delta 与活跃 flight 占用的 atom。
# usage: pick_atom.sh REPO POOL.tsv N   (输出 N 行:atom<TAB>title)
set -uo pipefail
[ $# -eq 3 ] || { echo "PICK_USAGE: pick_atom.sh REPO POOL.tsv N" >&2; exit 64; }
R="$1"; POOL="$2"; N="$3"
[ -f "$POOL" ] || { echo "PICK_NO_POOL=$POOL" >&2; exit 65; }
cd "$R" || exit 66
git fetch -q origin 2>/dev/null
# 占用集 = 所有 lane/math/* 分支相对 dev 改动的 atom 账目路径
{
  for b in $(git ls-remote --heads origin 'refs/heads/lane/math/*' 2>/dev/null | awk '{print $2}' | sed 's#refs/heads/##'); do
    git diff --name-only "origin/dev...origin/$b" 2>/dev/null | grep '^Meta/Digestion/backfill/.*/.*\.yaml$'
  done
} | sed 's#.*/##;s#\.yaml$##' | sort -u > /tmp/pick_taken.txt
# 还要排除尚未写出账目 delta 的活跃 flight。
# 2026-09-01 教训:选题器返回的三条里有两条正被别的 lane 做着。
# 从正在跑的 codex 的 flight 目录读它实际收到的 brief,提取 ATOM_ID。
for d in $(ps -eo args | grep 'codex exec' | grep -oE '/[^ ]*consensus-rnd/sshx/[a-z0-9-]+/attempt-[0-9]+' | sort -u); do
  [ -f "$d/brief.md" ] || continue
  grep -oE '\b[0-9a-f]{64}\b' "$d/brief.md" 2>/dev/null | head -1
done | sort -u >> /tmp/pick_taken.txt
sort -u -o /tmp/pick_taken.txt /tmp/pick_taken.txt
export LC_ALL=C
awk -F'\t' '($1=="CLEAN" || $1=="UNKNOWN") && $5 !~ /结论|总结|小结|目录|总纲/ && $3>=60 && $3<=140 {print $4"\t"$2"\t"$5}' "$POOL" \
  | sort -t$'\t' -k2 -rn | cut -f1,3 > /tmp/pick_cand.txt
n_taken=$(wc -l < /tmp/pick_taken.txt | tr -d ' ')
out=0
while IFS=$'\t' read -r a t; do
  grep -qx "$a" /tmp/pick_taken.txt && continue
  printf '%s\t%s\n' "$a" "$t"; out=$((out+1))
  [ "$out" -ge "$N" ] && break
done < /tmp/pick_cand.txt
echo "PICK_OK returned=$out taken_set=$n_taken" >&2
