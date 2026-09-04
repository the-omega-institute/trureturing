#!/bin/bash
# 器律⑨ + 第 11 条六路查重第⑥路: 列出所有在飞 lane 分支已形式化的模块名与 atom_id。
# 选题去重只查 dev 与自己上一批是不够的——744 个 lane 分支里躺着别人（和自己）已做的题。
# 2026-09-04 实测: 12 个候选全撞 DUPLICATE，其中一个正躺在自己的 dep0904e-2 上。
# usage: inflight_mods.sh REPO [OUT_MODS] [OUT_ATOMS]
# 哨兵: INFLIGHT_OK mods=<n> atoms=<n>
set -euo pipefail
REPO="${1:?usage: inflight_mods.sh REPO [OUT_MODS] [OUT_ATOMS]}"
OUT_M="${2:-/dev/stdout}"
OUT_A="${3:-}"
cd "$REPO"
tmp_m=$(mktemp); tmp_a=$(mktemp)
trap 'rm -f "$tmp_m" "$tmp_a"' EXIT
while read -r b; do
  git diff --name-only "origin/dev...$b" -- 'D5' 2>/dev/null \
    | grep '\.lean$' | sed 's|.*/||;s|\.lean$||' >> "$tmp_m" || true
  git diff --name-only "origin/dev...$b" -- 'Meta/Digestion/backfill' 2>/dev/null \
    | grep 'absorbed-closed' | sed 's|.*/||;s|\.yaml$||' >> "$tmp_a" || true
done < <(git for-each-ref --format='%(refname:short)' 'refs/remotes/origin/lane/math/*')
sort -u "$tmp_m" > "$OUT_M"
[ -n "$OUT_A" ] && sort -u "$tmp_a" > "$OUT_A"
echo "INFLIGHT_OK mods=$(wc -l < "$OUT_M" | tr -d ' ') atoms=$([ -n "$OUT_A" ] && wc -l < "$OUT_A" | tr -d ' ' || echo skipped)"
