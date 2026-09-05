#!/bin/bash
# 器律⑨: cover owner 可用性预筛 —— 列出「已冻结但没有 Scribe 定义」的模块。
#
# 为什么需要它(实测,非设想):cover 门的第四项前置是「owner 定理被其 Scribe 声明引用」。
# 一个整个模块没有 `Blueprint/<rel>.scribe.cs` 的冻结模块,其中任何定理都不能作 cover owner,
# 不管覆盖关系多么忠实 —— 门会答 `partial-closed deletable=false gaps=scribe-declaration-reference-missing`
# (issue #5573)。而 `make cover-batch` 严格串行、首败即中止,故一个这样的 owner
# 会连带阻塞同批后面所有的对。
# 2026-09-06 实测 origin/dev=9f31ed5ee2: 3389 个冻结模块中 226 个(6.7%)缺 Scribe 定义。
#
# 用法:挖掘席开工前跑一次,把输出当 owner 黑名单;选中的 owner 若在名单里,
# 要么换一条有 Scribe 的定理,要么把「补该模块 .scribe.cs + make emit」计入同一个 cover PR。
#
# 本器只列事实,不下「该不该补」的结论(第 8 条:不预建空壳;按需补,不批量补)。
#
# usage: scribe_gap.sh REPO [OUT.txt]
# 哨兵: SCRIBE_GAP_OK frozen=<n> missing=<n>
set -euo pipefail
REPO="${1:-}"
[ -n "$REPO" ] || { echo "SCRIBE_GAP_USAGE: scribe_gap.sh REPO [OUT.txt]" >&2; exit 64; }
[ -d "$REPO/.git" ] || [ -f "$REPO/.git" ] || { echo "SCRIBE_GAP_BAD_REPO=$REPO" >&2; exit 65; }
[ -d "$REPO/Golden/Frozen/state" ] || { echo "SCRIBE_GAP_NO_FROZEN_STATE=$REPO" >&2; exit 66; }
[ -d "$REPO/Blueprint" ] || { echo "SCRIBE_GAP_NO_BLUEPRINT=$REPO" >&2; exit 67; }
OUT="${2:-/dev/stdout}"
cd "$REPO"
tmp=$(mktemp)
trap 'rm -f "$tmp"' EXIT
frozen=0
missing=0
while IFS= read -r state; do
  frozen=$((frozen + 1))
  rel=${state#Golden/Frozen/state/}
  rel=${rel%.lean.json}
  if [ ! -f "Blueprint/$rel.scribe.cs" ]; then
    missing=$((missing + 1))
    printf '%s\n' "$rel" >> "$tmp"
  fi
done < <(find Golden/Frozen/state -name '*.lean.json' | sort)
[ "$frozen" -gt 0 ] || { echo "SCRIBE_GAP_EMPTY_FROZEN_STATE" >&2; exit 68; }
sort -u "$tmp" > "$OUT"
echo "SCRIBE_GAP_OK frozen=$frozen missing=$missing"
