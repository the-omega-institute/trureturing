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
#       扫描失败即 SCRIBE_GAP_SCAN_FAILED + exit 69,绝不以部分结果打成功哨兵
set -euo pipefail
REPO="${1:-}"
[ -n "$REPO" ] || { echo "SCRIBE_GAP_USAGE: scribe_gap.sh REPO [OUT.txt]" >&2; exit 64; }
[ -d "$REPO/.git" ] || [ -f "$REPO/.git" ] || { echo "SCRIBE_GAP_BAD_REPO=$REPO" >&2; exit 65; }
[ -d "$REPO/Golden/Frozen/state" ] || { echo "SCRIBE_GAP_NO_FROZEN_STATE=$REPO" >&2; exit 66; }
[ -d "$REPO/Blueprint" ] || { echo "SCRIBE_GAP_NO_BLUEPRINT=$REPO" >&2; exit 67; }
# OUT 为空即写继承来的 stdout —— **不得**默认成 /dev/stdout。
# 独立复审席 2026-09-06 实测:`scribe_gap.sh repo > out.txt` 时,`sort > /dev/stdout`
# 重新打开该普通文件写入**不推进原 stdout 的文件偏移**,随后 `echo` 哨兵从原偏移覆盖名单,
# 结果文件里只剩哨兵、黑名单全丢,而 exit 仍为 0 —— 又一条「成功哨兵盖住静默丢结果」。
# 该缺陷在本器首版即存在,不是 find 修复引入的。
OUT="${2:-}"
cd "$REPO"
# trap 必须先于 mktemp 注册:否则第二次 mktemp 失败时 errexit 会在注册前退出,遗留第一个临时文件。
tmp=""
states=""
trap 'rm -f "$tmp" "$states"' EXIT
tmp=$(mktemp)
states=$(mktemp)
# find 的失败必须传回主流程。进程替换 `< <(find …)` 会把 find 的退出码丢在子 shell 里:
# 遍历中途因不可读目录而失败时,循环照常正常结束,哨兵照常打印 SCRIBE_GAP_OK 且 exit=0
# —— 那是器律④ 所禁的坏原材料(部分结果冒充完整结果)。
# 独立评审席 2026-09-06 以合成夹具实测该形态:含不可读子目录的状态树上
# stderr 出 Permission denied,而脚本仍报 frozen=1 missing=0 exit=0。
# 故先把清单落盘并显式判 find 的退出码,再进循环。
if ! find Golden/Frozen/state -name '*.lean.json' > "$states"; then
  echo "SCRIBE_GAP_SCAN_FAILED root=Golden/Frozen/state" >&2
  exit 69
fi
sort -o "$states" "$states"
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
done < "$states"
[ "$frozen" -gt 0 ] || { echo "SCRIBE_GAP_EMPTY_FROZEN_STATE" >&2; exit 68; }
if [ -n "$OUT" ]; then
  sort -u "$tmp" > "$OUT"
else
  sort -u "$tmp"
fi
echo "SCRIBE_GAP_OK frozen=$frozen missing=$missing"
