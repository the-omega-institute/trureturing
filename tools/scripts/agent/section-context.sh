#!/usr/bin/env bash
# section-context.sh <source_md> <theorem_no> — 提取定理所在**章节的 standing clause**
#
# 立条依据(2026-09-04,dep0903aj 假 reject):
#   投票 brief 只内联 atom。而 atom 是**切片** —— 节级 standing clause 不在切片里。
#   于是评审席把源卷本来就有的载体条件判成「凭空新增假设」,给出 reject。
#   实测 aj:`0 < weight i` 在源卷第 2016 行、`0 < gamma <= 1` 在第 33 节开头,
#   两条都在,只是不在原子里。**这是编排缺陷,不是实施缺陷。**
#
# 输出:该定理所在节从节标题到该定理之间的全部文字(即 standing clause 的所在区间)。
set -uo pipefail
md="${1:?source markdown}"; thm="${2:?theorem number, e.g. 33.1}"
[ -r "$md" ] || { echo "SECTION_CTX_ERR 读不到 $md" >&2; exit 2; }
sec="${thm%%.*}"                      # 33.1 -> 33
# 节标题行:`# 33. …`(允许 `#` 到 `###`)
start=$(grep -nE "^#{1,3} ${sec}\. " "$md" | head -1 | cut -d: -f1)
[ -n "$start" ] || { echo "SECTION_CTX_NONE 未找到第 ${sec} 节标题" >&2; exit 3; }
# 该定理行
end=$(awk -v s="$start" -v t="定理 ${thm}" 'NR>s && index($0,t) {print NR; exit}' "$md")
[ -n "$end" ] || { echo "SECTION_CTX_NONE 第 ${sec} 节内未找到「定理 ${thm}」" >&2; exit 4; }
echo "### 源卷第 ${sec} 节的 standing clause(节标题 → 定理 ${thm} 之间,逐字)"
echo "来源:\`${md}\` 第 ${start}–${end} 行"
echo '```'
sed -n "${start},$((end-1))p" "$md"
echo '```'
echo "**以上是节级载体条件。原子是切片,不携带它们 —— 凡公开类型里的前提能在此区间指出,即非新增假设。**"
