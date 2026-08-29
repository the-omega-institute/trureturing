#!/usr/bin/env bash
# scope-freeze-delta.sh BASE -- 把 accepted 目录收窄到「本分支真正新增的冻结条目」
#
# 背景(issue #3888):base 含 legacy(v4)分片时,ledger-append 走 ReplaceEventFiles,
# 把 legacy 排除出最终集合并为其重新生成 v5 条目 ⟹ 全量重写;
# 而 admission 的 Legacy 授权器要求 base 全为 legacy ⟹ 混合态必然被拒。
# 先例:PR #3696「ledger: scope the freeze delta to this branch's twenty-four events」。
#
# 本器做三件事,逐条 fail-fast:
#   1) 恢复所有「dev 上有、本分支删掉」的分片(append-only,第〇节冻结律);
#   2) 删除所有「本分支新增、但其 descriptor_selector 不指向本分支新增 .lean」的分片;
#   3) 打印保留下来的条目,供 PR 说明引用。
set -euo pipefail
BASE="${1:?usage: scope-freeze-delta.sh BASE}"
ACC="Golden/Frozen/accepted"
git rev-parse --verify -q "$BASE" >/dev/null || { echo "FATAL: base 不可解析: $BASE" >&2; exit 2; }
[ -d "$ACC" ] || { echo "FATAL: 不在仓根或无 $ACC" >&2; exit 2; }

# 本分支新增的 Lean 模块(相对 BASE)
NEWLEAN=()
while IFS= read -r __l; do [ -n "$__l" ] && NEWLEAN+=("$__l"); done < <(git diff --name-only --diff-filter=A "$BASE"...HEAD -- 'D5/**/*.lean')
printf 'SCOPE new_lean_modules=%d\n' "${#NEWLEAN[@]}"
for m in "${NEWLEAN[@]}"; do printf '  NEW_LEAN %s\n' "$m"; done

restored=0; dropped=0; kept=0
while IFS=$'\t' read -r st path; do
  case "$st" in
    D)  # dev 上有、这里被删 → 恢复(不得改写历史冻结条目)
        git cat-file -p "$BASE:$path" > "$path"
        restored=$((restored+1)) ;;
    A)  # 本分支新增 → 只保留指向本分支新模块的
        sel=$(python3 -c "
import json,sys
p=json.load(open('$path')).get('payload',{})
print(p.get('descriptor_selector') or p.get('input',{}).get('descriptor_selector') or '')" 2>/dev/null || true)
        keep=no
        for m in "${NEWLEAN[@]}"; do [ "$sel" = "$m" ] && keep=yes && break; done
        if [ "$keep" = yes ]; then kept=$((kept+1)); printf '  KEEP %s -> %s\n' "${path##*/}" "$sel"
        else rm -f "$path"; dropped=$((dropped+1)); fi ;;
  esac
done < <(git diff --name-status "$BASE"...HEAD -- "$ACC")

printf 'SCOPE_RESULT restored=%d dropped=%d kept=%d\n' "$restored" "$dropped" "$kept"
[ "$kept" -gt 0 ] || { echo "FATAL: 收窄后没有任何本分支的冻结条目,不应发生" >&2; exit 3; }
