#!/bin/bash
# 器律⑨ + 第 7 条地层: 自查 SL-010「G artifact imports I fact」。
# 判据（读 RepositoryRules.Structure.cs:341-357）: 头部 generality=G 的模块，
# 其 import 传递闭包内不得出现 generality=I 或 E 的模块。
# 2026-09-04 立: 本会话 SL-010 三犯。前两次 import 多，我误归因为「聚合型模块」，
# 并在 brief 写下「import 超 5 行即自查」——第三次 FreePermutationObserverDistance
# import 仅 1 行照样违规，证明真判据是闭包地层跨度而非行数。
# usage: sl010_check.sh REPO LEAN_FILE
# 哨兵: SL010_OK 或 SL010_VIOLATION count=<n>
set -euo pipefail
REPO="${1:?usage: sl010_check.sh REPO LEAN_FILE}"; F="${2:?}"
cd "$REPO"
gen_of() { sed -n '1,20p' "$1" 2>/dev/null | grep -oiE 'generality:[[:space:]]*[GIE]' | head -1 | sed 's/.*[[:space:]]//' || true; }
[ "$(gen_of "$F")" = "G" ] || { echo "SL010_OK (not a G artifact)"; exit 0; }
seen=$(mktemp); queue=$(mktemp); next=$(mktemp)
trap 'rm -f "$seen" "$queue" "$next"' EXIT
echo "$F" > "$queue"; bad=0
while [ -s "$queue" ]; do
  : > "$next"
  while read -r cur; do
    grep -qxF "$cur" "$seen" 2>/dev/null && continue
    echo "$cur" >> "$seen"
    grep -oE '^import D5\.[A-Za-z0-9_.]+' "$cur" 2>/dev/null | sed 's/^import //' | while read -r m; do
      t=$(echo "$m" | tr '.' '/').lean
      [ -f "$t" ] || continue
      g=$(gen_of "$t")
      if [ "$g" = "I" ] || [ "$g" = "E" ]; then echo "VIOLATION: -> $t (generality=$g)"; fi
      echo "$t" >> "$next"
    done
  done < "$queue"
  cp "$next" "$queue"
done > /tmp/sl010.out 2>&1 || true
bad=$(grep -c "^VIOLATION" /tmp/sl010.out 2>/dev/null || echo 0)
cat /tmp/sl010.out | head -5
[ "$bad" -eq 0 ] && echo "SL010_OK" || echo "SL010_VIOLATION count=$bad"
