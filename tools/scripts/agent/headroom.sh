#!/bin/bash
# SL-003 余量普查:哪些文件逼近行数硬线、哪些目录逼近文件数上限。
#
# 为什么是器不是记忆:本会话手工量了四次(#5563/#5570/#5576/#5579 各一次),
# 且撞过一次线(#5433 把 752 行文件加到 903 行,当场被判红)。器律③「重复三遍先铸器」。
#
# **阈值从判官源码读,不硬编码** —— owner 调过阈值,而记忆里的旧值会把人带偏
# (本仓判例:headroom-includes-directory-file-count「动手前读源不读本条」)。
#
# 用法: headroom.sh [REV] [MARGIN]     缺省 REV=origin/dev,MARGIN=50
#       headroom.sh --selftest         验阈值解析与判据
set -u
SRC='tools/StrataLint.Engine/Rules/RepositoryRules.Structure.cs'

read_limits() {  # $1=rev;输出 "LINE DIR"
  local rev="$1" body
  body="$(git show "$rev:$SRC" 2>/dev/null)" || return 1
  local L D
  L="$(printf '%s' "$body" | sed -n 's/.*ArtifactHardLineLimit *= *\([0-9][0-9]*\).*/\1/p' | head -1)"
  D="$(printf '%s' "$body" | sed -n 's/.*DirectoryFileLimit *= *\([0-9][0-9]*\).*/\1/p' | head -1)"
  [ -n "$L" ] && [ -n "$D" ] || return 1
  printf '%s %s' "$L" "$D"
}

if [ "${1:-}" = "--selftest" ]; then
  # 阳性:能从当前 dev 解析出两个阈值,且都是正整数
  if lim="$(read_limits origin/dev)"; then
    set -- $lim
    if [ "$1" -gt 0 ] 2>/dev/null && [ "$2" -gt 0 ] 2>/dev/null; then
      echo "  ok   解析阈值 行=$1 目录=$2"
    else echo "  FAIL 阈值非正整数: $lim"; exit 1; fi
  else echo "  FAIL 无法从 $SRC 解析阈值"; exit 1; fi
  # 阴性:不存在的 rev 必须 fail-closed 而不是给出默认值
  if read_limits 'refs/heads/__no_such_ref__' >/dev/null 2>&1; then
    echo "  FAIL 不存在的 rev 未 fail-closed"; exit 1
  else echo "  ok   不存在的 rev 已 fail-closed"; fi
  echo "SELFTEST_PASS"; exit 0
fi

REV="${1:-origin/dev}"; MARGIN="${2:-50}"
lim="$(read_limits "$REV")" || { echo "HEADROOM_LIMITS_UNREADABLE rev=$REV src=$SRC" >&2; exit 2; }
set -- $lim; LINE_LIMIT="$1"; DIR_LIMIT="$2"
echo "rev=$REV  行数硬线=$LINE_LIMIT  目录上限=$DIR_LIMIT  报告阈值=余量<$MARGIN"

echo "--- 文件(按余量升序) ---"
git ls-tree -r --name-only "$REV" -- tools/ | grep -E '\.(cs|sh)$' | while read -r f; do
  n="$(git show "$REV:$f" | wc -l | tr -d ' ')"
  left=$((LINE_LIMIT - n))
  [ "$left" -lt "$MARGIN" ] && printf '%d\t%d\t%s\n' "$left" "$n" "${f#tools/}"
done | sort -n | awk -F'\t' '{printf "  余量%4d  %4d 行  %s\n",$1,$2,$3}'

echo "--- 目录(按余量升序) ---"
git ls-tree -r --name-only "$REV" -- tools/ | grep '\.cs$' | sed 's|/[^/]*$||' \
  | sort | uniq -c | while read -r c d; do
  left=$((DIR_LIMIT - c))
  [ "$left" -lt "$MARGIN" ] && printf '%d\t%d\t%s\n' "$left" "$c" "${d#tools/}"
done | sort -n | awk -F'\t' '{printf "  余量%4d  %3d 个  %s\n",$1,$2,$3}'
