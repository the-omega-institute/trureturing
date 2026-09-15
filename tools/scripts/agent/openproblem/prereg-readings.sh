#!/usr/bin/env bash
# Collect every literature and dedupe reading a preregistration needs, and print them as a markdown
# block, each with the command that produced it and that command's exit code.
#
# The point is the direction of the arrow: the preregistration prose is written FROM this output, not
# written first and spot-checked afterwards. Three lanes were lost in one day (issues #8173, #8189 and
# #8143 / PR #8184) to readings that were composed before they were run, and to a "no proof exists"
# claim whose domain was never enumerated.
#
# usage: prereg-readings.sh A123456 [extra-grep-pattern ...]
#   A123456              the OEIS entry under consideration
#   extra-grep-pattern   further ERE patterns to dedupe against D5/Blueprint/Library/Problems,
#                        e.g. a proposed module name or a conclusion shape
#
# Writes markdown to stdout. Exits 0 when every reading was taken, 3 when at least one reading could not
# be taken (missing tool, network failure, quota); a reading that could not be taken is printed as
# UNAVAILABLE with its reason, never as an empty result. It is not this script's job to decide whether a
# candidate is open — it is its job to make every input to that decision visible and attributable.
set -uo pipefail

die() { printf 'prereg-readings: %s\n' "$*" >&2; exit 2; }

[ "$#" -ge 1 ] || die "usage: prereg-readings.sh A123456 [extra-grep-pattern ...]"
ANUM="$1"; shift
printf '%s' "$ANUM" | grep -qE '^A[0-9]{6}$' || die "first argument must look like A123456, got '$ANUM'"

for tool in curl git python3; do
  command -v "$tool" >/dev/null 2>&1 || die "required tool not found: $tool"
done

HERE="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
REPO="$(git -C "$HERE" rev-parse --show-toplevel)" || die "not inside a git repository"
SCANNER="$HERE/oeis-conjecture-scan.py"
DEGRADED=0
note_unavailable() { DEGRADED=1; printf -- '- **UNAVAILABLE** — %s\n' "$1"; }

printf '## 文献与去重读数(%s,由 tools/scripts/agent/openproblem/prereg-readings.sh 生成)\n\n' "$(date -u +%Y-%m-%d)"
printf '每条读数下面就是产生它的命令与该命令的退出码。本节由器输出,不由记忆撰写。\n\n'

# ---------- 1. the entry itself, every line that can carry a settlement ----------
printf '### 条目全文的 %%N / %%S / %%O / %%C / %%F / %%H / %%D 行\n\n'
printf '```\n$ curl -s "https://oeis.org/search?fmt=text&q=id:%s" | grep -E "^%%[NSOCFHD]"\n' "$ANUM"
ENTRY="$(curl -fsS "https://oeis.org/search?fmt=text&q=id:$ANUM" 2>/dev/null)"; ENTRY_RC=$?
if [ "$ENTRY_RC" -ne 0 ] || [ -z "$ENTRY" ]; then
  printf '```\n\n'; note_unavailable "OEIS 取回失败(curl exit $ENTRY_RC);该条目的全部行未读,不得写任何「无证明行」断言"
else
  printf '%s\n' "$ENTRY" | grep -E '^%[NSOCFHD]' || true
  printf 'EXIT=%d\n```\n\n' "$ENTRY_RC"
  LINKS="$(printf '%s\n' "$ENTRY" | grep -cE '^%H' || true)"
  printf -- '- `%%H` 行 **%s** 条,`%%D` 行 **%s** 条。\n' "$LINKS" "$(printf '%s\n' "$ENTRY" | grep -cE '^%D' || true)"
  if [ "${LINKS:-0}" -gt 0 ]; then
    printf -- '- **每一篇 `%%H` 论文都要取全文读过**,才能写「该文献不涉及此陈述」。只看摘要页不算:\n'
    printf -- '  A181666 的结算就写在它 `%%H` 链接论文的正文里,而摘要页只列出了序列号。取不到全文的条目\n'
    printf -- '  逐条标 `ASSUMED-UNVERIFIED` 并写明原因,不写「不涉及」。\n'
  else
    printf -- '- `%%H` 为空:没有链接论文可藏结算,这一维由上面的命令当场证实。\n'
  fi
  printf '\n'
fi

# ---------- 2. the repository's own settlement-marker scanner ----------
printf '### 结算标记扫描(仓内器)\n\n'
printf '```\n$ python3 tools/scripts/agent/openproblem/oeis-conjecture-scan.py --ids %s\n' "$ANUM"
if [ ! -f "$SCANNER" ]; then
  printf '```\n\n'; note_unavailable "扫描器不在 $SCANNER"
else
  SCAN="$(python3 "$SCANNER" --ids "$ANUM" 2>&1)"; SCAN_RC=$?
  if [ "$SCAN_RC" -ne 0 ]; then
    printf '%s\nEXIT=%d\n```\n\n' "$SCAN" "$SCAN_RC"; note_unavailable "扫描器退出码 $SCAN_RC"
  else
    printf '%s\n' "$SCAN" | python3 -c '
import json,sys
try: d=json.load(sys.stdin)
except Exception as exc: print("PARSE_FAILED:",exc); raise SystemExit
for e in d:
    print(e["a"], e["status"])
    for c in e["conjectures"]:
        print("  ", c["status"], "|", c["conjecture"][:150])
        for s in c.get("settlement_lines") or []: print("     SETTLEMENT:", s[:150])
'
    printf 'EXIT=%d\n```\n\n' "$SCAN_RC"
  fi
fi

# ---------- 3. arXiv ----------
# http://export.arxiv.org answers 301 with an empty body and `curl -fsS` exits 0 on it, so a naive
# `grep -c "<entry>"` prints 0 for a request that never reached the API. That is the shape CLAUDE.md
# §2.9 and the `unmeasured-must-not-look-like-zero` judgement forbid, and it is why this block uses
# https, follows redirects, asserts HTTP 200, and reads opensearch:totalResults rather than counting
# <entry> elements (which are capped by max_results and so cannot distinguish "none" from "many").
printf '### arXiv\n\n'
Q="$(python3 -c 'import urllib.parse,sys; print(urllib.parse.quote("all:\"%s\"" % sys.argv[1]))' "$ANUM")"
AX_URL="https://export.arxiv.org/api/query?search_query=$Q&max_results=20"
printf '```\n$ curl -sL -w "%%{http_code}" "%s"\n' "$AX_URL"
AX_BODY="$(mktemp)"; trap 'rm -f "$AX_BODY"' EXIT
AX_CODE="$(curl -sL -o "$AX_BODY" -w '%{http_code}' "$AX_URL" 2>/dev/null)"; AX_RC=$?
AX_TOTAL="$(grep -oE '<opensearch:totalResults[^>]*>[0-9]+' "$AX_BODY" 2>/dev/null | grep -oE '[0-9]+$' | head -1)"
if [ "$AX_RC" -ne 0 ] || [ "$AX_CODE" != "200" ] || [ -z "$AX_TOTAL" ]; then
  printf 'http_code=%s curl_exit=%s totalResults=%s\n```\n\n' "$AX_CODE" "$AX_RC" "${AX_TOTAL:-<absent>}"
  note_unavailable "arXiv 未返回可解析的 200 响应(http_code=$AX_CODE, curl exit=$AX_RC);**不得把它记成 0 命中**"
else
  printf 'http_code=200  opensearch:totalResults=%s\n```\n\n' "$AX_TOTAL"
  printf -- '- 读的是 `opensearch:totalResults`,不是 `<entry>` 元素数——后者被 `max_results` 截断,\n'
  printf -- '  区分不了「零」与「很多」。HTTP 状态码单独断言,因为 `http://export.arxiv.org` 会以 301\n'
  printf -- '  空响应作答,而空响应 grep 出来同样是 0。\n'
  printf -- '- 按 A 号查 arXiv 命中少是常态;它不能替代按**数学内容**的检索,后者须另行申报。\n\n'
fi

# ---------- 4. repository dedupe, pinned to a revision ----------
printf '### 仓内去重\n\n'
git -C "$REPO" fetch -q origin 2>/dev/null
DEV="$(git -C "$REPO" rev-parse origin/dev 2>/dev/null)" || DEV=""
if [ -z "$DEV" ]; then
  note_unavailable "取不到 origin/dev,去重读数没有可钉的修订"
else
  printf -- '钉在 `origin/dev` `%s`。\n\n' "$DEV"
  printf '| 命令 | 命中行 |\n| --- | ---: |\n'
  for pat in "$ANUM" "$@"; do
    N="$(git -C "$REPO" grep -n -I -E "$pat" "$DEV" -- D5 Blueprint Library Problems 2>/dev/null | wc -l | tr -d ' ')"
    printf '| `git grep -n -I -E '"'"'%s'"'"' %s -- D5 Blueprint Library Problems` | %s |\n' "$pat" "${DEV:0:10}" "$N"
  done
  printf '\n- 命中非零不等于撞车,须逐条读:同一常数可能属别的恒等式。命中为零也只覆盖所查的模式,\n'
  printf -- '  **按结论形状的检索要另外做**,只按 A 号 grep 会漏掉换了名字的同一命题。\n\n'
fi

# ---------- 5. pinned Mathlib ----------
printf '### 钉版 Mathlib\n\n'
ML="$REPO/.lake/packages/mathlib/Mathlib"
if [ ! -d "$ML" ]; then
  note_unavailable "钉版 Mathlib 不在 $ML(该树尚未 provision)"
else
  printf '```\n'
  for pat in "$@"; do
    N="$(grep -rn --include='*.lean' -iE "$pat" "$ML" 2>/dev/null | wc -l | tr -d ' ')"
    printf '$ grep -rn --include=*.lean -iE %s .lake/packages/mathlib/Mathlib  -> %s\n' "$pat" "$N"
  done
  [ "$#" -eq 0 ] && printf '(未给检索模式;先库后证要求按拟议声明的名字与结论形状各查一次)\n'
  printf '```\n\n'
fi

printf -- '---\n\n'
if [ "$DEGRADED" -ne 0 ]; then
  printf '**本次有读数未能取得(见上面的 UNAVAILABLE 行)。** 按 CLAUDE.md §3.1 记具名\n'
  printf '`open(wait-for-capability)`,不得报 search-complete;按 §2.9,未取得的读数写明「没测什么、为什么」,\n'
  printf '不留空白也不用语气词代替。\n'
  exit 3
fi
printf '全部读数均已取得。仍须人工完成的是:每篇 `%%H` 论文的全文阅读,以及按结论形状(而非 A 号)的\n'
printf '仓内与上游检索——两者都不是本器能代劳的。\n'
