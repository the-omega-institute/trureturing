#!/bin/bash
# 器律⑨: prime/number-theory 选题器 —— 从 residual-open 全卷筛出「素数类 ∧ 定理级 ∧ 非碎片」的
# atom,并按 best-odds 信号排序。选题是长期形式化战役的真瓶颈,而 residual-open 的条数不是候选数:
# 2026-09-05 实测 ~19k 条 residual-open 里,过本器筛的素数类候选只有 256 条。
#
# 排序信号(纯启发式,非承重;第 3 条:美是罗盘不是判卷):
#   good  = 自带推理链与构造的词(因为/所以/取/令/存在素数/构造/反例/有限/恰好/唯一/介值/置换/同余/…)
#   heavy = 重型解析机器的词(RH/Weil/trace formula/谱/算子/渐近/素数定理/全纯/…)
#   proof = 原文自带 ### 证明 段或 ∎
#   score = good*2 + proof*6 - heavy*3
# 依据是 skills/codex-formalize/SKILL.md 步骤 1 的 claim class:
# 「自带数据的具体证书/计算类」落地率最高,「无机器方案的重型普遍命题」要么超时要么编造。
#
# 本器只排序,不下「可做」的结论(第 4 条不冒领):CLEAN 不排除异名覆盖,高分不蕴含非 bind-only。
# 席位仍须走 SKILL 步骤 1→3(权威原文 / 回声 / 先库后证)与 CLAUDE.md 5⁗ 的逃逸见证判定。
#
# usage: prime_pick.sh REPO OUT.tsv [EXCLUDE.txt]
#   EXCLUDE.txt = 每行一个 atom_id(见 refresh_exclusions.sh / inflight_mods.sh)
# 哨兵: PRIME_PICK_OK ranked=<n> scanned=<n> excluded=<n>
set -euo pipefail
[ $# -ge 2 ] || { echo "PRIME_PICK_USAGE: prime_pick.sh REPO OUT.tsv [EXCLUDE.txt]" >&2; exit 64; }
[ -d "$1/.git" ] || [ -f "$1/.git" ] || { echo "PRIME_PICK_BAD_REPO=$1" >&2; exit 65; }
[ -d "$1/Meta/Digestion/backfill" ] || { echo "PRIME_PICK_NO_BACKFILL=$1" >&2; exit 66; }
[ -d "$1/Meta/Digestion/atoms/sha256" ] || { echo "PRIME_PICK_NO_CAS=$1" >&2; exit 67; }
[ $# -lt 3 ] || [ -f "$3" ] || { echo "PRIME_PICK_BAD_EXCLUDE=$3" >&2; exit 68; }
python3 -X utf8 - "$@" <<'PY'
import re, sys, pathlib
repo, out = sys.argv[1:3]
excl_path = sys.argv[3] if len(sys.argv) > 3 else None
R = pathlib.Path(repo)
cas = R / "Meta/Digestion/atoms/sha256"

excluded = set()
if excl_path:
    excluded = {l.strip() for l in open(excl_path, encoding="utf-8") if l.strip()}

KW = re.compile(r'素数|prime|Prime|zeta|Zeta|Dirichlet|Legendre|Jacobi|同余|CRT|中国剩余|'
                r'Fibonacci|Zeckendorf|Galois|单位群|类群|Frobenius|二次剩余|欧拉|Euler|'
                r'Mobius|Möbius|Mertens|Mangoldt|Chebyshev|孪生|twin|因子|divisor|整除')
PROP = re.compile(r'定理|命题|引理|推论')
MATHCMD = re.compile(r'\\[A-Za-z]{2,}')
GOOD = re.compile(r'因为|由于|所以|因此|取|令|存在素数|构造|反例|有限|恰好|唯一|介值|不动点|'
                  r'置换|归纳|计数|余数|同余|整除|奇偶')
HEAVY = re.compile(r'RH|Riemann|解析延拓|测度|分布|Weil|trace formula|谱|算子|Hilbert|Banach|'
                   r'渐近|Mertens|素数定理|积分|收敛半径|全纯|亚纯')
PROOF = re.compile(r'###\s*证明|证明[:：]|∎')

scanned = 0
rows = []
for vol in sorted((R / "Meta/Digestion/backfill").iterdir()):
    ro = vol / "residual-open"
    if not ro.is_dir():
        continue
    for y in sorted(ro.glob("*.yaml")):
        scanned += 1
        if y.stem in excluded:
            continue
        f = cas / y.stem
        if not f.is_file():
            continue
        text = f.read_text(errors="replace")
        lines = text.splitlines()
        # 碎片/截断 atom(见 #4410)与超长叙事都不是独立可形式化单元
        if not (12 <= len(lines) <= 130):
            continue
        title = lines[0].strip()
        if not re.match(r'^#+\s', title):
            continue
        if not PROP.search(title + text[:400]):
            continue
        if not KW.search(text):
            continue
        # 数学密度按 \word 形式的 LaTeX 命令数,不按分隔符 —— 分隔符逐卷不同,拿它当代理每换一卷失效一次
        math = sum(1 for l in lines if '$' in l or MATHCMD.search(l))
        if math < 5:
            continue
        good = len(GOOD.findall(text))
        heavy = len(HEAVY.findall(text))
        proof = 1 if PROOF.search(text) else 0
        rows.append((good * 2 + proof * 6 - heavy * 3, good, heavy, proof,
                     math, len(lines), y.stem, vol.name, title[:70]))

rows.sort(key=lambda r: (-r[0], -r[4]))
with open(out, "w", encoding="utf-8") as fh:
    fh.write("score\tgood\theavy\tproof\tmath\tlines\tatom_id\tsource_id\ttitle\n")
    for r in rows:
        fh.write("\t".join(map(str, r)) + "\n")
print(f"PRIME_PICK_OK ranked={len(rows)} scanned={scanned} excluded={len(excluded)}")
PY
