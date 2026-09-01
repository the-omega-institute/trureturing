#!/bin/bash
# 器律⑨ + [[atom-check-both-sides]]: Lean 侧查重 —— 账目侧 residual-open 结构性落后 Lean 侧约 3 倍
# (2026-09-01 实测 D5 2832 个 .lean vs absorbed-closed 约 950),只查账目必然反复撞车。
# 判据: 理论卷标题的 ASCII 括注(作者自给的英文名)对 D5 模块名+声明名全语料做子串匹配。
# 三态, 不冒领 (第 4 条): CLEAN=关键词无命中 / HIT=有命中 / UNKNOWN=标题无 ASCII 括注,
#   本器拿不到查重键,不下结论。UNKNOWN 不是"干净",是"本器查不了",须席位自行查。
# 全仓实测(2026-09-01, 28 卷): clean=119 unknown=1588 hit=849, 可判总数 2556
#   (residual-open 约 15,000 条, 故只有约 17% 是定理级单元)。
#   hit=849 是本器最有价值的输出: 这些 atom 已有对应 Lean, 只差 cover 绑账。
# 适用边界: 只有标题带作者自给英文名的卷可判 —— 其余归 UNKNOWN。
#   pzg-v170 的 1928 个 atom 行数中位数仅 3(1827 条 <12 行), 是研究日志卷而非定理集,
#   entropy-info-primes-o5 的 54 条中位数 1 行; 这两卷的 0 是真 0, 不是盲区。
# 非承重: CLEAN 也只排除同名, 排除不了异名覆盖; 席位仍须走完 cover 查重五路。
# usage: atom_dedup.sh REPO VOLUME OUT.tsv   (sentinel: DEDUP_OK clean=<n> hit=<n>)
set -euo pipefail
[ $# -eq 3 ] || { echo "DEDUP_USAGE: atom_dedup.sh REPO VOLUME OUT.tsv" >&2; exit 64; }
[ -d "$1/.git" ] || [ -f "$1/.git" ] || { echo "DEDUP_BAD_REPO=$1" >&2; exit 65; }
[ -d "$1/Meta/Digestion/backfill/$2/residual-open" ] || { echo "DEDUP_BAD_VOLUME=$2" >&2; exit 66; }
[ -d "$1/D5" ] || { echo "DEDUP_NO_D5=$1/D5" >&2; exit 67; }
python3 -X utf8 - "$@" <<'PY'
import re, sys, pathlib, subprocess
repo, volume, out = sys.argv[1:4]
R = pathlib.Path(repo)

# --- D5 侧语料: 模块名 + 顶层声明名 (Lean 侧"写没写") ---
names = [p.stem for p in (R / "D5").rglob("*.lean")]
if not names:
    print("DEDUP_EMPTY_D5", file=sys.stderr); sys.exit(68)
decl = re.compile(r'^(?:theorem|lemma|def|structure|abbrev|instance|noncomputable def)\s+([A-Za-z_][A-Za-z0-9_\']*)')
for p in (R / "D5").rglob("*.lean"):
    for line in p.read_text(errors="replace").splitlines():
        m = decl.match(line)
        if m: names.append(m.group(1))
corpus = "\n".join(names).lower()

# 太泛的词单命中即假阳, 故不作为查重键
STOP = {"the","of","and","for","with","theorem","criterion","existence","lemma","principle",
        "property","condition","form","case","type","general","exact","local","global","new",
        "law","rule","test","value","map","set","one","two","all","non","via","under","from"}
# 「定义」也是可形式化对象 (Lean 的 def 与 theorem 同为承重产出); 漏掉它会把整卷判空 ——
# 2026-09-01 实测 formal-concept-dynamics 有 966 条因此被误滤, 其中含 ## 定义 431.3。
PROP = re.compile(r'定理|命题|引理|推论|定义')
MATHCMD = re.compile(r'\\[A-Za-z]{2,}')

cas = R / "Meta/Digestion/atoms/sha256"
rows = []
for y in sorted((R / "Meta/Digestion/backfill" / volume / "residual-open").glob("*.yaml")):
    f = cas / y.stem
    if not f.is_file(): continue
    txt = f.read_text(errors="replace"); lines = txt.splitlines()
    if len(lines) < 12: continue                      # 截断/碎片 atom (见 #4410)
    title = lines[0].strip()
    if not re.match(r'^#+\s', title): continue        # 无标题者非独立命题单元
    # 定理级: 标题含定理级词, 或正文含之 (中文标题卷的标题只有编号+描述)
    if not (PROP.search(title) or PROP.search(txt)): continue
    # 数学密度: 数 LaTeX 命令, 不数分隔符。
    # 分隔符逐卷不同 —— adelic 用 $$, FPOD 用 \[ ... \], formal-concept-dynamics 用裸 [ ... ]
    # (markdown 转换丢了反斜杠)。拿分隔符当代理, 每换一个卷就失效一次:
    # 2026-09-01 实测先后误判 FPOD 182 条、concept-dynamics 336 条为 math=0。
    # \word 形式的 LaTeX 命令(\boxed \left \lceil \sum \log ...)是跨卷稳定的特征。
    math = sum(1 for l in lines if ('$' in l or MATHCMD.search(l)))
    if math < 6: continue
    kws = [w.lower() for w in re.findall(r'[A-Za-z][A-Za-z\-]{2,}', title)
           if w.lower() not in STOP and len(w) >= 4]
    if not kws:                                       # 无 ASCII 括注 => 本器无查重键
        rows.append(("UNKNOWN", math, len(lines), y.stem, title[:80], "", ""))
        continue
    # Lean 名是 CamelCase 连写 (PrimePowers), 卷里的括注常带连字符 (prime-power);
    # 直接子串匹配会被连字符打断 —— 2026-09-01 实测漏判: 推论 158.1 的 prime-power
    # 明明已由 D5/S3/Factorization/PrimePowers/AlternatingFiveResidualSeparation.lean 覆盖,
    # 却报 CLEAN, 白派一条 lane。故连字符形与连写形都要试。
    def _hit(w):
        return w in corpus or (('-' in w) and w.replace('-', '') in corpus)
    hits = [w for w in kws if _hit(w)]
    rows.append(("HIT" if hits else "CLEAN", math, len(lines), y.stem, title[:80],
                 ",".join(kws), ",".join(hits)))

rows.sort(key=lambda r: ({"CLEAN":0,"UNKNOWN":1,"HIT":2}[r[0]], -r[1]))
with open(out, "w", encoding="utf-8") as fh:
    fh.write("status\tmath\tlines\tatom_id\ttitle\tkeywords\thits\n")
    for r in rows: fh.write("\t".join(map(str, r)) + "\n")
c = sum(1 for r in rows if r[0] == "CLEAN")
u = sum(1 for r in rows if r[0] == "UNKNOWN")
print(f"DEDUP_OK clean={c} unknown={u} hit={len(rows)-c-u} corpus_names={len(names)} volume={volume}")
PY
