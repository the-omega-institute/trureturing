#!/bin/bash
# 器律⑨: quarantine 记录的写前自检。**在写入账本之前跑,不是之后。**
#
# 立器案由(2026-09-06,同一形态三次):
#   ① #5744 的一条记录在 justification 里引用 missing_statement / searches,
#      而落盘的 receipts.quarantine 只有 justification / reentry_condition / blocker_class
#      三个键——被引用的内容根本不在账本里,读者读不到。独立评审席抓出。
#   ② 同一形态复发,而我的自查写在 git commit 之后,坏内容已推到远端才报错。
#   ③ 修复时只扫了 justification,漏了 reentry_condition,又推了一次。
# 三次的共同根因不是"忘了",是**检查的位置与范围都错了**:该在写入前跑、该覆盖两个字段。
#
# 检查项(逐条 fail-fast,任一不过即非零退出):
#   1. 悬空引用   —— 正文提到 missing_statement / searches below / see below 一类
#                     指向未落盘字段的措辞(账本 schema 只有那三个键)
#   2. SL-019 词表 —— anomal|exception|failure|(?<!ex)tension,命中即 admission 判红
#   3. 结构      —— blocker_class 取值合法、coverage_gids 为空
#   4. 冲突      —— 同一条目不得已有 quarantine,也不得有 cover_disposition(门禁止共存)
#   5. 位置      —— 必须仍在 residual-open
#   6. 仓内引用   —— 正文里的 `D5/<路径>.<声明>` 必须真能解析:该 .lean 存在 ∧ 其中确有该声明。
#                     立项案由(2026-09-06):同一批记录我手搓了两次校验器,两次都是器坏不是数据坏——
#                     ① 把 `Foo.lean` 的扩展名当成声明名 `lean`;② 只认 `theorem` 而漏掉 `lemma`。
#                     两个 bug 都会报出假的"悬空引用"。故把它铸进器里,并为这两种形态各留一条阴性对照。
#                     **fail-open(写在这里就是反例集合)**:①引用前 60 字内出现否定词
#                     (未核到/不存在/未命中/rejected attempt/retracted/…)即跳过——记录合法地
#                     报告某物缺席时不该判红,代价是真悬空引用若恰好跟在否定词后会被漏掉;
#                     ②只查 `D5/**`,不查 mathlib(要 .lake 在位)、不查 Blueprint/Meta/Golden 路径
#                     (那些常被合法地报告为缺席);③声明名以文本形式在该 .lean 内匹配,
#                     `to_additive` 之类由属性生成的名字不在本器射程。
#
# --selftest: 12 条夹具,预期红数写在跑之前(六元组第六项)——
#   F1 悬空 .lean 路径=1 / F2 悬空声明=1 / F3 真 theorem=0 / F4 真 lemma=0
#   F5 只提 .lean 路径=0 / F6 缺失声明但前有否定词=0 / F7 Blueprint 前缀路径不匹配=0
#   F8 引用已撤回的尝试=0 / F9 「的」形真定理=0 / F10 「的」形假声明=1
#   F11 无 GID 前缀的「的」形=0 / F12 **已知假阳**:账本字段名跟在「的」后=1
#   F12 是故意钉住的假阳:`X 的 statement_id 为 …` 会被判成声明引用。当前全库 0 次发生
#   (实测 459 条记录、633 条配对、判红 0),故按第 20″ 条不预先加停用词表;
#   真出一次再加,届时 F12 的预期由 1 改 0。本器是写前自检不是门,假阳的代价是我多看一眼。
#
# usage: quarantine_lint.sh REPO [FILE...]      # 不给 FILE 则扫 REPO 里全部带 quarantine 的条目
#        quarantine_lint.sh REPO --selftest     # 跑夹具,验本器仍能判红
# 哨兵: QUARANTINE_LINT_OK checked=<n>   /   失败时 QUARANTINE_LINT_FAILED findings=<n>
set -euo pipefail
REPO="${1:-}"
[ -n "$REPO" ] || { echo "QUARANTINE_LINT_USAGE: quarantine_lint.sh REPO [FILE...]" >&2; exit 64; }
[ -d "$REPO/.git" ] || [ -f "$REPO/.git" ] || { echo "QUARANTINE_LINT_BAD_REPO=$REPO" >&2; exit 65; }
[ -d "$REPO/Meta/Digestion/backfill" ] || { echo "QUARANTINE_LINT_NO_BACKFILL=$REPO" >&2; exit 66; }
shift || true
cd "$REPO"
python3 -X utf8 - "$@" <<'PY'
import sys, re, glob, pathlib
try:
    import yaml
except ImportError:
    print("QUARANTINE_LINT_NO_YAML", file=sys.stderr); sys.exit(67)

DANGLING = ("missing_statement", "searches below", "see below", "as listed below",
            "carried_owners", "sibling_absent_evidence", "evidence_commands",
            "sibling_checked", "why_not_synthesizable")
SL019 = re.compile(r"anomal|exception|failure|(?<!ex)tension", re.I)
CLASSES = {"multi-clause-guard", "missing-prerequisite", "already-covered"}

# --- 检查 6:仓内引用解析 -------------------------------------------------
# 声明行文法。必须认 lemma——只认 theorem 是 2026-09-06 手搓校验器的第二个 bug,
# 它把一条真实存在的 `lemma xiReading_eq_zero_iff_nontrivial` 报成了悬空引用。
DECL_KW = r"(?:theorem|lemma|def|abbrev|structure|inductive|instance|axiom|opaque)"
DECL_LINE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)\s+)*"
    + DECL_KW + r"\s+([A-Za-z_][A-Za-z0-9_'!?]*)")
# 扩展名不是声明名。把 `Foo.lean` 拆成 (Foo, lean) 再去找名为 `lean` 的声明,
# 是同一天手搓校验器的第一个 bug,它一次报出 11 条假的悬空引用。
FILE_EXT = {"lean", "yaml", "json", "cs", "md", "sh", "toml", "txt", "jsonl"}
# 左锚必须有:没有它,`Blueprint/D5/…/Foo.scribe.cs` 会从中间开始匹配并在 `.scribe` 截断,
# 报出 17 条假的"声明 scribe 不存在"。这是同一天第三个手搓校验器 bug,故连同理由钉在这里。
#
# 粘连词是本器的第二层(2026-09-06,同症状第二次即修根因):记录点名载体有两种写法——
#   ① `D5/<路径>.<声明>`      ② `GID D5/<路径> 的 <声明>`(中文「的」分隔)
# 首版只认 ①,于是在一整批用 ② 的记录上**空跑**:把其中一个真实引用改成假名,findings 仍为 0。
# 这不是想象出来的缺口,是变异证明当场测出来的;实测该批 17→32,即多看见 15 条引用。
# **粘连词只许 `.` 与 `的`,不许 `\s+`**:放宽到空白会把散文里的 `D5 search` / `D5 and` /
# `D5 files` 一并配成引用,实测全库因此多出 54 条假红。
REPO_REF = re.compile(
    r"(?<![A-Za-z0-9_/])(D5/[A-Za-z0-9_/]+?)(?:\.|\s*的\s*)[`']?([A-Za-z_][A-Za-z0-9_']*)")
# 记录合法地报告某物缺席时不判红(fail-open,见文件头反例集合)
# 跳过语境分两类,都由实测发现,不是预想:
#   ① 缺席报告——记录合法地写"未核到 X"。
#   ② 撤回战史——记录合法地写"rejected attempt `D5/…`"/"retracted module `D5/…`"。
#      第 12 条要求留失败战史;判它红会逼作者删掉"什么试过且被否决"这一最有用的部分。
#      立项当日全库 6 条命中**全部**属此类,逐条读过原文确认。
NEG = re.compile(r"未核到|未找到|未搜到|不存在|未命中|缺失|尚未|零命中|未见|没有找到|"
                 r"已撤回|被撤回|撤销|"
                 r"no such|not found|exit 1|退出 1|"
                 r"rejected attempt|retracted|withdrawn|reverted", re.I)

_decl_cache = {}


def declared_names(lean_path):
    if lean_path not in _decl_cache:
        names = set()
        try:
            for line in pathlib.Path(lean_path).read_text(
                    encoding="utf-8", errors="replace").splitlines():
                m = DECL_LINE.match(line)
                if m:
                    names.add(m.group(1))
        except OSError:
            names = None
        _decl_cache[lean_path] = names
    return _decl_cache[lean_path]


def check_repo_refs(text, bad):
    for m in REPO_REF.finditer(text):
        module, tail = m.group(1), m.group(2)
        ref = f"{module}.{tail}"
        if NEG.search(text[max(0, m.start() - 60):m.start()]):
            continue
        if tail in FILE_EXT:
            if not pathlib.Path(ref).is_file():
                bad(f"repo path does not exist: {ref}")
            continue
        lean = f"{module}.lean"
        names = declared_names(lean)
        if names is None:
            bad(f"repo reference does not resolve: {ref} (no such module {lean})")
        elif tail not in names:
            bad(f"repo reference does not resolve: {ref} "
                f"({tail} is not declared in {lean})")


def check_payload(q, doc, path, bad):
    text = f"{q.get('justification','')} {q.get('reentry_condition','')}"
    for token in DANGLING:
        if token in text:
            bad(f"dangling reference to a field the ledger does not persist: {token!r}")
    hits = sorted({m.group(0) for m in SL019.finditer(text)})
    if hits:
        bad(f"SL-019 anomaly-bearing words in quarantine payload: {hits}")
    # SL-016 canonical emission: BackfillInventoryWriter.Scalar throws on these shapes.
    # Landed case 2026-09-06: " #check" (a Lean command) and " #{y in Q ...}" (cardinality
    # notation) both tripped the YAML inline-comment sequence and rejected the whole PR.
    for key in ("justification", "reentry_condition"):
        value = " ".join((q.get(key) or "").split())
        if not value:
            continue
        if " #" in value:
            idx = value.index(" #")
            bad(f"{key}: contains ' #', which BackfillInventoryWriter cannot emit "
                f"canonically (YAML inline comment) at {idx}: "
                f"...{value[max(0, idx - 30):idx + 24]}...")
        if value[0] in "-?:!&*#{[":
            bad(f"{key}: starts with {value[0]!r}, which BackfillInventoryWriter rejects")
        if value[0].isspace() or value[-1].isspace():
            bad(f"{key}: leading or trailing whitespace is rejected by the writer")
    if q.get("blocker_class") not in CLASSES:
        bad(f"blocker_class not in {sorted(CLASSES)}: {q.get('blocker_class')!r}")
    for key in ("justification", "reentry_condition"):
        if not (q.get(key) or "").strip():
            bad(f"empty {key}")
    if (doc or {}).get("coverage_gids"):
        bad("coverage_gids must be empty on a quarantined entry")
    if "cover_disposition" in ((doc or {}).get("receipts") or {}):
        bad("cover_disposition cannot coexist with quarantine (BackfillInventoryLoader)")
    if "/residual-open/" not in path:
        bad("quarantine entry is not under residual-open")
    check_repo_refs(text, bad)


def find_anchor(keyword):
    """现找一个含该关键字声明的 D5 模块。位置不硬编码(第 5' 条:位置锚死于变更)。"""
    pat = re.compile(r"^\s*" + keyword + r"\s+([A-Za-z_][A-Za-z0-9_']*)")
    for f in sorted(glob.glob("D5/**/*.lean", recursive=True)):
        for line in pathlib.Path(f).read_text(encoding="utf-8", errors="replace").splitlines():
            m = pat.match(line)
            if m:
                return f[:-len(".lean")], m.group(1)
    return None, None


def selftest():
    thm_mod, thm = find_anchor("theorem")
    lem_mod, lem = find_anchor("lemma")
    if not thm_mod or not lem_mod:
        print("QUARANTINE_LINT_SELFTEST_NO_ANCHOR", file=sys.stderr); return 70
    base = {"blocker_class": "multi-clause-guard", "reentry_condition": "x"}
    cases = [
        ("F1 dangling .lean path", 1, "载体见 D5/NoSuchDir/NoSuchModule.lean 全文。"),
        ("F2 dangling declaration", 1, f"载体是 {thm_mod}.no_such_declaration_xyz 这条定理。"),
        ("F3 real theorem", 0, f"载体是 {thm_mod}.{thm},实读其冻结状态片。"),
        ("F4 real lemma", 0, f"载体是 {lem_mod}.{lem},实读其冻结状态片。"),
        ("F5 real .lean path only", 0, f"已 cat {thm_mod}.lean 全文。"),
        ("F6 absent decl after negation", 0,
         f"未核到 {thm_mod}.no_such_declaration_xyz 这条声明。"),
        ("F7 Blueprint-prefixed path not matched", 0,
         f"已读 Blueprint/{thm_mod}.scribe.cs 与其 .md 投影。"),
        ("F8 retracted-attempt citation", 0,
         "Rejected attempt: `D5/NoSuchDir/NoSuchModule.lean`, retracted at commit deadbeef."),
        ("F9 GID-de form, real theorem", 0, f"GID {thm_mod} 的 {thm} 已实读其冻结状态片。"),
        ("F10 GID-de form, absent decl", 1,
         f"GID {thm_mod} 的 no_such_declaration_xyz 承载该子句。"),
        ("F11 de form without GID prefix, real lemma", 0, f"{lem_mod} 的 {lem} 是近似命中。"),
        ("F12 KNOWN FALSE POSITIVE: ledger field after 的", 1,
         f"{thm_mod} 的 statement_id 为 sha256:0000。"),
    ]
    bad_rows = 0
    for name, expected, just in cases:
        got = []
        payload = dict(base, justification=just)
        check_payload(payload, {"coverage_gids": [], "receipts": {}},
                      "Meta/Digestion/backfill/v/residual-open/x.yaml",
                      lambda m: got.append(m))
        mark = "ok " if len(got) == expected else "RED"
        if len(got) != expected:
            bad_rows += 1
        print(f"  [{mark}] {name}: expected={expected} got={len(got)}"
              + ("" if len(got) == expected else " :: " + " | ".join(got)))
    print(f"  anchors: theorem={thm_mod}.{thm}  lemma={lem_mod}.{lem}")
    if bad_rows:
        print(f"QUARANTINE_LINT_SELFTEST_FAILED mismatched={bad_rows}", file=sys.stderr)
        return 1
    print(f"QUARANTINE_LINT_SELFTEST_OK cases={len(cases)}")
    return 0


args = sys.argv[1:]
if args and args[0] == "--selftest":
    sys.exit(selftest())

files = args
if not files:
    files = [p for p in glob.glob("Meta/Digestion/backfill/*/*/*.yaml")
             if "quarantine" in pathlib.Path(p).read_text(encoding="utf-8", errors="replace")]

findings = 0
checked = 0
for p in files:
    raw = pathlib.Path(p).read_text(encoding="utf-8", errors="replace")
    doc = yaml.safe_load(raw)
    receipts = (doc or {}).get("receipts") or {}
    q = receipts.get("quarantine")
    if q is None:
        continue
    checked += 1

    def bad(msg, _p=p):
        global findings
        findings += 1
        print(f"{_p}: {msg}")

    check_payload(q, doc, p, bad)

if findings:
    print(f"QUARANTINE_LINT_FAILED findings={findings} checked={checked}", file=sys.stderr)
    sys.exit(1)
print(f"QUARANTINE_LINT_OK checked={checked}")
PY
