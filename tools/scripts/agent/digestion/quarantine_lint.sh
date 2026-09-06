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
#
# usage: quarantine_lint.sh REPO [FILE...]      # 不给 FILE 则扫 REPO 里全部带 quarantine 的条目
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

files = sys.argv[1:]
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
    def bad(msg):
        global findings
        findings += 1
        print(f"{p}: {msg}")
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
                f"canonically (YAML inline comment) at {idx}: ...{value[max(0, idx - 30):idx + 24]}...")
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
    if "cover_disposition" in receipts:
        bad("cover_disposition cannot coexist with quarantine (BackfillInventoryLoader)")
    if "/residual-open/" not in p:
        bad("quarantine entry is not under residual-open")

if findings:
    print(f"QUARANTINE_LINT_FAILED findings={findings} checked={checked}", file=sys.stderr)
    sys.exit(1)
print(f"QUARANTINE_LINT_OK checked={checked}")
PY
