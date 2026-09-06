#!/bin/bash
# 器律⑨: 冻结面的**悬空引用**自检 —— accepted 事件与冻结状态片必须互相指得到。
#
# 立器案由(2026-09-07):
#   dev 上 `make deposit` 的 `ledger-align --add` 在**纯 dev、零改动的干净树**上失败,
#   判词为 `LEDGER_ALIGN_FAILED AUTHORIZATION ... prerequisite repair requires unchanged
#   statement/declaration identities and matching frozen state: <某模块>.lean`,
#   而全仓三门 CI **仍报 success**(实测 dev 的 7e2a03498 / c4ad17618 皆绿)。
#   根因是一类账目不一致:某些 accepted `Freeze` 事件的 `descriptor_selector` 指向一个
#   **从未存在过**的状态片(`git log --all -- <状态片路径>` 零记录)。立单 #5962。
#
#   **为什么现役门抓不到**:`RepositoryRules.FrozenState` 从**状态片**一侧出发扫描,
#   其读 accepted 的那段自带注释「only **changed** candidate accepted files are read here」
#   —— **delta-only**。一条两天前引入、此后再未改动的悬空事件,永远不会被重新检查。
#   这正是第Ⅵ节「引用必须机械可判,悬空即红」所指的缺口:**只验语法不验指向**。
#
# 检查两个方向(任一命中即非零退出):
#   A. accepted → state:凡 `payload.descriptor_selector` 以 `.lean` 结尾者,
#      `Golden/Frozen/state/<selector>.json` 必须存在。
#   B. state → module:凡 `Golden/Frozen/state/**.lean.json`,其对应的 `.lean` 必须存在。
#
# **本器不是门**(CI 看不到 agent 侧自审器),是写前/巡检自检;不跑即等于不存在。
#
# --selftest: 6 条夹具,预期红数写在跑之前(六元组第六项)——
#   F1 accepted 有状态片=0 / F2 accepted 无状态片=1 / F3 无 descriptor_selector=0
#   F4 状态片无 .lean=1 / F5 状态片有 .lean=0 / F6 accepted 是坏 JSON=1(fail-closed)
#   预期红合计 3。
#
# usage: dangling_freeze_lint.sh REPO            # 扫全库
#        dangling_freeze_lint.sh REPO --selftest # 跑夹具
# 哨兵: DANGLING_FREEZE_LINT_OK checked=<n>  /  ..._FAILED findings=<n>
set -euo pipefail
REPO="${1:-}"
[ -n "$REPO" ] || { echo "DANGLING_FREEZE_LINT_USAGE: dangling_freeze_lint.sh REPO [--selftest]" >&2; exit 64; }
[ -d "$REPO/.git" ] || [ -f "$REPO/.git" ] || { echo "DANGLING_FREEZE_LINT_BAD_REPO=$REPO" >&2; exit 65; }
[ -d "$REPO/Golden/Frozen" ] || { echo "DANGLING_FREEZE_LINT_NO_FROZEN=$REPO" >&2; exit 66; }
shift || true
cd "$REPO"
python3 -X utf8 - "$@" <<'PY'
import sys, os, json, glob, tempfile

ACCEPTED = "Golden/Frozen/accepted"
STATE = "Golden/Frozen/state"


def scan(root):
    """返回 (findings, checked)。root 为仓根,便于自测用临时目录。"""
    findings = []
    acc = sorted(glob.glob(os.path.join(root, ACCEPTED, "*.json")))
    for path in acc:
        try:
            with open(path, encoding="utf-8") as handle:
                event = json.load(handle)
        except Exception as error:            # fail-closed:读不动就是红
            findings.append(f"A unreadable accepted event {os.path.basename(path)}: {error}")
            continue
        selector = (event.get("payload") or {}).get("descriptor_selector")
        if not isinstance(selector, str) or not selector.endswith(".lean"):
            continue                          # 非模块事件,不在本器射程
        if not os.path.exists(os.path.join(root, STATE, selector + ".json")):
            findings.append(
                f"A dangling accepted Freeze: {os.path.basename(path)[:16]}… "
                f"descriptor_selector={selector} 无对应状态片")
    states = sorted(glob.glob(os.path.join(root, STATE, "**", "*.lean.json"), recursive=True))
    prefix = os.path.join(root, STATE) + os.sep
    for path in states:
        module = path[len(prefix):-len(".json")]
        if not os.path.exists(os.path.join(root, module)):
            findings.append(f"B dangling state slice: {module}.json 指向不存在的 {module}")
    return findings, len(acc) + len(states)


def write(path, text):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as handle:
        handle.write(text)


def selftest():
    cases = [
        ("F1 accepted 有状态片", 0),
        ("F2 accepted 无状态片", 1),
        ("F3 accepted 无 descriptor_selector", 0),
        ("F4 状态片无 .lean", 1),
        ("F5 状态片有 .lean", 0),
        ("F6 accepted 是坏 JSON", 1),
    ]
    bad = 0
    for name, expected in cases:
        with tempfile.TemporaryDirectory() as root:
            if name.startswith("F1"):
                write(f"{root}/{ACCEPTED}/e1.json",
                      json.dumps({"payload": {"descriptor_selector": "D5/A/B.lean"}}))
                write(f"{root}/{STATE}/D5/A/B.lean.json", '{"statement_id":"sha256:x"}')
                write(f"{root}/D5/A/B.lean", "-- ok\n")
            elif name.startswith("F2"):
                write(f"{root}/{ACCEPTED}/e2.json",
                      json.dumps({"payload": {"descriptor_selector": "D5/A/B.lean"}}))
            elif name.startswith("F3"):
                write(f"{root}/{ACCEPTED}/e3.json", json.dumps({"payload": {"note": "no selector"}}))
            elif name.startswith("F4"):
                write(f"{root}/{STATE}/D5/A/Gone.lean.json", '{"statement_id":"sha256:x"}')
            elif name.startswith("F5"):
                write(f"{root}/{STATE}/D5/A/Here.lean.json", '{"statement_id":"sha256:x"}')
                write(f"{root}/D5/A/Here.lean", "-- ok\n")
            else:
                write(f"{root}/{ACCEPTED}/e6.json", "{ this is not json")
            os.makedirs(f"{root}/{ACCEPTED}", exist_ok=True)
            os.makedirs(f"{root}/{STATE}", exist_ok=True)
            got, _ = scan(root)
            mark = "ok " if len(got) == expected else "RED"
            if len(got) != expected:
                bad += 1
            print(f"  [{mark}] {name}: expected={expected} got={len(got)}"
                  + ("" if len(got) == expected else " :: " + " | ".join(got)))
    if bad:
        print(f"DANGLING_FREEZE_LINT_SELFTEST_FAILED mismatched={bad}", file=sys.stderr)
        return 1
    print(f"DANGLING_FREEZE_LINT_SELFTEST_OK cases={len(cases)}")
    return 0


args = sys.argv[1:]
if args and args[0] == "--selftest":
    sys.exit(selftest())

findings, checked = scan(".")
for line in findings:
    print("  " + line)
if findings:
    print(f"DANGLING_FREEZE_LINT_FAILED findings={len(findings)} checked={checked}", file=sys.stderr)
    sys.exit(1)
print(f"DANGLING_FREEZE_LINT_OK checked={checked}")
PY
