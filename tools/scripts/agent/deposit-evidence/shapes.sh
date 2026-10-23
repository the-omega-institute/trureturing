#!/usr/bin/env bash
# op-body-shapes.sh WORKTREE MODULE_DOTTED — per-public-declaration evidence table for a deposit PR body.
#
# Machine columns describe elaborated dependencies and axioms; proof shape requires review.
set -uo pipefail
W="${1:?worktree}"; MOD="${2:?module dotted}"
SP="$(cd "$(dirname "$0")" && pwd)"
# Intermediates go to a scratch dir. This tool lives in the repository now, so writing beside itself
# would dirty the working tree; WORK can be overridden by the caller.
WORK="${WORK:-${TMPDIR:-/tmp}/deposit-evidence}"; mkdir -p "$WORK"
OUT="$WORK/edges-$(echo "$MOD" | tr '.' '_').json"
bash "$SP/proof-edges.sh" "$W" "$MOD" "$OUT" >&2 || { echo "(内核判形不可用:边提取失败,本表退化为仅事件字段)"; exit 0; }
python3 - "$W" "$OUT" "$SP" "$MOD" <<'PY'
import json, os, re, subprocess, sys

w, edges_path, tooldir, mod = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
eg = json.load(open(edges_path))
changed = subprocess.run(["git", "-C", w, "diff", "--name-only", "origin/dev...HEAD"],
                         capture_output=True, text=True).stdout.split()
selector = "/".join(mod.split(".")) + ".lean"
state_path = "Golden/Frozen/state/" + selector + ".json"
if state_path not in changed:
    sys.exit(f"shapes.sh: committed delta carries no state record for {selector}")
p = json.load(open(os.path.join(w, state_path)))
if set(p) != {"statement_id", "declarations"}:
    sys.exit("shapes.sh: invalid frozen state schema")
mod_comps = selector[:-5].split("/")

GEN = re.compile(r'\.(eq_def|eq_\d+|match_\d+(_\d+)*|proof_\d+(_\d+)*|sizeOf_spec|_sizeOf_inst|_sizeOf_\d+'
                 r'|_f|_sunfold|_unsafe_rec|_mutual|injEq|inj|noConfusion\w*|noConfusionType|rec|recOn'
                 r'|casesOn|mk\.\w+|below|brecOn|ibelow|binductionOn|ctorIdx|_flat_ctor)$|\._sizeOf')


def nm(key):
    c = re.findall(r'\d+:([^)]+)\)', key)
    return '.'.join(c[len(mod_comps):]) if c[:len(mod_comps)] == mod_comps else '.'.join(c)


src_path = os.path.join(w, selector)
src = open(src_path, encoding="utf-8").read() if os.path.exists(src_path) else ""
# Authored declaration parsing is shared with facts.py.
sys.path.insert(0, tooldir)
from facts import AUTHORED
authored = {m.group(2) for m in AUTHORED.finditer(src)}

edges = eg.get("edges", {})
axioms = eg.get("axioms", {})
numeric = eg.get("numeric_certificate", {})
ext = eg.get("external_deps", {})
undecided = []

def _pending_sentence(rows):
    from collections import Counter
    c = Counter(k or "?" for _, k in rows)
    parts = "、".join(f"{n} 条 {k}" for k, n in sorted(c.items()))
    return f"本表共 {len(rows)} 条公开声明({parts})待判词段处理。"

print("| 公开声明 | kind | 类型闭合 | 直接依赖含判定程序标记 | 模块内直接依赖(consumer → prerequisite) | 模块外依赖 | axioms |")
print("|---|---|---|---|---|---|---|")
for d in p.get("declarations", []):
    name = nm(d.get("declaration_name_key", ""))
    if name not in authored or GEN.search(name):
        continue
    kind = d.get("kind", "")
    inner = sorted(set(edges.get(name, [])))
    outer = sorted(set(ext.get(name, [])))
    ax = axioms.get(name, "?")
    if False:
        pass
    else:
        # No machine bind-only rule. CLAUDE.md 5-quadruple-prime makes a conclusion bind-only when it
        # follows by instantiation, projection or normalization of frozen results — not merely when no
        # module theorem sits on its live path. A multi-step analytic estimate assembled from several
        # Mathlib lemmas has no module theorem on its path and is still not an instantiation of one.
        # An earlier version of this table judged such a theorem bind-only; that was the same
        # fabrication a seat already rejected in the opposite direction, so the middle stays 未判.
        undecided.append((name, kind))
    # No truncation. These columns are the evidence a seat checks against the proof term; a review seat
    # caught an earlier version silently dropping three of eight direct dependencies behind `[:5]`.
    inner_s = ", ".join(f"`{e}`" for e in inner) or "无"
    outer_s = ", ".join(f"`{e}`" for e in outer) or "无"
    closed = "是" if numeric.get(name + "::closed", numeric.get(name)) is not None else "—"
    dec = "是" if numeric.get(name) else "否"
    print(f"| `{name}` | {kind} | {closed} | {dec} | {inner_s} | {outer_s} | {ax} |")

print()
print("**本表不给判形**。机器三次尝试分类都产出了伪造结论(经本模块定理即 content;活路径无本模块定理即 bind-only;"
      "类型闭合且出现判定程序即数值证书——第三条在一条两行推导上误触发)。故此表只报事实:"
      "kind、类型是否闭合、**直接**依赖里是否出现判定程序标记(`decide` / `norm_num` 一族)、"
      "内核直接依赖、模块外依赖、axioms。"
      "**注意该列只看直接依赖**:一条自身用 `decide` 但把它藏在私有引理里的定理,这一列会显示「否」;"
      "而一条只是引用了它的定理反而可能显示「是」。它是原始事实,不是「谁在做计算」的答案。"
      "**`proof_shape` 与 `escape_witness` 由提出方在正文的判词段逐条给出并说明理由,评审席可推翻**(5⁗)。"
      + (_pending_sentence(undecided) if undecided else ""))
print()
print("依赖两列由内核环境导出(`Expr.getUsedConstants` 于证明项与类型,展开辅助常量),不是文本扫描;"
      "`axioms` 列由 `Lean.collectAxioms` 得出。")

# The deposit body must carry the evidence checklist that skills/codex-formalize/SKILL.md:241-251 makes
# mandatory ("Any item without evidence blocks deposit"). Five deposit pull requests shipped without it
# and three review seats on two of them raised it independently, so the skeleton is emitted here rather
# than left to memory. Every line is deliberately blank: these are judgments, and a generator that
# pre-filled them would be manufacturing the evidence it is supposed to prompt for.
print()
print("---")
print()
print("## 首冻保真证据(SKILL.md:241-251;缺项即阻断 deposit)")
print()
print("| 项 | 证据 | 状态 |")
print("|---|---|---|")
print("| 假设可满足性 | `example : … := …`(须在钉版工具链下真 elaborate) | 待填 |")
print("| 论域可居 | `example : … := …` | 待填 |")
print("| 逐子句保真 | atom 子句 ↔ Lean binder/假设/结论 一一对照表 | 待填 |")
print("| 逐符号发射保真 | Blueprint `.md` 显示式 vs Lean 声明,逐符号 | 待填 |")
print()
print("**散文断言不算证据**:必须是能编译的项;产不出即 `open`,不 deposit。")
print()
print("### 七个 grader trap(逐条给结论或「不适用」)")
print()
for t in ("witness-vs-universal", "instance-vs-general", "conditional-vs-unconditional",
          "pointwise-vs-operator", "proof-internal-vs-addressable-statement",
          "multi-clause residue names", "mechanism-vs-outcome"):
    print(f"- **{t}**:待填")
print()
print("### 逐条 escape_witness")
print()
print("| 公开定理 | proof_shape | escape_witness(content 才有;bind-only 写 `—` 并记一条有向边) |")
print("|---|---|---|")
for name, kind in undecided:
    if kind == "theorem":
        print(f"| `{name}` |  |  |")
print()
print("**判形按 5⁗ 判:把私有引理内联后问反事实**。私有引理自身若只是 `rfl` / `simp [该定义]` / "
      "`norm_num`,它零贡献,消费者是 bind-only;若它经具名非平凡引理搬运或作归纳,才是 content。"
      "上表的依赖列是证据,**不是判据**——它说依赖了谁,不说那个依赖干了多少活。")
PY
