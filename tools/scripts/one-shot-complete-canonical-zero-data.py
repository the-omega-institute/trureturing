#!/usr/bin/env python3
from __future__ import annotations

import os
import pathlib
import re
import subprocess
import urllib.request

ROOT = pathlib.Path.cwd()
UPSTREAM = os.environ.get(
    "UPSTREAM_COMMIT", "2bafb8c88f177284a2123b5fefa2ff84e2365eb6"
)
RAW = f"https://raw.githubusercontent.com/anthropics/formal-math/{UPSTREAM}/zeta23"

MODULES = [
    (
        "Zeta23/GammaFacts/IntMu.lean",
        "D5/S3/Weil/ZetaGamma/GammaIntMu.lean",
        "D5/S3/Weil/ZetaGamma/GammaIntMu",
        "Port the proof-complete Gamma half-integral estimates.",
    ),
    (
        "Zeta23/GammaFacts/Complete.lean",
        "D5/S3/Weil/ZetaGamma/GammaFactsComplete.lean",
        "D5/S3/Weil/ZetaGamma/GammaFactsComplete",
        "Assemble the unconditional GammaFacts certificate.",
    ),
    (
        "Zeta23/FromPNTPlus/ZetaConj.lean",
        "D5/S3/Weil/ZetaPntBase/ZetaConj.lean",
        "D5/S3/Weil/ZetaPntBase/ZetaConj",
        "Port the zeta logarithmic-derivative conjugation identities.",
    ),
    (
        "Zeta23/RvM/Defs.lean",
        "D5/S3/Weil/ZetaRvm/Defs.lean",
        "D5/S3/Weil/ZetaRvm/Defs",
        "Port the shared Riemann-von Mangoldt contour vocabulary.",
    ),
    (
        "Zeta23/RvM/NcountWindow.lean",
        "D5/S3/Weil/ZetaRvm/NcountWindow.lean",
        "D5/S3/Weil/ZetaRvm/NcountWindow",
        "Port the zero-count window arithmetic.",
    ),
    (
        "Zeta23/RvM/GammaSide.lean",
        "D5/S3/Weil/ZetaRvm/GammaSide.lean",
        "D5/S3/Weil/ZetaRvm/GammaSide",
        "Identify the folded Gamma contour with the mu integral.",
    ),
    (
        "Zeta23/RvM/BacklundDefs.lean",
        "D5/S3/Weil/ZetaRvm/BacklundDefs.lean",
        "D5/S3/Weil/ZetaRvm/BacklundDefs",
        "Port the shared Backlund zero-set definition.",
    ),
    (
        "Zeta23/RvM/ReZeroCount.lean",
        "D5/S3/Weil/ZetaRvm/ReZeroCount.lean",
        "D5/S3/Weil/ZetaRvm/ReZeroCount",
        "Port the Jensen real-part zero-count bound.",
    ),
    (
        "Zeta23/RvM/Backlund.lean",
        "D5/S3/Weil/ZetaRvm/Backlund.lean",
        "D5/S3/Weil/ZetaRvm/Backlund",
        "Port the horizontal Backlund and vertical-line bounds.",
    ),
    (
        "Zeta23/RvM/Fold.lean",
        "D5/S3/Weil/ZetaRvm/Fold.lean",
        "D5/S3/Weil/ZetaRvm/Fold",
        "Fold the completed-zeta argument-principle contour.",
    ),
    (
        "Zeta23/RvM/MainTerm.lean",
        "D5/S3/Weil/ZetaRvm/MainTerm.lean",
        "D5/S3/Weil/ZetaRvm/MainTerm",
        "Prove the Riemann-von Mangoldt dyadic main term.",
    ),
    (
        "Zeta23/RvM/Statement.lean",
        "D5/S3/Weil/ZetaRvm/Statement.lean",
        "D5/S3/Weil/ZetaRvm/Statement",
        "Assemble RiemannVonMangoldt for the canonical zeta-zero configuration.",
    ),
]

IMPORTS = {
    "Zeta23.GammaFacts.Mu": "D5.S3.Weil.ZetaGamma.GammaMu",
    "Zeta23.GammaFacts.IntMu": "D5.S3.Weil.ZetaGamma.GammaIntMu",
    "Zeta23.GammaFacts.StirlingVert": "D5.S3.Weil.ZetaGamma.GammaStirlingVert",
    "Zeta23.GammaFacts": "D5.S3.Weil.ZetaGamma.GammaFacts",
    "Zeta23.Hypotheses": "D5.S3.Weil.ZetaCore.Hypotheses",
    "Zeta23.Statement.SeamClosed": "D5.S3.Weil.ZetaSeam.StatementSeamClosed",
    "Zeta23.Statement": "D5.S3.Weil.ZetaCore.Statement",
    "Zeta23.ZetaReflect": "D5.S3.Weil.ZetaSeam.ZetaReflect",
    "Zeta23.Prelude.InstancePriorities": "D5.S3.Weil.ZetaCore.InstancePriorities",
    "Zeta23.FromPNTPlus.StrongPNTPrefix": "D5.S3.Weil.ZetaPntBase.StrongPNTPrefix",
    "Zeta23.FromPNTPlus.ZetaConj": "D5.S3.Weil.ZetaPntBase.ZetaConj",
    "Zeta23.WeilEF.XiLogDeriv": "D5.S3.Weil.ZetaExplicit.XiLogDeriv",
    "Zeta23.Analytic.RectangleLogDeriv": "D5.S3.Weil.ZetaAnalytic.RectangleLogDeriv",
    "Zeta23.RvM.Defs": "D5.S3.Weil.ZetaRvm.Defs",
    "Zeta23.RvM.NcountWindow": "D5.S3.Weil.ZetaRvm.NcountWindow",
    "Zeta23.RvM.GammaSide": "D5.S3.Weil.ZetaRvm.GammaSide",
    "Zeta23.RvM.BacklundDefs": "D5.S3.Weil.ZetaRvm.BacklundDefs",
    "Zeta23.RvM.ReZeroCount": "D5.S3.Weil.ZetaRvm.ReZeroCount",
    "Zeta23.RvM.Backlund": "D5.S3.Weil.ZetaRvm.Backlund",
    "Zeta23.RvM.Fold": "D5.S3.Weil.ZetaRvm.Fold",
    "Zeta23.RvM.MainTerm": "D5.S3.Weil.ZetaRvm.MainTerm",
    "Zeta23.RvM.CountByIntegral": "D5.S3.Weil.ZetaRvm.CountByIntegral",
    "Zeta23.RvM.LocalCount": "D5.S3.Weil.ZetaRvm.LocalCount",
    "Zeta23.RvM.ZetaGrowth": "D5.S3.Weil.ZetaRvm.ZetaGrowth",
}


def fetch_text(path: str) -> str:
    request = urllib.request.Request(
        f"{RAW}/{path}", headers={"User-Agent": "trureturing-upstream-port"}
    )
    with urllib.request.urlopen(request) as response:
        return response.read().decode("utf-8")


def rewrite_imports(text: str) -> str:
    for old, new in sorted(IMPORTS.items(), key=lambda item: -len(item[0])):
        text = re.sub(rf"(?m)^import {re.escape(old)}$", f"import {new}", text)
    return text


def write_upstream_modules() -> None:
    for source, destination, gid, digest in MODULES:
        text = rewrite_imports(fetch_text(source))
        header = f"""/- GID: {gid}
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:upstream-proof-complete-port)
   anchors: []
   digest: {digest} -/

/- Ported from anthropics/formal-math commit {UPSTREAM}.
   Modified by trureturing on 2026-09-04: repository routing and canonical ZeroData assembly. -/
"""
        output = ROOT / destination
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(header + text, encoding="utf-8")


def write_unconditional_zero_data() -> None:
    output = ROOT / "D5/S3/Weil/ZetaBridge/UnconditionalCanonicalZeroData.lean"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        r'''/- GID: D5/S3/Weil/ZetaBridge/UnconditionalCanonicalZeroData
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/UnconditionalCanonicalZeroData
   mirror-E: none(waiver:canonical-zeta-zero-presentation)
   anchors: []
   digest: Assemble unconditional Gamma and Riemann-von Mangoldt sources into a parameter-free exhaustive ZeroData value. -/

import D5.S3.Weil.ZetaGamma.GammaFactsComplete
import D5.S3.Weil.ZetaRvm.Statement
import D5.S3.Weil.ZetaBridge.CanonicalZeroDataNonvacuityAssembly

/-!
# Unconditional canonical zeta `ZeroData`

This node removes the final analytic-source parameter from the canonical
`ZeroData` lane. It composes the proof-complete Gamma certificate with the
Riemann--von Mangoldt assembly, then instantiates the existing nonvacuity,
enumeration, multiplicity, symmetry, local-finiteness, and semantic-realization
chain.

The natural-number ordering is selected classically. The represented zero
set, analytic multiplicities, symmetric finite sums, and convergent zero sums
are independent of that presentation by the existing enumeration-invariance
results.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData

open D5.S3.Weil.ZeroSum
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataFromRiemannVonMangoldt
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataProvider
open D5.S3.Weil.ZetaBridge.CanonicalZeroDataNonvacuityAssembly

/-- The proof-complete, hypothesis-free Riemann--von Mangoldt source for
Mathlib's Riemann zeta function. -/
theorem zetaRiemannVonMangoldt :
    Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig :=
  Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts

/-- The source consumed by the canonical presentation layer, with no external
field or theorem parameter. -/
noncomputable def zetaCanonicalZeroDataSource : CanonicalZeroDataSource where
  riemannVonMangoldt := zetaRiemannVonMangoldt

/-- A fixed, exhaustive, duplicate-free, multiplicity-aware presentation of
all nontrivial zeta zeros. Only its presentation order depends on classical
choice. -/
noncomputable def zetaZeroData : ZeroData :=
  canonicalZeroData zetaCanonicalZeroDataSource

/-- `ZeroData` is unconditionally inhabited. -/
theorem nonempty_zeroData : Nonempty ZeroData :=
  ⟨zetaZeroData⟩

/-- Every canonical entry is a genuine nontrivial zeta zero. -/
theorem zetaZeroData_isNontrivial (n : ℕ) :
    IsNontrivialZero (zetaZeroData.zero n) :=
  canonicalZeroData_isNontrivial zetaCanonicalZeroDataSource n

/-- Every genuine nontrivial zeta zero occurs at exactly one canonical index. -/
theorem zetaZeroData_exhaustiveUnique {rho : ℂ}
    (hrho : IsNontrivialZero rho) :
    ∃! n : ℕ, zetaZeroData.zero n = rho :=
  canonicalZeroData_exhaustiveUnique zetaCanonicalZeroDataSource hrho

/-- The stored multiplicities are the positive analytic zero orders. -/
theorem zetaZeroData_multiplicity_pos (n : ℕ) :
    0 < zetaZeroData.multiplicity n :=
  canonicalZeroData_multiplicity_pos zetaCanonicalZeroDataSource n

/-- Functional-equation reflection is realized as an index permutation. -/
theorem zetaZeroData_reflection (n : ℕ) :
    zetaZeroData.zero (zetaZeroData.reflection n) = 1 - zetaZeroData.zero n :=
  canonicalZeroData_reflection zetaCanonicalZeroDataSource n

/-- Reflection preserves analytic multiplicity. -/
theorem zetaZeroData_multiplicity_reflection (n : ℕ) :
    zetaZeroData.multiplicity (zetaZeroData.reflection n) =
      zetaZeroData.multiplicity n :=
  canonicalZeroData_multiplicity_reflection zetaCanonicalZeroDataSource n

/-- Complex conjugation is realized as an index permutation. -/
theorem zetaZeroData_conjugation (n : ℕ) :
    zetaZeroData.zero (zetaZeroData.conjugation n) = conj (zetaZeroData.zero n) :=
  canonicalZeroData_conjugation zetaCanonicalZeroDataSource n

/-- Conjugation preserves analytic multiplicity. -/
theorem zetaZeroData_multiplicity_conjugation (n : ℕ) :
    zetaZeroData.multiplicity (zetaZeroData.conjugation n) =
      zetaZeroData.multiplicity n :=
  canonicalZeroData_multiplicity_conjugation zetaCanonicalZeroDataSource n

/-- Every symmetric spectral-radius cutoff is finite. -/
theorem zetaZeroData_locallyFinite (T : ℝ) :
    {n : ℕ | spectralRadius (zetaZeroData.zero n) ≤ T}.Finite :=
  canonicalZeroData_locallyFinite zetaCanonicalZeroDataSource T

/-- The unconditional consumer-facing fidelity certificate. -/
noncomputable def zetaZeroDataCertificate : CanonicalZeroDataCertificate :=
  certificate zetaCanonicalZeroDataSource

/-- Exact soundness, completeness, and uniqueness of the canonical
presentation. -/
theorem zetaZeroData_representation_iff (rho : ℂ) :
    IsNontrivialZero rho ↔ ∃! n : ℕ, zetaZeroData.zero n = rho := by
  simpa [zetaZeroData, zetaZeroDataCertificate] using
    certificate_representation_iff zetaZeroDataCertificate rho

/-- A property holds on the canonical sequence exactly when it holds on every
actual nontrivial zeta zero. -/
theorem zetaZeroData_universal_iff_actual (P : ℂ → Prop) :
    (∀ n : ℕ, P (zetaZeroData.zero n)) ↔
      ∀ rho : ℂ, IsNontrivialZero rho → P rho := by
  constructor
  · intro h rho hrho
    obtain ⟨n, hn, _⟩ := zetaZeroData_exhaustiveUnique hrho
    rw [← hn]
    exact h n
  · intro h n
    exact h (zetaZeroData.zero n) (zetaZeroData_isNontrivial n)

/-- A universal canonical-sequence theorem is witnessed by at least one actual
nontrivial zeta zero. -/
theorem zetaZeroData_exists_of_forall
    (P : ℂ → Prop) (h : ∀ n : ℕ, P (zetaZeroData.zero n)) :
    ∃ rho : ℂ, IsNontrivialZero rho ∧ P rho :=
  ⟨zetaZeroData.zero 0, zetaZeroData_isNontrivial 0, h 0⟩

/-- Any theorem universally quantified over `ZeroData` is unconditionally
realized on the fixed zeta presentation. -/
theorem universal_claim_realized_on_zetaZeroData
    {P : ZeroData → Prop} (h : ∀ Z : ZeroData, P Z) :
    P zetaZeroData ∧ ∃ rho : ℂ, IsNontrivialZero rho :=
  ⟨h zetaZeroData,
    ⟨zetaZeroData.zero 0, zetaZeroData_isNontrivial 0⟩⟩

/-- The entire nonvacuity and fidelity chain, without an analytic input
parameter. -/
theorem zetaZeroData_closed_chain :
    {rho : ℂ | IsNontrivialZero rho}.Infinite ∧
      Nonempty ZeroData ∧
      ∃ C : CanonicalZeroDataCertificate, C.data = zetaZeroData := by
  refine ⟨nontrivial_zeta_zero_set_infinite_of_riemannVonMangoldt
      zetaRiemannVonMangoldt, nonempty_zeroData, ?_⟩
  exact ⟨zetaZeroDataCertificate, rfl⟩

#print axioms zetaRiemannVonMangoldt
#print axioms nonempty_zeroData
#print axioms zetaZeroData_isNontrivial
#print axioms zetaZeroData_exhaustiveUnique
#print axioms zetaZeroData_representation_iff
#print axioms zetaZeroData_universal_iff_actual
#print axioms zetaZeroData_closed_chain

end D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData
''',
        encoding="utf-8",
    )


BLUEPRINT_NODES = [
    (
        "D5/S3/Weil/ZetaGamma/GammaIntMu",
        "Gamma Integral Estimates",
        "Zeta23.MuInts.int_mu_of_stirling",
        "The Stirling estimate yields the first and second dyadic mu-integral asymptotics.",
    ),
    (
        "D5/S3/Weil/ZetaGamma/GammaFactsComplete",
        "Complete GammaFacts Assembly",
        "Zeta23.gammaFacts",
        "All Gamma-side fields are assembled without hypotheses.",
    ),
    (
        "D5/S3/Weil/ZetaPntBase/ZetaConj",
        "Zeta Conjugation Identities",
        "logDerivZeta_conj'",
        "Complex conjugation commutes with the zeta logarithmic derivative.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/Defs",
        "Riemann-von Mangoldt Definitions",
        "Zeta23.RvM.halfContour_add",
        "The right-half contour and its additive law are fixed.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/NcountWindow",
        "Zero-Count Window Arithmetic",
        "Zeta23.Ncount_add",
        "Multiplicity-weighted zero counts are additive across adjacent windows.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/GammaSide",
        "Riemann-von Mangoldt Gamma Side",
        "Zeta23.RvM.gamma_side",
        "The folded Gamma logarithmic derivative equals the mu integral.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/BacklundDefs",
        "Backlund Definitions",
        "Zeta23.RvM.mem_reZeroSet",
        "The real-part zero set used in Backlund's bound is fixed.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/ReZeroCount",
        "Jensen Real-Zero Count",
        "Zeta23.RvM.reZeroSet_card_le",
        "Jensen theory bounds the real-part crossing count by a logarithmic term.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/Backlund",
        "Backlund Horizontal Bound",
        "Zeta23.RvM.backlund_horizontal",
        "The horizontal argument variation and vertical line are logarithmically controlled.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/Fold",
        "Completed-Zeta Contour Fold",
        "Zeta23.RvM.Ncount_eq_im_halfContour",
        "Functional-equation symmetry folds the full argument-principle contour.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/MainTerm",
        "Riemann-von Mangoldt Main Term",
        "Zeta23.RvM.rvM_main",
        "The dyadic multiplicity count has its classical main term and logarithmic error.",
    ),
    (
        "D5/S3/Weil/ZetaRvm/Statement",
        "Riemann-von Mangoldt Statement",
        "Zeta23.RvM.riemannVonMangoldt",
        "The main term and local count assemble the canonical Riemann-von Mangoldt certificate.",
    ),
    (
        "D5/S3/Weil/ZetaBridge/UnconditionalCanonicalZeroData",
        "Unconditional Canonical Zeta ZeroData",
        "D5.S3.Weil.ZetaBridge.UnconditionalCanonicalZeroData.zetaZeroData_closed_chain",
        "The unconditional Gamma and Riemann-von Mangoldt sources produce a fixed exhaustive zeta ZeroData presentation.",
    ),
]


def write_blueprints() -> None:
    for gid, title, declaration, summary in BLUEPRINT_NODES:
        parts = gid.split("/")
        stem = parts[-1]
        namespace = ".".join(["StrataLint", "Scribe", "Blueprint", *parts[:-1]])
        slug = re.sub(r"[^a-z0-9]+", "-", stem.lower()).strip("-")
        markdown = ROOT / "Blueprint" / pathlib.Path(*parts)
        markdown = markdown.with_suffix(".md")
        markdown.parent.mkdir(parents=True, exist_ok=True)
        markdown.write_text(
            f"# {title}\n\n"
            f"**Declaration:** `{declaration}`\n\n"
            f"{summary}\n\n"
            "This node belongs to the proof-complete upstream Riemann-von Mangoldt "
            "closure used to construct the parameter-free `zetaZeroData`. "
            "Lean remains the truth source.\n",
            encoding="utf-8",
        )
        scribe = markdown.with_suffix(".scribe.cs")
        class_name = re.sub(r"[^A-Za-z0-9]", "", stem) + "Document"
        scribe.write_text(
            f'''using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace {namespace};

internal sealed class {class_name} : IScribeDocumentDefinition
{{
    private const string Declaration = "{declaration}";

    public DocumentDefinition Create()
    {{
        return DocumentDefinition.Create(ScribeNode.Create(
            "{summary}",
            H("{title}"),
            Blocks(Describe.Lean(
                DescribeId.Create("{slug}"),
                DeclarationHandle.Create(Declaration),
                H("{title}"),
                StatementSource.FromAuthor(Disp(F.Id("{stem}"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("{summary}"))),
                DescribeRole.Theorem))));
    }}
}}
''',
            encoding="utf-8",
        )


CLOSURE_SECTION = r'''
---

## [PR #5065] UNCONDITIONAL_CANONICAL_ZERO_DATA_CLOSURE

# 无参数 `zetaZeroData` 与解析来源闭合

本增补恢复本 PR 误删的历史理论段，并把此前显式接收 `RiemannVonMangoldt zetaZeroConfig` 的条件链升级为无参数机器构造。

新增 proof-complete 路径为：

\[
\boxed{
\begin{aligned}
\texttt{GammaStirlingVert.mu\_stirling}
&\Longrightarrow \texttt{GammaFacts},\\
\texttt{GammaFacts}
&\Longrightarrow \texttt{RiemannVonMangoldt(zetaZeroConfig)},\\
\texttt{RiemannVonMangoldt}
&\Longrightarrow N(T,2T)\to\infty,\\
&\Longrightarrow \mathcal Z_\zeta\text{ infinite},\\
&\Longrightarrow \operatorname{Nonempty}(\texttt{ZeroData}),\\
&\Longrightarrow \texttt{zetaZeroData : ZeroData}.
\end{aligned}
}
\]

机器 owner 为：

```text
D5/S3/Weil/ZetaGamma/GammaIntMu.lean
D5/S3/Weil/ZetaGamma/GammaFactsComplete.lean
D5/S3/Weil/ZetaPntBase/ZetaConj.lean
D5/S3/Weil/ZetaRvm/Defs.lean
D5/S3/Weil/ZetaRvm/NcountWindow.lean
D5/S3/Weil/ZetaRvm/GammaSide.lean
D5/S3/Weil/ZetaRvm/BacklundDefs.lean
D5/S3/Weil/ZetaRvm/ReZeroCount.lean
D5/S3/Weil/ZetaRvm/Backlund.lean
D5/S3/Weil/ZetaRvm/Fold.lean
D5/S3/Weil/ZetaRvm/MainTerm.lean
D5/S3/Weil/ZetaRvm/Statement.lean
D5/S3/Weil/ZetaBridge/UnconditionalCanonicalZeroData.lean
```

`zetaZeroData` 是一个固定的自然数索引 presentation。其顺序由 `Classical.choice` 选出。canonical 内容位于它穷尽表示的真实非平凡零点集合、解析重数、反射与共轭作用，以及已经证明为枚举不变的零点观察量。

无参数接口闭合以下事实：

1. `ZeroData` 确实有 inhabitant；
2. 每个 `zetaZeroData.zero n` 都是真实非平凡 zeta 零点；
3. 每个真实非平凡零点恰有一个索引；
4. 存储重数是严格正的解析零点阶；
5. 函数方程反射与复共轭由索引置换忠实实现，并保持重数；
6. 每个对称谱半径截断有限；
7. 枚举上的全称命题与真实非平凡零点上的全称命题等价；
8. 围绕 `ZeroData` 的任意全称结构定理都可以直接实例化到 `zetaZeroData`。

本增补没有为自然数编号赋予高度排序、可计算性或内在意义，也没有使用 RH。它关闭的是实际零点对象进入既有 `ZeroData` consumer DAG 的语义入口。
'''.strip()


def rewrite_theory() -> None:
    theory_path = ROOT / "docs/develop/theory/RH_RESEARCH_LANE_THEORY.md"
    current = theory_path.read_text(encoding="utf-8")
    marker = "\n---\n\n## [PR #5065] CANONICAL_ZERO_DATA_NONVACUITY"
    position = current.find(marker)
    existing_append = current[position:].strip() if position >= 0 else ""
    dev_theory = subprocess.check_output(
        ["git", "show", f"origin/dev:{theory_path.relative_to(ROOT).as_posix()}"],
        text=True,
    )
    pieces = [dev_theory.rstrip()]
    if existing_append and "## [PR #5065] CANONICAL_ZERO_DATA_NONVACUITY" not in dev_theory:
        pieces.append(existing_append)
    if "## [PR #5065] UNCONDITIONAL_CANONICAL_ZERO_DATA_CLOSURE" not in "\n\n".join(pieces):
        pieces.append(CLOSURE_SECTION)
    theory_path.write_text("\n\n".join(pieces).rstrip() + "\n", encoding="utf-8")


def main() -> None:
    write_upstream_modules()
    write_unconditional_zero_data()
    write_blueprints()
    rewrite_theory()


if __name__ == "__main__":
    main()
