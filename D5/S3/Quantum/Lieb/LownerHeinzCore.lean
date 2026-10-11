/- GID: D5/S3/Quantum/Lieb/LownerHeinzCore
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/LownerHeinzCore
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Functional-calculus operator convexity and concavity predicates for the consumed Lieb proof. -/

/-
Attributed Physlib source transplant, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Source: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean
Copyright and Apache-2.0 header follow; full license retained at
`docs/reports/inoutbalance/physlib-LICENSE.txt`; supplier root has no NOTICE.
Retire this transplant when the repository-pinned Mathlib provides an equivalent
consumed declaration, replacing this proof with its direct application.
This is upstream reuse; no mathematical originality is claimed.
-/

/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/

module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

/-!
## 構造（Core / Wrapper）

このファイルは Löwner–Heinz まわりの議論を、**一般の C★代数 `𝓐`** 上で再利用できるように
Core として切り出したものです。

- `section Pure`：`cfcR` と `OperatorMonotone(On)` / `OperatorConvexOn` などの **定義**（軽い層）
- `section Spectrum`：`NonnegSpectrumClass` などを仮定して、主要定理群を置く **重い層**
- `namespace LownerHeinzCore.Spectral`：`spectralOrder` を **`local instance`** として閉じ込めた wrapper

`spectralOrder` を Core 本体に混ぜず、wrapper 側で局所化することで、他モジュールへの順序変更が
漏れないようにしています。また `NonnegSpectrumClass` は必要な層で明示し、場当たりの `infer_instance`
散布を避けています。
-/

namespace LownerHeinzCore

universe u v

open CFC

section Pure

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : 𝓐) : 𝓐 :=
  cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A

/-- Fixed-space operator monotonicity on the ambient algebra `𝓐`. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A → cfcR f B ≤ cfcR f A

/-- Fixed-space operator monotonicity on `s` for the ambient algebra `𝓐`. -/
def OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄,
    0 ≤ A → 0 ≤ B → B ≤ A →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f B ≤ cfcR f A

/-- Fixed-space operator antitonicity on the ambient algebra `𝓐`. -/
def OperatorAntitone (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄, 0 ≤ A → 0 ≤ B → B ≤ A →
    cfcR f A ≤ cfcR f B

/-- Fixed-space operator antitonicity on `s` for the ambient algebra `𝓐`. -/
def OperatorAntitoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄,
    0 ≤ A → 0 ≤ B → B ≤ A →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f A ≤ cfcR f B

/-- Fixed-space operator convexity on the ambient algebra `𝓐`. -/
def OperatorConvex (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄ ⦃t : ℝ⦄, 0 ≤ t → t ≤ 1 →
    cfcR f ((1 - t) • A + t • B)
      ≤ (1 - t) • cfcR f A + t • cfcR f B

/-- Fixed-space operator convexity on `s` for the ambient algebra `𝓐`. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄ ⦃t : ℝ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    0 ≤ t → t ≤ 1 →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f ((1 - t) • A + t • B)
      ≤ (1 - t) • cfcR f A + t • cfcR f B

/-- Fixed-space operator concavity on the ambient algebra `𝓐`. -/
def OperatorConcave (f : ℝ → ℝ) : Prop :=
  OperatorConvex (𝓐 := 𝓐) (fun x => - f x)

/-- Fixed-space operator concavity on `s` for the ambient algebra `𝓐`. -/
def OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorConvexOn (𝓐 := 𝓐) (s : Set ℝ) (fun x => - f x)

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator monotonicity over all ambient algebras in universe `u`. -/
def OperatorMonotoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorMonotone (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator monotonicity on `s` over all ambient algebras in universe `u`. -/
def OperatorMonotoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorMonotoneOn (𝓐 := 𝓑) s f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator antitonicity over all ambient algebras in universe `u`. -/
def OperatorAntitoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorAntitone (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator antitonicity on `s` over all ambient algebras in universe `u`. -/
def OperatorAntitoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorAntitoneOn (𝓐 := 𝓑) s f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator convexity over all ambient algebras in universe `u`. -/
def OperatorConvexAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorConvex (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator convexity on `s` over all ambient algebras in universe `u`. -/
def OperatorConvexOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorConvexOn (𝓐 := 𝓑) s f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator concavity over all ambient algebras in universe `u`. -/
def OperatorConcaveAll (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorConcave (𝓐 := 𝓑) f

omit 𝓐 [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] [Nontrivial 𝓐] in
/-- Uniform operator concavity on `s` over all ambient algebras in universe `u`. -/
def OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {𝓑 : Type u} [CStarAlgebra 𝓑] [PartialOrder 𝓑] [StarOrderedRing 𝓑]
    [ContinuousFunctionalCalculus ℝ 𝓑 IsSelfAdjoint] [Nontrivial 𝓑],
    OperatorConcaveOn (𝓐 := 𝓑) s f

end Pure

end LownerHeinzCore
