/- GID: D5/S3/Quantum/Lieb/LownerHeinzTheorem
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/LownerHeinzTheorem
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hilbert-space predicates and the consumed pinned-Mathlib rpow concavity supplier. -/

/-
Attributed Physlib source transplant, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Source: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzTheorem.lean
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

public import D5.S3.Quantum.Lieb.LownerHeinzCore

public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.InnerProductSpace.StarOrder

@[expose] public section

/-!
## Wrapper（`B(ℋ)`）

このファイルは `LownerHeinzCore` の結果を、`L ℋ := ℋ →L[ℂ] ℋ`（有界線形作用素）に
**特殊化して再公開する薄い wrapper** です。

- 証明は `simpa using` による Core の特殊化のみ（重複証明は書かない）
- `B(ℋ)` 側では既存の Loewner order の ecosystem を尊重し、`spectralOrder` は導入しません
  （`spectralOrder` が必要な場合は `LownerHeinzCore.Spectral` を利用）
-/

namespace LownerHeinzTheorem

universe u v

open CFC

abbrev L (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  ℋ →L[ℂ] ℋ

variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

noncomputable instance instNontrivialL : Nontrivial (L ℋ) := inferInstance

set_option synthInstance.maxHeartbeats 40000 in
noncomputable local instance : NonnegSpectrumClass ℝ (L ℋ) := inferInstance

set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance instCFCRealSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint := inferInstance

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : L ℋ) : L ℋ :=
  LownerHeinzCore.cfcR (𝓐 := L ℋ) f A

/-- Fixed-space operator monotonicity on the Hilbert space `ℋ`. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorMonotone (𝓐 := L ℋ) f

/-- Fixed-space operator monotonicity on `s` for the Hilbert space `ℋ`. -/
def OperatorMonotoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorMonotoneOn (𝓐 := L ℋ) s f

/-- Fixed-space operator antitonicity on the Hilbert space `ℋ`. -/
def OperatorAntitone (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorAntitone (𝓐 := L ℋ) f

/-- Fixed-space operator antitonicity on `s` for the Hilbert space `ℋ`. -/
def OperatorAntitoneOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorAntitoneOn (𝓐 := L ℋ) s f

/-- Fixed-space operator convexity on the Hilbert space `ℋ`. -/
def OperatorConvex (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvex (𝓐 := L ℋ) f

/-- Fixed-space operator convexity on `s` for the Hilbert space `ℋ`. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConvexOn (𝓐 := L ℋ) s f

/-- Fixed-space operator concavity on the Hilbert space `ℋ`. -/
def OperatorConcave (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcave (𝓐 := L ℋ) f

/-- Fixed-space operator concavity on `s` for the Hilbert space `ℋ`. -/
def OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  LownerHeinzCore.OperatorConcaveOn (𝓐 := L ℋ) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator monotonicity over all Hilbert spaces in universe `u`. -/
def OperatorMonotoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorMonotone (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator monotonicity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorMonotoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorMonotoneOn (ℋ := K) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator antitonicity over all Hilbert spaces in universe `u`. -/
def OperatorAntitoneAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorAntitone (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator antitonicity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorAntitoneOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorAntitoneOn (ℋ := K) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator convexity over all Hilbert spaces in universe `u`. -/
def OperatorConvexAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConvex (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator convexity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorConvexOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConvexOn (ℋ := K) s f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator concavity over all Hilbert spaces in universe `u`. -/
def OperatorConcaveAll (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConcave (ℋ := K) f

omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/-- Uniform operator concavity on `s` over all Hilbert spaces in universe `u`. -/
def OperatorConcaveOnAll (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ {K : Type u}
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    [Nontrivial K],
    OperatorConcaveOn (ℋ := K) s f

/-- Consumed rpow concavity supplier; the pinned Mathlib proof replaces the
upstream integral proof rather than duplicating it. -/
theorem power_Icc_zero_one_operatorConcaveOn_Ici : ∀ p ∈ Set.Icc (0 : ℝ) 1,
    OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) (fun x ↦ x ^ p) := by
  intro p hp A B t hA hB ht0 ht1 hAs hBs
  have hA0 : (0 : L ℋ) ≤ A :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A (ha := hA)).2 hAs
  have hB0 : (0 : L ℋ) ≤ B :=
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) B (ha := hB)).2 hBs
  have hmix0 : (0 : L ℋ) ≤ (1 - t) • A + t • B :=
    add_nonneg (smul_nonneg (sub_nonneg.mpr ht1) hA0) (smul_nonneg ht0 hB0)
  have h := (CFC.concaveOn_rpow (A := L ℋ) hp).2 hA0 hB0
    (sub_nonneg.mpr ht1) ht0 (by ring)
  have hcfc (T : L ℋ) (hT : 0 ≤ T) :
      cfcR (fun x : ℝ ↦ -(x ^ p)) T = -(T ^ p) := by
    change cfc (fun x : ℝ ↦ -(x ^ p)) T = -(T ^ p)
    rw [cfc_neg, ← CFC.rpow_eq_cfc_real (a := T) (y := p) (ha := hT)]
  change cfcR (fun x : ℝ ↦ -(x ^ p)) ((1 - t) • A + t • B) ≤
    (1 - t) • cfcR (fun x : ℝ ↦ -(x ^ p)) A +
      t • cfcR (fun x : ℝ ↦ -(x ^ p)) B
  rw [hcfc _ hmix0, hcfc A hA0, hcfc B hB0]
  simpa only [smul_neg, neg_add] using neg_le_neg h

end LownerHeinzTheorem
