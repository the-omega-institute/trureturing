/- GID: D5/S3/Quantum/Lieb/OperatorGeometricMean
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/OperatorGeometricMean
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Joint concavity of the power perspective on strictly positive operator pairs. -/

/-
Attributed Physlib source transplant, revision b9043cc548ef6d63a28454cf3a57fb12a0c2e142.
Source: https://github.com/leanprover-community/physlib/blob/b9043cc548ef6d63a28454cf3a57fb12a0c2e142/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/OperatorGeometricMean.lean
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

public import D5.S3.Quantum.Lieb.GeneralizedPerspectiveFunction
public import D5.S3.Quantum.Lieb.PowerConvexity

@[expose] public section

namespace OperatorGeometricMean

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- The operator `(α, β)`-power mean, realized as a generalized perspective. -/
noncomputable def operatorPowerMean (α β : ℝ) (A B : L ℋ) : L ℋ :=
  GeneralizedPerspective (fun x : ℝ ↦ x ^ α) (fun x : ℝ ↦ x ^ β) A B

private lemma rpow_continuousOn_Ici (p : ℝ) (hp : 0 ≤ p) :
    ContinuousOn (fun x : ℝ ↦ x ^ p) (Set.Ici (0 : ℝ)) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x p (Or.inr hp)).continuousWithinAt

omit [Nontrivial ℋ] in
private lemma operatorConcaveOn_Ioi_of_Ici {f : ℝ → ℝ}
    (h : OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) f) :
    OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) f := by
  intro A B t hA hB ht0 ht1 hAs hBs
  exact h hA hB ht0 ht1 (Set.Subset.trans hAs Set.Ioi_subset_Ici_self)
      (Set.Subset.trans hBs Set.Ioi_subset_Ici_self)

omit [Nontrivial ℋ] in
private lemma pdSet_subset_psdSet : pdSet (ℋ := ℋ) ⊆ psdSet (ℋ := ℋ) := by
  intro A hA
  rcases hA with ⟨hA_sa, hA_spec⟩
  exact ⟨hA_sa, Set.Subset.trans hA_spec Set.Ioi_subset_Ici_self⟩

private lemma rpow_pos_on_Ioi (p : ℝ) :
    ∀ x ∈ Set.Ioi (0 : ℝ), 0 < x ^ p := by
  intro x hx
  exact Real.rpow_pos_of_pos hx p

/--
Theorem 1.1, concave range: the operator `(α, β)`-power mean is jointly concave on
strictly positive operators for `0 ≤ α, β ≤ 1`.
-/
theorem operatorPowerMean_jointlyConcaveOn_pdSet
    {α β : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (operatorPowerMean (ℋ := ℋ) α β) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hconc :=
    theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici
      (ℋ := ℋ)
      (f := fun x : ℝ ↦ x ^ α)
      (h := fun x : ℝ ↦ x ^ β)
      (hfconc := by
        intro K _ _ _ _
        exact power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := K) α hα)
      (hfcont := rpow_continuousOn_Ici α hα.1)
      (hf0 := by
        exact Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by simp) α)
      (hconc := by
        exact operatorConcaveOn_Ioi_of_Ici (ℋ := ℋ)
          (power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) β hβ))
      (hcont := by
        intro x hx
        exact (Real.continuousAt_rpow_const x β (Or.inl (ne_of_gt hx))).continuousWithinAt)
      (hpos := rpow_pos_on_Ioi β)
  simpa [operatorPowerMean] using
    hconc (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) (θ := θ)
      (pdSet_subset_psdSet (ℋ := ℋ) hA₁) (pdSet_subset_psdSet (ℋ := ℋ) hA₂)
      hB₁ hB₂ hθ0 hθ1


/--
Theorem 1.1, convex range: the operator `(α, β)`-power mean is jointly convex on
strictly positive operators for `1 ≤ α ≤ 2` and `0 ≤ β ≤ 1`.
-/
theorem operatorPowerMean_jointlyConvexOn_pdSet
    {α β : ℝ}
    (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (operatorPowerMean (ℋ := ℋ) α β) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hconv :=
    theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici
      (ℋ := ℋ)
      (f := fun x : ℝ ↦ x ^ α)
      (h := fun x : ℝ ↦ x ^ β)
      (hf := D5.S3.Quantum.Lieb.PowerConvexity.condIciAll_rpow hα)
      (hconc := by
        exact operatorConcaveOn_Ioi_of_Ici (ℋ := ℋ)
          (power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) β hβ))
      (hcont := by
        intro x hx
        exact (Real.continuousAt_rpow_const x β (Or.inl (ne_of_gt hx))).continuousWithinAt)
      (hpos := rpow_pos_on_Ioi β)
  simpa [operatorPowerMean] using
    hconv (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) (θ := θ)
      (pdSet_subset_psdSet (ℋ := ℋ) hA₁) (pdSet_subset_psdSet (ℋ := ℋ) hA₂)
      hB₁ hB₂ hθ0 hθ1

end OperatorGeometricMean
