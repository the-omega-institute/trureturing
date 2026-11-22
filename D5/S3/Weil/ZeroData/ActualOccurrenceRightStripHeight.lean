/- GID: D5/S3/Weil/ZeroData/ActualOccurrenceRightStripHeight
   generality: I
   mirror-B: D5/B/S3/Weil/ZeroData/ActualOccurrenceRightStripHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Reciprocal heights are summable on actual right-strip zero occurrences. -/

import D5.S3.Weil.RightStripZeroDensity
import D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
import D5.S3.Weil.ZetaBridge.ClassicExplicitFormula

/-! Reciprocal heights in a fixed right strip on the actual Robin occurrence indices. -/

set_option autoImplicit false

namespace D5.S3.Weil.ZeroData.ActualOccurrenceRightStripHeight

open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds
open D5.S3.Weil.ZetaBridge.ClassicExplicitFormula (zeroEquiv multiplicity_eq_zeroMult)

/-- The reciprocal absolute heights to the right of `σ > 1/2` are summable on
the actual occurrence indices, with every zero repeated at its analytic order. -/
theorem actual_rightStrip_inverse_height_summable {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun k : ℕ =>
      if σ < (actualZero k).re then |(actualZero k).im|⁻¹ else 0) := by
  classical
  let rightIndices : Set ℕ := {n | σ < (actualData.zero n).re}
  let toRightStrip : rightIndices → {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ σ < ρ.re} :=
    fun n => ⟨actualData.zero n.1, (zeroEquiv actualData n.1).property, n.property⟩
  have hinj : Function.Injective toRightStrip := by
    intro n m h
    apply Subtype.ext
    exact actualData.zero_injective (congrArg Subtype.val h)
  let weightedHeight (n : ℕ) : ℝ :=
    (actualData.multiplicity n : ℝ) * |(actualData.zero n).im|⁻¹
  have hsub : Summable (weightedHeight ∘ (Subtype.val : rightIndices → ℕ)) := by
    refine ((Zeta23.summable_rightStrip_inverse_height hσ).comp_injective hinj).congr ?_
    intro n
    change (Zeta23.zeroMult (actualData.zero n.1) : ℝ) / |(actualData.zero n.1).im| =
      (actualData.multiplicity n.1 : ℝ) * |(actualData.zero n.1).im|⁻¹
    rw [← multiplicity_eq_zeroMult actualData n.1, div_eq_mul_inv]
  let cutoffHeight (n : ℕ) : ℝ :=
    if σ < (actualData.zero n).re then |(actualData.zero n).im|⁻¹ else 0
  have hweighted : Summable (fun n : ℕ => (actualData.multiplicity n : ℝ) * cutoffHeight n) := by
    have hind : Summable (rightIndices.indicator weightedHeight) :=
      summable_subtype_iff_indicator.mp hsub
    refine hind.congr fun n => ?_
    by_cases hn : σ < (actualData.zero n).re
    · have hmem : n ∈ rightIndices := hn
      simp only [Set.indicator_of_mem hmem, weightedHeight, cutoffHeight, if_pos hn]
    · have hmem : n ∉ rightIndices := hn
      simp only [Set.indicator_of_notMem hmem, cutoffHeight, if_neg hn, mul_zero]
  have hnonneg (n : ℕ) : 0 ≤ cutoffHeight n := by
    dsimp only [cutoffHeight]
    split
    · exact inv_nonneg.mpr (abs_nonneg _)
    · exact le_rfl
  have hfibers : Summable (fun p : ActualZeroOccurrence => cutoffHeight p.1) := by
    apply (summable_sigma_of_nonneg (fun p : ActualZeroOccurrence => hnonneg p.1)).2
    constructor
    · intro n
      exact Summable.of_finite
    · simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] using hweighted
  apply ((actualOccurrenceEquiv.summable_iff).2 hfibers).congr
  intro k
  simp only [Function.comp_apply, cutoffHeight, actualZero]
  exact congrArg
    (fun d : Decidable (σ < (actualData.zero (actualOccurrenceEquiv k).1).re) =>
      @ite ℝ _ d |(actualData.zero (actualOccurrenceEquiv k).1).im|⁻¹ 0)
    (Subsingleton.elim _ _)

/-- Selecting positive ordinates yields the reciprocal-height series used by
the compact filter, on the same actual occurrence indices. -/
theorem actual_positive_rightStrip_inverse_height_summable {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun k : ℕ =>
      if σ < (actualZero k).re ∧ 0 < (actualZero k).im then (actualZero k).im⁻¹ else 0) := by
  refine Summable.of_nonneg_of_le ?_ ?_ (actual_rightStrip_inverse_height_summable hσ)
  · intro k
    by_cases hk : σ < (actualZero k).re ∧ 0 < (actualZero k).im
    · rw [if_pos hk]
      exact inv_nonneg.mpr hk.2.le
    · simp only [if_neg hk, le_refl]
  · intro k
    by_cases hk : σ < (actualZero k).re ∧ 0 < (actualZero k).im
    · simp only [if_pos hk, if_pos hk.1, abs_of_pos hk.2, le_refl]
    · rw [if_neg hk]
      split
      · exact inv_nonneg.mpr (abs_nonneg _)
      · exact le_rfl

end D5.S3.Weil.ZeroData.ActualOccurrenceRightStripHeight
