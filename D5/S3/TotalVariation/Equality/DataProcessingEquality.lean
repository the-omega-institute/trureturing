/- GID: D5/S3/TotalVariation/Equality/DataProcessingEquality
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Equality/DataProcessingEquality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Characterize equality in total-variation contraction by absence of sign mixing. -/

/- Library-search audit trail (2026-08-15):
   * Repository searches for total-variation channel equality, sign coherence, and no sign mixing
     found no existing theorem beyond the sibling contraction inequality.
   * Pinned-mathlib searches for finite absolute-sum equality and triangle-equality criteria found
     no matching characterization. The proof reuses `Finset.abs_sum_le_sum_abs`,
     `Finset.sum_eq_sum_iff_of_le`, and `Finset.sum_eq_zero_iff_of_nonneg`.
-/

import D5.S3.TotalVariation.DataProcessing

namespace D5.S3.TotalVariation.Equality.DataProcessingEquality

open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker

private theorem abs_sum_eq_sum_abs_iff_sign_coherent
    {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    |∑ i, f i| = ∑ i, |f i| ↔
      (∀ i, 0 ≤ f i) ∨ ∀ i, f i ≤ 0 := by
  classical
  let P : ℝ := ∑ i with 0 ≤ f i, f i
  let N : ℝ := ∑ i with ¬0 ≤ f i, -f i
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact Finset.sum_nonneg fun i hi => (Finset.mem_filter.mp hi).2
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    exact Finset.sum_nonneg fun i hi => neg_nonneg.mpr (le_of_not_ge (Finset.mem_filter.mp hi).2)
  have hsum : (∑ i, f i) = P - N := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 ≤ f i) f]
    dsimp [P, N]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    simp
  have habs : (∑ i, |f i|) = P + N := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 ≤ f i) (fun i => |f i|)]
    dsimp [P, N]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      exact abs_of_nonneg (Finset.mem_filter.mp hi).2
    · apply Finset.sum_congr rfl
      intro i hi
      exact abs_of_nonpos (le_of_not_ge (Finset.mem_filter.mp hi).2)
  rw [hsum, habs]
  have hscalar : |P - N| = P + N ↔ P = 0 ∨ N = 0 := by
    constructor
    · intro h
      by_cases hPN : P ≤ N
      · left
        rw [abs_of_nonpos (sub_nonpos.mpr hPN)] at h
        linarith
      · right
        rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hPN))] at h
        linarith
    · rintro (hP | hN)
      · rw [hP]
        simp [hN_nonneg]
      · rw [hN]
        simp [hP_nonneg]
  rw [hscalar]
  constructor
  · rintro (hP | hN)
    · right
      intro i
      by_cases hi : 0 ≤ f i
      · have hzero :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j hj => (Finset.mem_filter.mp hj).2)).mp hP i
              (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
        exact hzero.le
      · exact le_of_not_ge hi
    · left
      intro i
      by_cases hi : 0 ≤ f i
      · exact hi
      · have hzero :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun j hj => neg_nonneg.mpr (le_of_not_ge (Finset.mem_filter.mp hj).2))).mp hN i
              (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
        linarith
  · rintro (hpos | hneg)
    · right
      dsimp [N]
      apply Finset.sum_eq_zero
      intro i hi
      exact (Finset.mem_filter.mp hi).2 (hpos i) |>.elim
    · left
      dsimp [P]
      apply Finset.sum_eq_zero
      intro i hi
      exact le_antisymm (hneg i) (Finset.mem_filter.mp hi).2

/-- Equality in total-variation data processing holds exactly when, at each output,
the signed input discrepancy has one sign on the channel support. -/
private theorem total_variation_channel_eq_iff_sign_coherent
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    totalVariation (channelOutput W p) (channelOutput W q) = totalVariation p q ↔
      ∀ y, (∀ x, 0 ≤ (p x - q x) * W x y) ∨
        ∀ x, (p x - q x) * W x y ≤ 0 := by
  classical
  have houtput :
      totalVariation (channelOutput W p) (channelOutput W q) =
        (1 / 2 : ℝ) * ∑ y, |∑ x, (p x - q x) * W x y| := by
    rw [totalVariation]
    apply congrArg ((1 / 2 : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro y _
    congr 1
    rw [channelOutput, channelOutput, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have htransport :
      (∑ y, ∑ x, |(p x - q x) * W x y|) = ∑ x, |p x - q x| := by
    calc
      (∑ y, ∑ x, |(p x - q x) * W x y|) =
          ∑ y, ∑ x, |p x - q x| * W x y := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro x _
        rw [abs_mul, abs_of_nonneg (hW.1 x y)]
      _ = ∑ x, ∑ y, |p x - q x| * W x y := Finset.sum_comm
      _ = ∑ x, |p x - q x| := by
        apply Finset.sum_congr rfl
        intro x _
        rw [← Finset.mul_sum, hW.2 x, mul_one]
  have hinput :
      totalVariation p q =
        (1 / 2 : ℝ) * ∑ y, ∑ x, |(p x - q x) * W x y| := by
    rw [totalVariation, htransport]
  rw [houtput, hinput]
  constructor
  · intro h
    have hsum :
        (∑ y, |∑ x, (p x - q x) * W x y|) =
          ∑ y, ∑ x, |(p x - q x) * W x y| := by
      linarith
    have hpoint :=
      (Finset.sum_eq_sum_iff_of_le
        (fun y (_hy : y ∈ (Finset.univ : Finset Y)) =>
          Finset.abs_sum_le_sum_abs (fun x => (p x - q x) * W x y) Finset.univ)).mp hsum
    intro y
    exact (abs_sum_eq_sum_abs_iff_sign_coherent
      (fun x => (p x - q x) * W x y)).mp (hpoint y (Finset.mem_univ y))
  · intro h
    apply congrArg ((1 / 2 : ℝ) * ·)
    apply Finset.sum_congr rfl
    intro y _
    exact (abs_sum_eq_sum_abs_iff_sign_coherent
      (fun x => (p x - q x) * W x y)).mpr (h y)

/-- A channel preserves total variation exactly when no output mixes the strictly positive and
strictly negative supports of the signed discrepancy `p - q`. -/
theorem total_variation_channel_eq_iff_no_sign_mixing
    {X Y : Type*} [Fintype X] [Fintype Y]
    (p q : X → ℝ) (W : X → Y → ℝ)
    (hW : (∀ x y, 0 ≤ W x y) ∧ ∀ x, ∑ y, W x y = 1) :
    totalVariation (channelOutput W p) (channelOutput W q) = totalVariation p q ↔
      ∀ y, (∀ x, p x < q x → W x y = 0) ∨
        ∀ x, q x < p x → W x y = 0 := by
  rw [total_variation_channel_eq_iff_sign_coherent p q W hW]
  constructor
  · intro h y
    rcases h y with hnonneg | hnonpos
    · left
      intro x hx
      apply le_antisymm _ (hW.1 x y)
      by_contra hnot
      exact (not_lt_of_ge (hnonneg x))
        (mul_neg_of_neg_of_pos (sub_neg.mpr hx) (lt_of_not_ge hnot))
    · right
      intro x hx
      apply le_antisymm _ (hW.1 x y)
      by_contra hnot
      exact (not_lt_of_ge (hnonpos x))
        (mul_pos (sub_pos.mpr hx) (lt_of_not_ge hnot))
  · intro h y
    rcases h y with hnegative | hpositive
    · left
      intro x
      by_cases hx : p x < q x
      · rw [hnegative x hx, mul_zero]
      · exact mul_nonneg (sub_nonneg.mpr (le_of_not_gt hx)) (hW.1 x y)
    · right
      intro x
      by_cases hx : q x < p x
      · rw [hpositive x hx, mul_zero]
      · exact mul_nonpos_of_nonpos_of_nonneg
          (sub_nonpos.mpr (le_of_not_gt hx)) (hW.1 x y)

#print axioms total_variation_channel_eq_iff_no_sign_mixing

end D5.S3.TotalVariation.Equality.DataProcessingEquality
