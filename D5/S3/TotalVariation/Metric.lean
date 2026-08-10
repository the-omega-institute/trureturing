/- GID: D5/S3/TotalVariation/Metric
   generality: G
   mirror-B: D5/B/S3/TotalVariation/Metric
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Prove the metric laws and finite-event variational formula for total variation. -/

/- Library-search audit trail (2026-08-10):
   * Local pinned-mathlib grep terms: `totalVariation`, `total variation`, `variation`,
     `MetricSpace`, `PiLp`, `dist_pi`, `abs_add_le`, `abs_sub_comm`,
     `sum_le_sum_of_subset_of_nonneg`, `Finset.sup'`, and `IsGreatest`.
   * Mathlib's `SignedMeasure.totalVariation` and `VectorMeasure.variation` are
     `Measure`-valued. No theorem was found that identifies either with this repository's
     finite real-valued half-`L¹` sum. The Pi metric is the sup metric; `PiLp` would require a
     new wrapper and bridge. The scalar lemmas `abs_add_le`, `abs_sub_comm`, and the finite-sum
     order lemmas are reused directly instead.
   * Repository grep over every Lean declaration below `D5/S3` found only `totalVariation`,
     `total_variation_eq_sum_positive`, and Pinsker's bound in the sibling file. No metric law,
     unit bound, or event variational characterization was found under another name.
-/

import D5.S3.TotalVariation.Pinsker

namespace D5.S3.TotalVariation.Metric

open D5.S3.TotalVariation.Pinsker

/-- Total variation is nonnegative for arbitrary finite real functions. -/
theorem total_variation_nonneg {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    0 ≤ totalVariation p q := by
  rw [totalVariation]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ ↦ abs_nonneg (p i - q i))

/-- Total variation separates arbitrary finite real functions. -/
theorem total_variation_eq_zero_iff {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    totalVariation p q = 0 ↔ p = q := by
  constructor
  · intro h
    rw [totalVariation] at h
    have hsum : (∑ i, |p i - q i|) = 0 := by
      nlinarith
    funext i
    have hi :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ abs_nonneg (p j - q j))).mp
        hsum i (Finset.mem_univ i)
    exact sub_eq_zero.mp (abs_eq_zero.mp hi)
  · rintro rfl
    simp [totalVariation]

/-- Total variation is symmetric for arbitrary finite real functions. -/
theorem total_variation_comm {ι : Type*} [Fintype ι] (p q : ι → ℝ) :
    totalVariation p q = totalVariation q p := by
  simp only [totalVariation, abs_sub_comm]

/-- Total variation satisfies the triangle inequality for arbitrary finite real functions. -/
theorem total_variation_triangle {ι : Type*} [Fintype ι] (p q r : ι → ℝ) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  rw [totalVariation, totalVariation, totalVariation]
  have hsum :
      (∑ i, |p i - r i|) ≤ ∑ i, (|p i - q i| + |q i - r i|) := by
    apply Finset.sum_le_sum
    intro i _
    calc
      |p i - r i| = |(p i - q i) + (q i - r i)| := by ring_nf
      _ ≤ |p i - q i| + |q i - r i| := abs_add_le _ _
  calc
    (1 / 2 : ℝ) * ∑ i, |p i - r i| ≤
        (1 / 2 : ℝ) * ∑ i, (|p i - q i| + |q i - r i|) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ i, |p i - q i| +
        (1 / 2 : ℝ) * ∑ i, |q i - r i| := by
      rw [Finset.sum_add_distrib]
      ring

/-- Total variation between nonnegative normalized finite mass functions is at most one. -/
theorem total_variation_le_one {ι : Type*} [Fintype ι]
    (p q : ι → ℝ)
    (hp : (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ ∑ i, q i = 1) :
    totalVariation p q ≤ 1 := by
  rw [totalVariation]
  have hsum : (∑ i, |p i - q i|) ≤ ∑ i, (p i + q i) := by
    apply Finset.sum_le_sum
    intro i _
    refine abs_le.mpr ⟨?_, ?_⟩
    · linarith [hp.1 i, hq.1 i]
    · linarith [hp.1 i, hq.1 i]
  calc
    (1 / 2 : ℝ) * ∑ i, |p i - q i| ≤
        (1 / 2 : ℝ) * ∑ i, (p i + q i) :=
      mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 1 := by
      rw [Finset.sum_add_distrib, hp.2, hq.2]
      norm_num

/-- For equal-mass finite real functions, total variation is the greatest absolute mass gap over
all events. The greatest-element formulation records both attainment and the upper bound; its
witness is the event on which `p` dominates `q`. -/
theorem total_variation_eq_sup_event_gap {ι : Type*} [Fintype ι]
    (p q : ι → ℝ) (hmass : ∑ i, p i = ∑ i, q i) :
    IsGreatest
      (Set.range fun A : Finset ι ↦
        |(∑ i ∈ A, p i) - ∑ i ∈ A, q i|)
      (totalVariation p q) := by
  classical
  have event_gap_le (a b : ι → ℝ) (hmass_ab : ∑ i, a i = ∑ i, b i)
      (A : Finset ι) :
      (∑ i ∈ A, (a i - b i)) ≤ totalVariation a b := by
    calc
      (∑ i ∈ A, (a i - b i)) =
          (∑ i ∈ A.filter (fun i ↦ b i ≤ a i), (a i - b i)) +
            ∑ i ∈ A.filter (fun i ↦ ¬b i ≤ a i), (a i - b i) := by
        rw [Finset.sum_filter_add_sum_filter_not]
      _ ≤ (∑ i ∈ A.filter (fun i ↦ b i ≤ a i), (a i - b i)) + 0 := by
        have hnonpos :
            (∑ i ∈ A.filter (fun i ↦ ¬b i ≤ a i), (a i - b i)) ≤ 0 :=
          Finset.sum_nonpos fun i hi ↦
            sub_nonpos.mpr (le_of_not_ge (Finset.mem_filter.mp hi).2)
        linarith
      _ ≤ ∑ i with b i ≤ a i, (a i - b i) := by
        rw [add_zero]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi ↦ Finset.mem_filter.mpr
            ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩)
          (fun i hi _ ↦ sub_nonneg.mpr (Finset.mem_filter.mp hi).2)
      _ = totalVariation a b :=
        (total_variation_eq_sum_positive a b hmass_ab).symm
  constructor
  · refine ⟨Finset.univ.filter (fun i ↦ q i ≤ p i), ?_⟩
    change |(∑ i with q i ≤ p i, p i) - ∑ i with q i ≤ p i, q i| =
      totalVariation p q
    rw [← Finset.sum_sub_distrib,
      ← total_variation_eq_sum_positive p q hmass,
      abs_of_nonneg (total_variation_nonneg p q)]
  · rintro x ⟨A, rfl⟩
    change |(∑ i ∈ A, p i) - ∑ i ∈ A, q i| ≤ totalVariation p q
    rw [← Finset.sum_sub_distrib]
    refine abs_le.mpr ⟨?_, event_gap_le p q hmass A⟩
    have hreverse := event_gap_le q p hmass.symm A
    have hneg :
        (∑ i ∈ A, (q i - p i)) = -(∑ i ∈ A, (p i - q i)) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hneg, total_variation_comm q p] at hreverse
    linarith

end D5.S3.TotalVariation.Metric
