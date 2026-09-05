/- GID: D5/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion
   generality: G
   mirror-B: D5/B/S3/Analytic/ReflectedSpectrum/ReflectionInvariantBidirectionalTimeCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bidirectional reflected summability detects zero transverse displacement. -/

import D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-09-05):
   * Repository searches found the frozen `reflectedGrowthPair`, its symmetric
     readout, and reflection laws, but no owner for the bidirectional geometric
     series criterion or its convergence radius. The frozen pair is reused as
     the full two-branch carrier below.
   * Pinned Mathlib supplies `summable_geometric_iff_norm_lt_one`,
     `Summable.of_nonneg_of_le`, the real exponential order laws, and
     `Real.log_exp`.
   * Loogle found the pinned geometric-series characterization and no exact
     two-branch theorem. LeanSearch and Reservoir endpoints were unavailable;
     GitHub code search found Mathlib and downstream copies, but no exact
     reflected bidirectional criterion.
   * The source context fixes `period > 0` and discounts `0 <= beta < 1`.
     This scalar theorem does not assert a completed-zeta realization or RH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.ReflectedSpectrum.ReflectionInvariantBidirectionalTimeCriterion

open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare

/-- The termwise sum of the future and past scalar Gramian series. The two
ratios are the coordinates of the frozen reflected pair after one doubled
observation period. -/
def bidirectionalGramianTerm
    (delta period beta : ℝ) (n : ℕ) : ℝ :=
  (beta * (reflectedGrowthPair delta (2 * period)).1) ^ n +
    (beta * (reflectedGrowthPair delta (2 * period)).2) ^ n

/-- The first singular radius of the complete reflected pair. -/
def bidirectionalConvergenceRadius (delta period : ℝ) : ℝ :=
  Real.exp (-2 * period * |delta|)

/-- For a nonnegative discount, the bidirectional series is summable exactly
when both reflected geometric ratios have norm below one. -/
theorem bidirectional_gramian_summable_iff
    (delta period beta : ℝ) (hbeta : 0 ≤ beta) :
    Summable (bidirectionalGramianTerm delta period beta) ↔
      ‖beta * (reflectedGrowthPair delta (2 * period)).1‖ < 1 ∧
      ‖beta * (reflectedGrowthPair delta (2 * period)).2‖ < 1 := by
  have hfirstPositive :
      0 < (reflectedGrowthPair delta (2 * period)).1 := by
    exact Real.exp_pos _
  have hsecondPositive :
      0 < (reflectedGrowthPair delta (2 * period)).2 := by
    exact Real.exp_pos _
  have hfirstNonnegative :
      0 ≤ beta * (reflectedGrowthPair delta (2 * period)).1 :=
    mul_nonneg hbeta hfirstPositive.le
  have hsecondNonnegative :
      0 ≤ beta * (reflectedGrowthPair delta (2 * period)).2 :=
    mul_nonneg hbeta hsecondPositive.le
  constructor
  · intro hsum
    have hfirstSummable : Summable (fun n : ℕ =>
        (beta * (reflectedGrowthPair delta (2 * period)).1) ^ n) :=
      Summable.of_nonneg_of_le
        (fun n => pow_nonneg hfirstNonnegative n)
        (fun n => by
          exact le_add_of_nonneg_right (pow_nonneg hsecondNonnegative n))
        hsum
    have hsecondSummable : Summable (fun n : ℕ =>
        (beta * (reflectedGrowthPair delta (2 * period)).2) ^ n) :=
      Summable.of_nonneg_of_le
        (fun n => pow_nonneg hsecondNonnegative n)
        (fun n => by
          exact le_add_of_nonneg_left (pow_nonneg hfirstNonnegative n))
        hsum
    exact ⟨summable_geometric_iff_norm_lt_one.mp hfirstSummable,
      summable_geometric_iff_norm_lt_one.mp hsecondSummable⟩
  · rintro ⟨hfirst, hsecond⟩
    exact (summable_geometric_of_norm_lt_one hfirst).add
      (summable_geometric_of_norm_lt_one hsecond)

private theorem bidirectional_convergence_radius_lt_one_iff
    (delta period : ℝ) (hperiod : 0 < period) :
    bidirectionalConvergenceRadius delta period < 1 ↔ delta ≠ 0 := by
  constructor
  · intro hradius hdelta
    subst delta
    simp [bidirectionalConvergenceRadius] at hradius
  · intro hdelta
    apply Real.exp_lt_one_iff.mpr
    have habs : 0 < |delta| := abs_pos.mpr hdelta
    have hproduct : 0 < 2 * period * |delta| :=
      mul_pos (mul_pos (by norm_num) hperiod) habs
    linarith

private theorem recover_abs_from_bidirectional_radius
    (delta period : ℝ) (hperiod : 0 < period) :
    |delta| =
      -(1 / (2 * period)) *
        Real.log (bidirectionalConvergenceRadius delta period) := by
  rw [bidirectionalConvergenceRadius, Real.log_exp]
  field_simp [hperiod.ne']

/-- Reflection removes the orientation of the transverse displacement but not
its magnitude. At a positive observation period, zero displacement is exactly
the condition that the complete future-past Gramian is summable for every
proper discount. The first singular radius recovers the absolute displacement,
and a nonzero displacement is exactly a strict radius defect. -/
theorem reflection_invariant_bidirectional_time_criterion
    (delta period : ℝ) (hperiod : 0 < period) :
    (delta = 0 ↔
      ∀ beta : ℝ, 0 ≤ beta → beta < 1 →
        Summable (bidirectionalGramianTerm delta period beta)) ∧
      (∀ beta : ℝ, ∀ n : ℕ,
        bidirectionalGramianTerm (-delta) period beta n =
          bidirectionalGramianTerm delta period beta n) ∧
      |delta| =
        -(1 / (2 * period)) *
          Real.log (bidirectionalConvergenceRadius delta period) ∧
      (delta ≠ 0 ↔ bidirectionalConvergenceRadius delta period < 1) := by
  constructor
  · constructor
    · rintro rfl beta hbeta hbetaLt
      apply (bidirectional_gramian_summable_iff 0 period beta hbeta).2
      simpa [reflectedGrowthPair, Real.norm_eq_abs,
        abs_of_nonneg hbeta] using And.intro hbetaLt hbetaLt
    · intro hall
      by_contra hdelta
      let radius := bidirectionalConvergenceRadius delta period
      have hradiusPositive : 0 < radius := by
        exact Real.exp_pos _
      have hradiusLtOne : radius < 1 := by
        exact (bidirectional_convergence_radius_lt_one_iff
          delta period hperiod).2 hdelta
      have hsum : Summable (bidirectionalGramianTerm delta period radius) :=
        hall radius hradiusPositive.le hradiusLtOne
      have hratios :=
        (bidirectional_gramian_summable_iff
          delta period radius hradiusPositive.le).1 hsum
      rcases lt_or_gt_of_ne hdelta with hnegative | hpositive
      · have hsecondRatio :
            radius * (reflectedGrowthPair delta (2 * period)).2 = 1 := by
          simp only [radius, bidirectionalConvergenceRadius,
            reflectedGrowthPair]
          rw [← Real.exp_add, abs_of_neg hnegative, ← Real.exp_zero]
          congr 1
          ring
        rw [hsecondRatio, norm_one] at hratios
        exact lt_irrefl 1 hratios.2
      · have hfirstRatio :
            radius * (reflectedGrowthPair delta (2 * period)).1 = 1 := by
          simp only [radius, bidirectionalConvergenceRadius,
            reflectedGrowthPair]
          rw [← Real.exp_add, abs_of_pos hpositive, ← Real.exp_zero]
          congr 1
          ring
        rw [hfirstRatio, norm_one] at hratios
        exact lt_irrefl 1 hratios.1
  constructor
  · intro beta n
    simp only [bidirectionalGramianTerm, reflectedGrowthPair]
    ring_nf
  constructor
  · exact recover_abs_from_bidirectional_radius delta period hperiod
  · exact (bidirectional_convergence_radius_lt_one_iff
      delta period hperiod).symm

#print axioms bidirectional_gramian_summable_iff
#print axioms reflection_invariant_bidirectional_time_criterion

end D5.S3.Analytic.ReflectedSpectrum.ReflectionInvariantBidirectionalTimeCriterion
