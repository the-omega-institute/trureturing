/- GID: D5/S3/Observer/Tomography/FiniteRankConcentrationModeBound
   generality: G
   mirror-B: D5/B/S3/Observer/Tomography/FiniteRankConcentrationModeBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite trace budget bounds and finitely supports every positive spectral superlevel. -/

import D5.S3.Observer.Tomography.InnovationCountBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/- Library-search audit trail (2026-08-31):
   * Repository searches for summable superlevel counts found the frozen general owner
     `large_innovation_count_le_budget_div`, which is applied to the concentration spectrum below.
     Its public statement gives the count inequality but does not expose superlevel finiteness.
   * Pinned Mathlib searches found no theorem stating both public clauses. The owner already applies
     the exact supporting results `Summable.tendsto_atTop_zero`, `Finset.card_nsmul_le_sum`, and
     `Summable.sum_le_tsum`; this extension reuses the owner and exposes its finiteness argument.
-/

namespace D5.S3.Observer.Tomography.FiniteRankConcentrationModeBound

open D5.S3.Observer.Tomography.InnovationCountBound

/-- A nonnegative summable concentration spectrum with the stated trace has only finitely many
modes above a positive threshold, and their count obeys the trace-normalized bound. -/
theorem finite_rank_concentration_mode_bound
    (concentrationEigenvalue : ℕ → ℝ) (intervalRadius frequencyMeasure threshold : ℝ)
    (hNonneg : ∀ j, 0 ≤ concentrationEigenvalue j)
    (hSummable : Summable concentrationEigenvalue)
    (hTrace : ∑' j, concentrationEigenvalue j =
      intervalRadius * frequencyMeasure / Real.pi)
    (hThreshold : 0 < threshold) :
    Set.Finite {j | threshold ≤ concentrationEigenvalue j} ∧
      (({j | threshold ≤ concentrationEigenvalue j} : Set ℕ).ncard : ℝ) ≤
        intervalRadius * frequencyMeasure / (Real.pi * threshold) := by
  have hZero := hSummable.tendsto_atTop_zero
  simp only [Metric.tendsto_atTop, Real.dist_eq, sub_zero] at hZero
  obtain ⟨N, hN⟩ := hZero threshold hThreshold
  have hFinite : Set.Finite {j | threshold ≤ concentrationEigenvalue j} := by
    apply (Set.finite_Iio N).subset
    intro j hj
    simp only [Set.mem_setOf_eq] at hj
    by_contra hjN
    have hNj : N ≤ j := Nat.le_of_not_gt hjN
    have hAbs : |concentrationEigenvalue j| < threshold := hN j hNj
    exact (not_lt_of_ge hj) ((le_abs_self (concentrationEigenvalue j)).trans_lt hAbs)
  refine ⟨hFinite, ?_⟩
  simpa [div_div] using
    large_innovation_count_le_budget_div concentrationEigenvalue
      (intervalRadius * frequencyMeasure / Real.pi) threshold
      hNonneg hSummable hTrace.le hThreshold

#print axioms finite_rank_concentration_mode_bound

end D5.S3.Observer.Tomography.FiniteRankConcentrationModeBound
