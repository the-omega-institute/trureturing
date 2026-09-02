/- GID: D5/S3/Fourier/Concentration/SlepianConcentrationBound
   generality: G
   mirror-B: D5/B/S3/Fourier/Concentration/SlepianConcentrationBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive concentration spectrum is bounded by one and by its trace budget. -/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/- Library-search audit trail (2026-09-02):
   * Repository searches found `FiniteRankConcentrationModeBound`, which bounds
     the number of eigenvalues above a positive threshold. It does not bound
     the maximal concentration eigenvalue by the trace.
   * Searches for Slepian operators, concentration norms, trace domination,
     spectral maxima, and semantic generalizations found no equivalent D5
     declaration.
   * Pinned Mathlib has no usable infinite-dimensional trace-class operator
     interface for this statement. The theorem therefore works with the
     nonnegative summable concentration spectrum supplied by the spectral
     theorem.
   * `Summable.sum_le_tsum` is the exact library bridge from the attained
     maximal eigenvalue to the trace. `Real.pi_ne_zero` excludes the denominator
     degeneracy in the displayed trace formula. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Fourier.Concentration.SlepianConcentrationBound

/-- A nonnegative summable concentration spectrum whose eigenvalues are at
most one has maximal eigenvalue at most both one and its Slepian trace. A zero
trace budget forces the maximum to attain the lower boundary zero. -/
theorem slepian_concentration_bound
    (concentrationEigenvalue : ℕ → ℝ)
    (intervalRadius frequencyMeasure maximumConcentration : ℝ)
    (hIntervalRadius : 0 ≤ intervalRadius)
    (hFrequencyMeasure : 0 ≤ frequencyMeasure)
    (hNonnegative : ∀ j, 0 ≤ concentrationEigenvalue j)
    (hAtMostOne : ∀ j, concentrationEigenvalue j ≤ 1)
    (hSummable : Summable concentrationEigenvalue)
    (hTrace : ∑' j, concentrationEigenvalue j =
      intervalRadius * frequencyMeasure / Real.pi)
    (hMaximum : ∃ j, maximumConcentration = concentrationEigenvalue j) :
    maximumConcentration ≤
        min 1 (intervalRadius * frequencyMeasure / Real.pi) ∧
      (intervalRadius * frequencyMeasure = 0 → maximumConcentration = 0) := by
  have hPi : Real.pi ≠ 0 := Real.pi_ne_zero
  obtain ⟨j, hMaximumAt⟩ := hMaximum
  have hEigenvalueLeTrace :
      concentrationEigenvalue j ≤ ∑' k, concentrationEigenvalue k := by
    simpa using hSummable.sum_le_tsum {j} fun k _ => hNonnegative k
  constructor
  · rw [le_min_iff]
    exact ⟨hMaximumAt.trans_le (hAtMostOne j),
      hMaximumAt.trans_le (hEigenvalueLeTrace.trans_eq hTrace)⟩
  · intro hZeroBudget
    have hDivisionSafe :
        intervalRadius * frequencyMeasure / Real.pi = 0 ↔
          intervalRadius * frequencyMeasure = 0 := by
      rw [div_eq_zero_iff, or_iff_left hPi]
    have hTraceZero : ∑' k, concentrationEigenvalue k = 0 := by
      exact hTrace.trans (hDivisionSafe.mpr hZeroBudget)
    rw [hMaximumAt]
    apply le_antisymm
    · simpa [hTraceZero] using hEigenvalueLeTrace
    · exact hNonnegative j

#print axioms slepian_concentration_bound

end D5.S3.Fourier.Concentration.SlepianConcentrationBound
