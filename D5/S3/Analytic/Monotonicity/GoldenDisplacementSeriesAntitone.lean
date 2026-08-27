/- GID: D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesAntitone
   generality: I
   mirror-B: D5/B/S3/Analytic/Monotonicity/GoldenDisplacementSeriesAntitone
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The golden displacement sum decreases under coordinatewise parameter increases. -/

/- Library-search audit trail (2026-08-27):
* A repository-wide search of `D5/**/*.lean` found every declaration mentioning `dTerm` and
  found no statement relating it to `Antitone`, `Monotone`, or `StrictAnti`.
* Searches of pinned `Mathlib/**/*.lean` for real powers, exponent order, summable series,
  and termwise order found `Real.rpow_le_rpow_of_exponent_le` and
  `Summable.tsum_le_tsum`, which are used directly below.
* The repository already uses the latter call shape in `GoldenHeatSpectrum.lean:134` and
  `PrimeSpectrumHeatAbscissa.lean:162`. The exact convergence-region characterization and
  `le_nS` supply the remaining object-specific facts, so no general lemma is reproved here.
-/

import D5.S3.Analytic.Displacement.GoldenDisplacementTwoConstraintRegion

open GoldenDesubstitutionLength
open GoldenDisplacementEulerProduct
open GoldenDisplacementTwoConstraintRegion

namespace D5.S3.Analytic.Monotonicity.GoldenDisplacementSeriesAntitone

noncomputable section

private lemma dTerm_le_of_parameters_le {s1 w1 s2 w2 : ℝ}
    (hs : s1 ≤ s2) (hw : w1 ≤ w2) (n : ℕ) :
    dTerm s2 w2 n ≤ dTerm s1 w1 n := by
  by_cases hn : n = 0
  · subst n
    rw [dTerm_zero, dTerm_zero]
  · have hnOneNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnOne : (1 : ℝ) ≤ n := by
      exact_mod_cast hnOneNat
    have hnSOne : (1 : ℝ) ≤ nS n := by
      exact_mod_cast hnOneNat.trans (le_nS hn)
    unfold dTerm
    rw [if_neg hn, if_neg hn]
    exact mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hnSOne (neg_le_neg hs))
      (Real.rpow_le_rpow_of_exponent_le hnOne (neg_le_neg hw))
      (by positivity) (by positivity)

/-- If both parameters increase coordinatewise from a convergent pair, the golden displacement
sum cannot increase. Summability at the larger pair follows from the exact two-constraint region. -/
theorem golden_displacement_series_antitone {s1 w1 s2 w2 : ℝ}
    (hs : s1 ≤ s2) (hw : w1 ≤ w2) (hsum1 : Summable (dTerm s1 w1)) :
    (∑' n : ℕ, dTerm s2 w2 n) ≤ ∑' n : ℕ, dTerm s1 w1 n := by
  have hsum2 : Summable (dTerm s2 w2) := by
    rw [dTerm_summable_iff_two_constraints] at hsum1 ⊢
    constructor <;> linarith [hsum1.1, hsum1.2]
  exact hsum2.tsum_le_tsum (dTerm_le_of_parameters_le hs hw) hsum1

end

end D5.S3.Analytic.Monotonicity.GoldenDisplacementSeriesAntitone
