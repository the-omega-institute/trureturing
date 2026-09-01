/- GID: D5/S3/Analytic/Adelic/ReflectedGrowthPairEvenOddDecomposition
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/ReflectedGrowthPairEvenOddDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Even and odd reflected channels separate invariant magnitude from time orientation. -/

import D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Repository searches for `ReflectedGrowthPairEvenOddObservation`,
     `ReflectedGrowthPairEvenOddDecomposition`, `evenObservation`, and
     `oddObservation` found only research targets, with no existing Lean owner.
   * The frozen owners `ReflectedGrowthPairNegativeSquare` and
     `ReflectedGrowthPairSecondOrderSpectrum` already provide the reciprocal
     branches, time-reversal exchange, forward orientation, and exact
     derivative laws. They are imported and reused rather than reproved.
   * Pinned Mathlib contains the analogous hyperbolic identity
     `cosh_sq_sub_sinh_sq`; this module keeps the repository's existing branch
     vocabulary and derives the same invariant from the frozen reciprocal
     product. No new transcendental identity is introduced.
   * The result is a scalar reflected-mode decomposition. It does not identify
     the parameter with physical time or assert a completed-zeta realization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.Adelic.ReflectedGrowthPairEvenOddDecomposition

open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
open D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum

/-- The reflection-invariant channel obtained by averaging the two branches. -/
def evenObservation (delta time : ℝ) : ℝ :=
  (positiveRateBranch delta time + negativeRateBranch delta time) / 2

/-- The oriented channel obtained by taking half the branch difference. -/
def oddObservation (delta time : ℝ) : ℝ :=
  (positiveRateBranch delta time - negativeRateBranch delta time) / 2

/-- Reversing the parameter turns the positive-rate branch into the reflected branch. -/
theorem positive_rate_branch_time_reversal (delta time : ℝ) :
    positiveRateBranch delta (-time) = negativeRateBranch delta time := by
  simp [positiveRateBranch, negativeRateBranch, reflectedGrowthPair]

/-- Reversing the parameter turns the reflected branch into the positive-rate branch. -/
theorem negative_rate_branch_time_reversal (delta time : ℝ) :
    negativeRateBranch delta (-time) = positiveRateBranch delta time := by
  simp [positiveRateBranch, negativeRateBranch, reflectedGrowthPair]

/-- The averaged channel is invariant under parameter reversal. -/
theorem even_observation_even (delta time : ℝ) :
    evenObservation delta (-time) = evenObservation delta time := by
  simp only [evenObservation, positive_rate_branch_time_reversal,
    negative_rate_branch_time_reversal]
  ring

/-- The difference channel changes sign under parameter reversal. -/
theorem odd_observation_odd (delta time : ℝ) :
    oddObservation delta (-time) = -oddObservation delta time := by
  simp only [oddObservation, positive_rate_branch_time_reversal,
    negative_rate_branch_time_reversal]
  ring

/-- The even and odd channels reconstruct both oriented branches exactly. -/
theorem reflected_branches_reconstruct_from_even_odd (delta time : ℝ) :
    evenObservation delta time + oddObservation delta time =
        positiveRateBranch delta time ∧
      evenObservation delta time - oddObservation delta time =
        negativeRateBranch delta time := by
  constructor <;> simp [evenObservation, oddObservation] <;> ring

/-- The reciprocal branch law becomes the Lorentzian invariant
`even^2 - odd^2 = 1`. -/
theorem even_sq_sub_odd_sq (delta time : ℝ) :
    evenObservation delta time ^ 2 - oddObservation delta time ^ 2 = 1 := by
  have hreciprocal :
      positiveRateBranch delta time * negativeRateBranch delta time = 1 := by
    simpa [positiveRateBranch, negativeRateBranch] using
      reflected_growth_pair_reciprocal delta time
  simp only [evenObservation, oddObservation]
  nlinarith

/-- The odd channel vanishes exactly when the split or the parameter vanishes. -/
theorem odd_observation_eq_zero_iff (delta time : ℝ) :
    oddObservation delta time = 0 ↔ delta = 0 ∨ time = 0 := by
  constructor
  · intro hzero
    have hbranches :
        positiveRateBranch delta time = negativeRateBranch delta time := by
      unfold oddObservation at hzero
      linarith
    have harguments : delta * time = -(delta * time) := by
      apply Real.exp_injective
      simpa [positiveRateBranch, negativeRateBranch, reflectedGrowthPair] using hbranches
    have hproduct : delta * time = 0 := by linarith
    exact mul_eq_zero.mp hproduct
  · rintro (rfl | rfl) <;>
      simp [oddObservation, positiveRateBranch, negativeRateBranch,
        reflectedGrowthPair]

/-- A positive split observed in the positive parameter direction has positive
odd orientation. -/
theorem odd_observation_positive_of_forward_orientation
    (delta time : ℝ) (hdelta : 0 < delta) (htime : 0 < time) :
    0 < oddObservation delta time := by
  have hforward := reflected_growth_pair_forward_orientation delta time hdelta htime
  have hnegative_lt_positive :
      negativeRateBranch delta time < positiveRateBranch delta time := by
    exact (show negativeRateBranch delta time < 1 by
      simpa [negativeRateBranch] using hforward.2).trans
        (show 1 < positiveRateBranch delta time by
          simpa [positiveRateBranch] using hforward.1)
  unfold oddObservation
  linarith

/-- The complete finite decomposition: the even channel is invariant, the odd
channel carries orientation, both branches are recovered, and their reciprocal
law is the unit Lorentzian hyperbola. -/
theorem reflected_growth_pair_even_odd_decomposition (delta time : ℝ) :
    evenObservation delta (-time) = evenObservation delta time ∧
      oddObservation delta (-time) = -oddObservation delta time ∧
      evenObservation delta time + oddObservation delta time =
        positiveRateBranch delta time ∧
      evenObservation delta time - oddObservation delta time =
        negativeRateBranch delta time ∧
      evenObservation delta time ^ 2 - oddObservation delta time ^ 2 = 1 := by
  exact ⟨even_observation_even delta time,
    odd_observation_odd delta time,
    (reflected_branches_reconstruct_from_even_odd delta time).1,
    (reflected_branches_reconstruct_from_even_odd delta time).2,
    even_sq_sub_odd_sq delta time⟩

/-- The hypotheses of forward orientation are inhabited. -/
example : 0 < oddObservation 1 1 := by
  exact odd_observation_positive_of_forward_orientation 1 1 zero_lt_one zero_lt_one

#print axioms reflected_growth_pair_even_odd_decomposition
#print axioms odd_observation_eq_zero_iff
#print axioms odd_observation_positive_of_forward_orientation

end D5.S3.Analytic.Adelic.ReflectedGrowthPairEvenOddDecomposition
