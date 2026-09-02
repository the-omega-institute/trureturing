/- GID: D5/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup
   generality: G
   mirror-B: D5/B/S3/Analytic/ReflectedSpectrum/ReflectedGrowthPairTimeGroup
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The oriented reflected pair is a faithful one-parameter multiplicative group, while symmetric observation loses parameter orientation. -/

import D5.S3.Analytic.ReflectedSpectrum.ReflectedGrowthPairEvenOddDecomposition
import Mathlib.Tactic

/- Library-search audit trail (2026-09-01):
   * Repository searches for `ReflectedGrowthPairTimeGroup` and
     `OrientedTimeRecoverySymmetricTimeLoss` found only research targets in the
     consolidated RH theory volume, with no Lean owner.
   * `ReflectedGrowthPairNegativeSquare` already owns the exponential pair,
     reciprocal product, time-reversal exchange, and symmetric readout.
   * `ReflectedGrowthPairEvenOddDecomposition` already owns the even and odd
     channels and exact branch reconstruction. Both are imported and reused.
   * Pinned Mathlib supplies the product-group instances and real exponential
     addition/injectivity laws. This file does not redeclare a custom group.
   * The parameter is an auxiliary one-parameter group coordinate. The theorem
     does not identify it with physical time or assert a completed-zeta flow. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Analytic.ReflectedSpectrum.ReflectedGrowthPairTimeGroup

open D5.S3.Analytic.Adelic.ReflectedGrowthPairNegativeSquare
open D5.S3.Analytic.Adelic.ReflectedGrowthPairSecondOrderSpectrum
open D5.S3.Analytic.ReflectedSpectrum.ReflectedGrowthPairEvenOddDecomposition

/-- The jointly observed even and odd channels. This observer retains the
orientation erased by the even channel alone. -/
def orientedEvenOddObservation (delta time : ℝ) : ℝ × ℝ :=
  (evenObservation delta time, oddObservation delta time)

/-- The reflected pair starts at the multiplicative identity. -/
theorem reflected_growth_pair_zero (delta : ℝ) :
    reflectedGrowthPair delta 0 = (1, 1) := by
  simp [reflectedGrowthPair]

/-- Addition of the parameter is coordinatewise multiplication of the two
reflected branches. -/
theorem reflected_growth_pair_add (delta first second : ℝ) :
    reflectedGrowthPair delta (first + second) =
      reflectedGrowthPair delta first * reflectedGrowthPair delta second := by
  ext
  · change Real.exp (delta * (first + second)) =
      Real.exp (delta * first) * Real.exp (delta * second)
    rw [mul_add, Real.exp_add]
  · change Real.exp (-(delta * (first + second))) =
      Real.exp (-(delta * first)) * Real.exp (-(delta * second))
    rw [show -(delta * (first + second)) =
      -(delta * first) + -(delta * second) by ring, Real.exp_add]

/-- Negative parameter is the multiplicative inverse of the oriented pair. -/
theorem reflected_growth_pair_neg_eq_inv (delta time : ℝ) :
    reflectedGrowthPair delta (-time) =
      (reflectedGrowthPair delta time)⁻¹ := by
  ext
  · change Real.exp (delta * (-time)) = (Real.exp (delta * time))⁻¹
    rw [show delta * (-time) = -(delta * time) by ring, Real.exp_neg]
  · change Real.exp (-(delta * (-time))) =
      (Real.exp (-(delta * time)))⁻¹
    rw [show -(delta * (-time)) = -(-(delta * time)) by ring, Real.exp_neg]

/-- The reflected pair is a one-parameter multiplicative group. -/
theorem reflected_growth_pair_time_group (delta : ℝ) :
    reflectedGrowthPair delta 0 = (1, 1) ∧
      (∀ first second,
        reflectedGrowthPair delta (first + second) =
          reflectedGrowthPair delta first * reflectedGrowthPair delta second) ∧
      (∀ time,
        reflectedGrowthPair delta (-time) =
          (reflectedGrowthPair delta time)⁻¹) := by
  exact ⟨reflected_growth_pair_zero delta,
    reflected_growth_pair_add delta,
    reflected_growth_pair_neg_eq_inv delta⟩

/-- A nonzero reflected split makes the full oriented pair a faithful
observation of the parameter. -/
theorem reflected_growth_pair_injective
    (delta : ℝ) (hdelta : delta ≠ 0) :
    Function.Injective (reflectedGrowthPair delta) := by
  intro first second heq
  have hfirstCoordinate :
      Real.exp (delta * first) = Real.exp (delta * second) := by
    simpa [reflectedGrowthPair] using congrArg Prod.fst heq
  have harguments : delta * first = delta * second := by
    apply Real.exp_injective
    exact hfirstCoordinate
  have hzero : delta * (first - second) = 0 := by
    linarith
  have hdifference : first - second = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hdelta
  linarith

/-- The branch-forgetting symmetric readout is never injective: it identifies
`time` with `-time`. -/
theorem reflected_growth_sum_not_injective (delta : ℝ) :
    ¬ Function.Injective (reflectedGrowthSum delta) := by
  intro hinjective
  have hcollision : reflectedGrowthSum delta (-1) =
      reflectedGrowthSum delta 1 :=
    reflected_growth_sum_even delta 1
  have himpossible : (-1 : ℝ) = 1 := hinjective hcollision
  norm_num at himpossible

/-- For a nonzero split, observing the even and odd channels together restores
faithful parameter recovery. -/
theorem oriented_even_odd_observation_injective
    (delta : ℝ) (hdelta : delta ≠ 0) :
    Function.Injective (orientedEvenOddObservation delta) := by
  intro first second heq
  have hsum :
      evenObservation delta first + oddObservation delta first =
        evenObservation delta second + oddObservation delta second := by
    exact congrArg (fun pair : ℝ × ℝ => pair.1 + pair.2) heq
  have hpositive :
      positiveRateBranch delta first = positiveRateBranch delta second := by
    calc
      positiveRateBranch delta first =
          evenObservation delta first + oddObservation delta first :=
        (reflected_branches_reconstruct_from_even_odd delta first).1.symm
      _ = evenObservation delta second + oddObservation delta second := hsum
      _ = positiveRateBranch delta second :=
        (reflected_branches_reconstruct_from_even_odd delta second).1
  have harguments : delta * first = delta * second := by
    apply Real.exp_injective
    simpa [positiveRateBranch, reflectedGrowthPair] using hpositive
  have hzero : delta * (first - second) = 0 := by
    linarith
  have hdifference : first - second = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hdelta
  linarith

/-- The complete observer statement: the full oriented state and the joint
Even-Odd observer recover the parameter, while symmetric observation loses its
orientation. Negative parameter is the inverse group element. -/
theorem oriented_time_recovery_symmetric_time_loss
    (delta : ℝ) (hdelta : delta ≠ 0) :
    Function.Injective (reflectedGrowthPair delta) ∧
      ¬ Function.Injective (reflectedGrowthSum delta) ∧
      Function.Injective (orientedEvenOddObservation delta) ∧
      ∀ time,
        reflectedGrowthPair delta (-time) =
          (reflectedGrowthPair delta time)⁻¹ := by
  exact ⟨reflected_growth_pair_injective delta hdelta,
    reflected_growth_sum_not_injective delta,
    oriented_even_odd_observation_injective delta hdelta,
    reflected_growth_pair_neg_eq_inv delta⟩

/-- The nonzero-split hypotheses are inhabited. -/
example : Function.Injective (reflectedGrowthPair 1) := by
  exact reflected_growth_pair_injective 1 one_ne_zero

#print axioms reflected_growth_pair_time_group
#print axioms reflected_growth_pair_injective
#print axioms reflected_growth_sum_not_injective
#print axioms oriented_even_odd_observation_injective
#print axioms oriented_time_recovery_symmetric_time_loss

end D5.S3.Analytic.ReflectedSpectrum.ReflectedGrowthPairTimeGroup
