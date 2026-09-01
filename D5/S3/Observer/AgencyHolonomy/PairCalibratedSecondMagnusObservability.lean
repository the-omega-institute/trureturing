/- GID: D5/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pair-adapted half-turn sampling recovers four times the finite off-diagonal holonomy energy exactly. -/

import D5.S3.Observer.AgencyHolonomy.SecondMagnusKernelNormSquare
import D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy
import Mathlib.Tactic

/-!
# Pair-calibrated second-Magnus observability

A fixed two-slot sample can vanish at resonance even when the underlying swap
curvature is nonzero. For a finite family with injective frequencies, each
off-diagonal pair has a canonical half-turn separation
`pi / (frequency p - frequency q)`. At that pair-adapted sample the frozen
second-Magnus kernel has squared norm four.

Summing these calibrated responses gives exactly four times the finite
holonomy energy, provided the curvature has zero diagonal. This is a genuine
finite reverse-observability statement. Its clocks depend on the ordered pair;
it does not yet provide one common time window, an ordered-simplex average,
an infinite-frequency frame bound, or a zeta-zero comparison.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.Observer.AgencyHolonomy.PairCalibratedSecondMagnusObservability

open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
open D5.S3.Observer.AgencyHolonomy.SecondMagnusKernelNormSquare
open D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy

universe u

/-- The pair-adapted half-turn time. Equal frequencies receive the harmless
zero convention. -/
noncomputable def pairCalibratedTime
    (frequencyP frequencyQ : ℝ) : ℝ :=
  if frequencyP = frequencyQ then 0
  else Real.pi / (frequencyP - frequencyQ)

/-- The finite energy obtained by evaluating each ordered pair at its own
half-turn time separation. -/
noncomputable def pairCalibratedSecondMagnusEnergy
    {ι : Type u} [Fintype ι]
    (frequency : ι → ℝ) (curvature : ι → ι → ℂ) : ℝ :=
  ∑ p, ∑ q,
    ‖secondMagnusSwapKernel
        (frequency p) (frequency q)
        (pairCalibratedTime (frequency p) (frequency q)) 0 *
      curvature p q‖ ^ 2

private theorem pair_calibrated_term
    {ι : Type u} [Fintype ι]
    (frequency : ι → ℝ) (curvature : ι → ι → ℂ)
    (hFrequency : Function.Injective frequency)
    (hDiagonal : ∀ p, curvature p p = 0)
    (p q : ι) :
    ‖secondMagnusSwapKernel
        (frequency p) (frequency q)
        (pairCalibratedTime (frequency p) (frequency q)) 0 *
      curvature p q‖ ^ 2 =
      4 * ‖curvature p q‖ ^ 2 := by
  by_cases hpq : p = q
  · subst q
    rw [hDiagonal p]
    simp
  · have hFrequencyNe : frequency p ≠ frequency q := by
      intro hEqual
      exact hpq (hFrequency hEqual)
    rw [pairCalibratedTime, if_neg hFrequencyNe]
    rw [norm_mul, mul_pow]
    rw [second_magnus_swap_kernel_half_turn_norm_sq
      (frequency p) (frequency q) hFrequencyNe]

/-- Pair-adapted half-turn sampling gives an exact reverse estimate: the
calibrated second-Magnus energy is four times the full finite holonomy energy. -/
theorem pair_calibrated_second_magnus_energy_eq_four_holonomy
    {ι : Type u} [Fintype ι]
    (frequency : ι → ℝ) (curvature : ι → ι → ℂ)
    (hFrequency : Function.Injective frequency)
    (hDiagonal : ∀ p, curvature p p = 0) :
    pairCalibratedSecondMagnusEnergy frequency curvature =
      4 * finiteHolonomyEnergy curvature := by
  classical
  unfold pairCalibratedSecondMagnusEnergy
  calc
    (∑ p, ∑ q,
      ‖secondMagnusSwapKernel
          (frequency p) (frequency q)
          (pairCalibratedTime (frequency p) (frequency q)) 0 *
        curvature p q‖ ^ 2) =
        ∑ p, ∑ q, 4 * ‖curvature p q‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          exact pair_calibrated_term
            frequency curvature hFrequency hDiagonal p q
    _ = 4 * finiteHolonomyEnergy curvature := by
      unfold finiteHolonomyEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]

/-- The calibrated energy vanishes exactly when every curvature entry
vanishes. -/
theorem pair_calibrated_second_magnus_energy_eq_zero_iff
    {ι : Type u} [Fintype ι]
    (frequency : ι → ℝ) (curvature : ι → ι → ℂ)
    (hFrequency : Function.Injective frequency)
    (hDiagonal : ∀ p, curvature p p = 0) :
    pairCalibratedSecondMagnusEnergy frequency curvature = 0 ↔
      ∀ p q, curvature p q = 0 := by
  rw [pair_calibrated_second_magnus_energy_eq_four_holonomy
    frequency curvature hFrequency hDiagonal]
  constructor
  · intro hEnergy p q
    have hHolonomy : finiteHolonomyEnergy curvature = 0 := by
      nlinarith
    have hExpanded :
        (∑ i : ι, ∑ j : ι, ‖curvature i j‖ ^ 2) = 0 := by
      simpa [finiteHolonomyEnergy] using hHolonomy
    have hOuter : (∑ j : ι, ‖curvature p j‖ ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i hi => Finset.sum_nonneg fun j hj => sq_nonneg ‖curvature i j‖)).1
        hExpanded p (Finset.mem_univ p)
    have hInner : ‖curvature p q‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => sq_nonneg ‖curvature p j‖)).1
        hOuter q (Finset.mem_univ q)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hInner)
  · intro hZero
    simp [finiteHolonomyEnergy, hZero]

#print axioms pair_calibrated_second_magnus_energy_eq_four_holonomy
#print axioms pair_calibrated_second_magnus_energy_eq_zero_iff

end D5.S3.Observer.AgencyHolonomy.PairCalibratedSecondMagnusObservability
