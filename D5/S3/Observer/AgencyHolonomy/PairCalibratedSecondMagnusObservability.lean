/- GID: D5/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/PairCalibratedSecondMagnusObservability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Pair-adapted samples recover four times the finite holonomy energy. -/

import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import D5.S3.Observer.AgencyHolonomy.FiniteHolonomyEnergy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

private theorem local_second_magnus_swap_kernel_norm_sq
    (frequencyP frequencyQ time1 time2 : ℝ) :
    ‖secondMagnusSwapKernel frequencyP frequencyQ time1 time2‖ ^ 2 =
      4 * Real.sin
        ((time1 - time2) * ((frequencyP - frequencyQ) / 2)) ^ 2 := by
  rw [second_magnus_swap_kernel_sine_form]
  have hPhase :
      ‖Complex.exp
          (-Complex.I * ((time1 + time2 : ℝ) : ℂ) *
            (((frequencyP + frequencyQ) / 2 : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hCoefficient : ‖(-2 : ℂ) * Complex.I‖ = 2 := by
    norm_num
  have hSineComplex :
      Complex.sin
          ((((time1 - time2) *
            ((frequencyP - frequencyQ) / 2) : ℝ) : ℂ)) =
        (Real.sin
          ((time1 - time2) * ((frequencyP - frequencyQ) / 2)) : ℂ) := by
    exact (Complex.ofReal_sin _).symm
  rw [norm_mul, norm_mul, hCoefficient, hPhase, hSineComplex,
    Complex.norm_real, Real.norm_eq_abs, mul_one]
  nlinarith [sq_abs
    (Real.sin ((time1 - time2) * ((frequencyP - frequencyQ) / 2)))]

private theorem pair_calibrated_kernel_half_turn_norm_sq
    (frequencyP frequencyQ : ℝ)
    (hFrequency : frequencyP ≠ frequencyQ) :
    ‖secondMagnusSwapKernel frequencyP frequencyQ
        (Real.pi / (frequencyP - frequencyQ)) 0‖ ^ 2 = 4 := by
  rw [local_second_magnus_swap_kernel_norm_sq]
  have hGap : frequencyP - frequencyQ ≠ 0 := sub_ne_zero.mpr hFrequency
  have hArea :
      (Real.pi / (frequencyP - frequencyQ) - 0) *
          ((frequencyP - frequencyQ) / 2) = Real.pi / 2 := by
    field_simp [hGap]
    ring
  rw [hArea, Real.sin_pi_div_two]
  norm_num

private theorem pair_calibrated_term
    {ι : Type u}
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
    rw [pair_calibrated_kernel_half_turn_norm_sq
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
