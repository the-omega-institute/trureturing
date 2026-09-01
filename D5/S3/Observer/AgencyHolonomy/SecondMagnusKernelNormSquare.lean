/- GID: D5/S3/Observer/AgencyHolonomy/SecondMagnusKernelNormSquare
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/SecondMagnusKernelNormSquare
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the exact squared strength of the alternating Fourier slot kernel and exhibit a maximal nonresonant sample. -/

import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Exact second-Magnus kernel strength

The frozen second-Magnus slot kernel already has a sine form and a uniform
upper bound. This module removes the remaining norm inequality: the squared
kernel norm is exactly four times the squared sine of half the time-frequency
area. Every pair of distinct frequencies therefore admits an explicit
half-turn time separation at which the kernel has maximal squared norm four.

The result is pairwise and finite. It does not provide a common sampling clock
for a whole frequency family, an ordered-simplex integral, a Magnus-series
convergence theorem, a prime-zero transport, or a zero-location statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.AgencyHolonomy.SecondMagnusKernelNormSquare

open D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature

/-- The real half-area controlling the alternating two-slot Fourier kernel. -/
def secondMagnusHalfArea
    (frequencyP frequencyQ time1 time2 : ℝ) : ℝ :=
  (time1 - time2) * ((frequencyP - frequencyQ) / 2)

/-- The squared kernel norm is exactly the squared sine response to the
half-area swept out by the two time and frequency slots. -/
theorem second_magnus_swap_kernel_norm_sq
    (frequencyP frequencyQ time1 time2 : ℝ) :
    ‖secondMagnusSwapKernel frequencyP frequencyQ time1 time2‖ ^ 2 =
      4 * Real.sin
        (secondMagnusHalfArea frequencyP frequencyQ time1 time2) ^ 2 := by
  rw [second_magnus_swap_kernel_sine_form]
  have hPhase :
      ‖Complex.exp
          (-Complex.I * ((time1 + time2 : ℝ) : ℂ) *
            (((frequencyP + frequencyQ) / 2 : ℝ) : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  have hSine :
      ‖Complex.sin
          (((secondMagnusHalfArea frequencyP frequencyQ time1 time2 : ℝ) : ℂ))‖ =
        |Real.sin
          (secondMagnusHalfArea frequencyP frequencyQ time1 time2)| := by
    rw [← Complex.ofReal_sin]
    simp
  rw [norm_mul, norm_mul, hPhase, hSine]
  have hCoefficient : ‖(-2 : ℂ) * Complex.I‖ = 2 := by norm_num
  rw [hCoefficient]
  rw [sq_abs]
  ring

/-- Distinct frequencies can be sampled at the explicit half-turn separation
`pi / (frequencyP - frequencyQ)`, where the kernel response is maximal. -/
theorem second_magnus_swap_kernel_half_turn_norm_sq
    (frequencyP frequencyQ : ℝ)
    (hFrequency : frequencyP ≠ frequencyQ) :
    ‖secondMagnusSwapKernel frequencyP frequencyQ
        (Real.pi / (frequencyP - frequencyQ)) 0‖ ^ 2 = 4 := by
  rw [second_magnus_swap_kernel_norm_sq]
  have hGap : frequencyP - frequencyQ ≠ 0 := sub_ne_zero.mpr hFrequency
  have hArea :
      secondMagnusHalfArea frequencyP frequencyQ
          (Real.pi / (frequencyP - frequencyQ)) 0 = Real.pi / 2 := by
    unfold secondMagnusHalfArea
    field_simp [hGap]
    ring
  rw [hArea, Real.sin_pi_div_two]
  norm_num

/-- At equal frequencies the kernel is identically invisible, while every
nonzero frequency gap has an explicit sample with maximal response. -/
theorem second_magnus_frequency_gap_observability
    (frequencyP frequencyQ : ℝ) :
    frequencyP = frequencyQ ∨
      ‖secondMagnusSwapKernel frequencyP frequencyQ
          (Real.pi / (frequencyP - frequencyQ)) 0‖ ^ 2 = 4 := by
  by_cases hFrequency : frequencyP = frequencyQ
  · exact Or.inl hFrequency
  · exact Or.inr
      (second_magnus_swap_kernel_half_turn_norm_sq
        frequencyP frequencyQ hFrequency)

#print axioms second_magnus_swap_kernel_norm_sq
#print axioms second_magnus_swap_kernel_half_turn_norm_sq
#print axioms second_magnus_frequency_gap_observability

end D5.S3.Observer.AgencyHolonomy.SecondMagnusKernelNormSquare
