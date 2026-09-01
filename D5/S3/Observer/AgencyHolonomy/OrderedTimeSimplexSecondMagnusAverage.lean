/- GID: D5/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage
   generality: G
   mirror-B: D5/B/S3/Observer/AgencyHolonomy/OrderedTimeSimplexSecondMagnusAverage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluate the ordered-simplex average of the second-Magnus kernel exactly. -/

import D5.S3.Observer.AgencyHolonomy.SecondMagnusSwapCurvature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Ordered-time simplex second-Magnus average

The second Magnus term is integrated over the ordered simplex
`0 ≤ time2 ≤ time1 ≤ horizon`. After passing to the time difference
`tau = time1 - time2`, a scalar kernel acquires the triangular weight
`horizon - tau`. This module evaluates the resulting squared Fourier response
exactly.

For a nonzero frequency gap `gap`, the ordered-simplex response is

`horizon^2 - 2 * (1 - cos (gap * horizon)) / gap^2`.

The result supplies a common finite time window for each fixed nonzero gap. It
does not yet take a minimum over a finite frequency family, construct a
Bochner-valued Magnus integral, prove Magnus-series convergence, or compare
the prime-side response with a Weil or zero-side quadratic form.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.AgencyHolonomy.OrderedTimeSimplexSecondMagnusAverage

/-- The triangularly weighted squared response obtained after collapsing the
ordered two-time simplex to the time difference. -/
noncomputable def orderedTimeSimplexKernelAverage
    (gap horizon : ℝ) : ℝ :=
  ∫ tau in (0 : ℝ)..horizon,
    (horizon - tau) *
      (4 * Real.sin (gap * tau / 2) ^ 2)

private theorem four_mul_sin_sq_half (x : ℝ) :
    4 * Real.sin (x / 2) ^ 2 = 2 - 2 * Real.cos x := by
  have hDouble : 2 * (x / 2) = x := by ring
  have hCos := Real.cos_two_mul' (x / 2)
  rw [hDouble] at hCos
  nlinarith [Real.sin_sq_add_cos_sq (x / 2)]

private theorem ordered_time_simplex_primitive_derivative
    (gap horizon x : ℝ) (hGap : gap ≠ 0) :
    HasDerivAt
      (fun y : ℝ =>
        2 * horizon * y - y ^ 2 -
          2 * ((horizon - y) * Real.sin (gap * y)) / gap +
          2 * Real.cos (gap * y) / gap ^ 2)
      ((horizon - x) *
        (4 * Real.sin (gap * x / 2) ^ 2)) x := by
  have hInner : HasDerivAt (fun y : ℝ => gap * y) gap x := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id x).const_mul gap
  have hSinRaw := (Real.hasDerivAt_sin (gap * x)).comp x hInner
  have hSin :
      HasDerivAt (fun y : ℝ => Real.sin (gap * y))
        (gap * Real.cos (gap * x)) x := by
    exact hSinRaw.congr_deriv (by ring)
  have hCosRaw := (Real.hasDerivAt_cos (gap * x)).comp x hInner
  have hCos :
      HasDerivAt (fun y : ℝ => Real.cos (gap * y))
        (-gap * Real.sin (gap * x)) x := by
    exact hCosRaw.congr_deriv (by ring)
  have hLinear :
      HasDerivAt (fun y : ℝ => horizon - y) (-1) x := by
    simpa only [id_eq] using
      (hasDerivAt_id x).const_sub horizon
  have hProductRaw := hLinear.mul hSin
  have hProduct :
      HasDerivAt
        (fun y : ℝ => (horizon - y) * Real.sin (gap * y))
        (-Real.sin (gap * x) +
          (horizon - x) * (gap * Real.cos (gap * x))) x := by
    exact hProductRaw.congr_deriv (by ring)
  have hFirst :
      HasDerivAt (fun y : ℝ => 2 * horizon * y) (2 * horizon) x := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id x).const_mul (2 * horizon)
  have hSquare := hasDerivAt_pow 2 x
  have hRaw :=
    ((hFirst.sub hSquare).sub
      ((hProduct.const_mul 2).div_const gap)).add
        ((hCos.const_mul 2).div_const (gap ^ 2))
  refine (hRaw.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · rfl
  · rw [four_mul_sin_sq_half]
    field_simp [hGap]
    ring

/-- The exact ordered-simplex response for a nonzero frequency gap. -/
theorem ordered_time_simplex_kernel_average_formula
    (gap horizon : ℝ) (hGap : gap ≠ 0) :
    orderedTimeSimplexKernelAverage gap horizon =
      horizon ^ 2 -
        2 * (1 - Real.cos (gap * horizon)) / gap ^ 2 := by
  let primitive := fun y : ℝ =>
    2 * horizon * y - y ^ 2 -
      2 * ((horizon - y) * Real.sin (gap * y)) / gap +
      2 * Real.cos (gap * y) / gap ^ 2
  have hIntegrable :
      IntervalIntegrable
        (fun tau : ℝ =>
          (horizon - tau) *
            (4 * Real.sin (gap * tau / 2) ^ 2))
        MeasureTheory.volume 0 horizon := by
    apply Continuous.intervalIntegrable
    fun_prop
  unfold orderedTimeSimplexKernelAverage
  calc
    (∫ tau in (0 : ℝ)..horizon,
      (horizon - tau) *
        (4 * Real.sin (gap * tau / 2) ^ 2)) =
        primitive horizon - primitive 0 := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro x hx
            exact ordered_time_simplex_primitive_derivative
              gap horizon x hGap
          · exact hIntegrable
    _ = horizon ^ 2 -
        2 * (1 - Real.cos (gap * horizon)) / gap ^ 2 := by
          dsimp only [primitive]
          field_simp [hGap]
          simp
          ring

/-- A zero frequency gap has zero ordered-simplex response. -/
theorem ordered_time_simplex_kernel_average_zero_gap (horizon : ℝ) :
    orderedTimeSimplexKernelAverage 0 horizon = 0 := by
  simp [orderedTimeSimplexKernelAverage]

/-- For a nonnegative horizon the ordered-simplex response is nonnegative. -/
theorem ordered_time_simplex_kernel_average_nonnegative
    (gap horizon : ℝ) (hHorizon : 0 ≤ horizon) :
    0 ≤ orderedTimeSimplexKernelAverage gap horizon := by
  unfold orderedTimeSimplexKernelAverage
  apply intervalIntegral.integral_nonneg hHorizon
  intro tau hTau
  exact mul_nonneg (sub_nonneg.mpr hTau.2) (by positivity)

#print axioms ordered_time_simplex_kernel_average_formula
#print axioms ordered_time_simplex_kernel_average_zero_gap
#print axioms ordered_time_simplex_kernel_average_nonnegative

end D5.S3.Observer.AgencyHolonomy.OrderedTimeSimplexSecondMagnusAverage
