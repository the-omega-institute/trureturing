/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenPrimeCircle/GoldenVerticalSampling
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fourier frequency on the golden scale circle equals vertical Mellin frequency on logarithmic scale. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle

/-!
This owner closes the exact algebraic bridge between the golden shell phase and
vertical Mellin sampling.  The infinite Euler-product logarithmic derivative
identity remains an analytic theorem with convergence hypotheses and is not
asserted here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenVerticalSampling

open scoped goldenRatio
open D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle

/-- Fundamental angular frequency of the golden scale circle. -/
def goldenAngularFrequency : ℝ :=
  Real.pi / Real.log Real.goldenRatio

/-- The fundamental golden angular frequency is positive. -/
theorem golden_angular_frequency_pos : 0 < goldenAngularFrequency := by
  unfold goldenAngularFrequency
  exact div_pos Real.pi_pos (Real.log_pos Real.one_lt_goldenRatio)

/-- The Fourier phase of shell coordinate `log x / (2 log phi)` is exactly the
Mellin vertical frequency `k pi / log phi` paired with `log x`. -/
theorem golden_phase_vertical_frequency_identity
    (x : ℝ) (k : ℤ) :
    2 * Real.pi * (k : ℝ) * goldenScaleCoordinate x =
      ((k : ℝ) * goldenAngularFrequency) * Real.log x := by
  unfold goldenScaleCoordinate goldenScalePeriod goldenAngularFrequency
  have hLog : Real.log Real.goldenRatio ≠ 0 :=
    ne_of_gt (Real.log_pos Real.one_lt_goldenRatio)
  field_simp [hLog]
  ring

/-- Adjacent Fourier modes are separated by one fundamental golden frequency. -/
theorem golden_vertical_mode_spacing (k : ℤ) :
    (((k + 1 : ℤ) : ℝ) * goldenAngularFrequency) -
      ((k : ℝ) * goldenAngularFrequency) = goldenAngularFrequency := by
  push_cast
  ring

/-- The zero Fourier mode is the uncharged scale-average mode. -/
@[simp]
theorem golden_vertical_zero_mode :
    ((0 : ℝ) * goldenAngularFrequency) = 0 := by
  ring

#print axioms golden_angular_frequency_pos
#print axioms golden_phase_vertical_frequency_identity
#print axioms golden_vertical_mode_spacing

end D5.S3.Observer.GoldenPrimeCircle.GoldenVerticalSampling
