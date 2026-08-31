/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenHawkingTemperatureNormalization
   generality: I
   mirror-B: D5/B/S3/Observer/GoldenPrimeCircle/GoldenHawkingTemperatureNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden data admit distinct Hawking temperatures under distinct time normalizations. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle

/- Library-search audit trail (2026-09-01):
   * The target atom and both chain atoms remain residual-open with no receipt or coverage GID.
     Repository searches for Hawking temperature, Killing time, time normalization, and regulator
     period found no declaration with the target's same-data/different-temperature countermodel.
   * The adjacent frozen owners `GoldenScaleCircle` and `GoldenVerticalSampling` define the golden
     period and angular frequency, but neither represents a physical-time normalization or proves
     temperature nonuniqueness. Their imports add no such result.
   * Pinned Mathlib contains the real-order primitives used below but no Hawking-temperature or
     Killing-time declaration. A NyxID-proxied GitHub/Lean ecosystem search found no exact
     result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenHawkingTemperatureNormalization

open D5.S3.Observer.GoldenPrimeCircle.GoldenScaleCircle

/-- A temperature specification records the visible scale data and the independent conversion
from one affine step to physical Killing time. -/
structure GoldenTemperatureSpecification where
  scalingRate : ℝ
  regulatorPeriod : ℝ
  killingTimePerAffineUnit : ℝ
  killing_time_per_affine_unit_pos : 0 < killingTimePerAffineUnit

/-- The visible data omit the independent Killing-time normalization. -/
def goldenTemperatureData (spec : GoldenTemperatureSpecification) : ℝ × ℝ :=
  (spec.scalingRate, spec.regulatorPeriod)

/-- Converting an affine scaling rate to physical Killing time fixes the surface gravity. -/
def goldenSurfaceGravity (spec : GoldenTemperatureSpecification) : ℝ :=
  spec.scalingRate / spec.killingTimePerAffineUnit

/-- Hawking temperature in natural units is surface gravity divided by `2π`. -/
def goldenHawkingTemperature (spec : GoldenTemperatureSpecification) : ℝ :=
  goldenSurfaceGravity spec / (2 * Real.pi)

/-- The golden scaling rate and regulator period do not determine a unique Hawking temperature:
two positive physical-time normalizations have the same visible golden data and different
temperatures. -/
theorem golden_data_does_not_determine_hawking_temperature :
    ∃ a b : GoldenTemperatureSpecification,
      goldenTemperatureData a = (goldenScalePeriod, goldenScalePeriod) ∧
      goldenTemperatureData a = goldenTemperatureData b ∧
      goldenHawkingTemperature a ≠ goldenHawkingTemperature b := by
  let a : GoldenTemperatureSpecification :=
    { scalingRate := goldenScalePeriod
      regulatorPeriod := goldenScalePeriod
      killingTimePerAffineUnit := 1
      killing_time_per_affine_unit_pos := by norm_num }
  let b : GoldenTemperatureSpecification :=
    { scalingRate := goldenScalePeriod
      regulatorPeriod := goldenScalePeriod
      killingTimePerAffineUnit := 2
      killing_time_per_affine_unit_pos := by norm_num }
  refine ⟨a, b, rfl, rfl, ?_⟩
  apply ne_of_gt
  unfold goldenHawkingTemperature goldenSurfaceGravity
  dsimp [a, b]
  have hTwoPi : 0 < (2 : ℝ) * Real.pi := Real.two_pi_pos
  rw [div_lt_div_iff_of_pos_right hTwoPi]
  nlinarith [golden_scale_period_pos]

#print axioms golden_data_does_not_determine_hawking_temperature

end D5.S3.Observer.GoldenPrimeCircle.GoldenHawkingTemperatureNormalization
