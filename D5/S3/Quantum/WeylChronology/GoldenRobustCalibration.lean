/- GID: D5/S3/Quantum/WeylChronology/GoldenRobustCalibration
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:deterministic-calibration-envelope)
   anchors: []
   digest: Bounded Ramsey calibration errors preserve chronology separation when the nominal fringe gap exceeds the certified perturbation budget. -/

import D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Robust Ramsey calibration

This deterministic layer exposes baseline, visibility, coupling, phase offset
and a probability-level closure/readout residual. Mathlib's one-Lipschitz sine
bound gives an exact word-level perturbation budget. Two words may use distinct
calibration records, so the separation theorem permits bounded run-to-run
drift. The closure residual is an interface parameter; no wavefunction norm
conversion is asserted here.

The interface matches current Ramsey practice. Tomita et al., Nat. Commun. 17,
4727 (2026), DOI 10.1038/s41467-026-73348-x, report imperfect visibility,
wrapped phase and projection-noise-limited readout. You et al., Sci. Rep. 16,
18474 (2026), DOI 10.1038/s41598-026-49820-5, fit coherent phase modulation
and heating in spin-echo Ramsey data. No stochastic drift law or new
concentration inequality is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenRobustCalibration

open D5.S3.Quantum.WeylChronology.GoldenInterferometricRecovery
open D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility

noncomputable section

structure RamseyCalibration where
  baseline : ℝ
  visibility : ℝ
  coupling : ℝ
  phaseOffset : ℝ
  closureError : ℝ

/-- Ideal calibration for the preceding visibility model. -/
def idealCalibration (visibility coupling : ℝ) : RamseyCalibration :=
  ⟨1 / 2, visibility, coupling, 0, 0⟩

/-- Perturbed Ramsey plus-port probability. -/
def robustChronologyFringe (cal : RamseyCalibration) (word : List Bool) : ℝ :=
  cal.baseline + cal.visibility / 2 *
    Real.sin (2 * cal.coupling * (magnusCenter word : ℝ) + cal.phaseOffset) +
    cal.closureError

/-- Certified word-level deviation around nominal visibility and coupling. -/
def calibrationDeviationBudget
    (cal : RamseyCalibration) (v0 k0 : ℝ) (word : List Bool) : ℝ :=
  |cal.baseline - 1 / 2| + |cal.closureError| + |cal.visibility - v0| / 2 +
    |v0| / 2 *
      |2 * (cal.coupling - k0) * (magnusCenter word : ℝ) + cal.phaseOffset|

/-- The robust interface specializes to the ideal visibility model. -/
theorem robust_fringe_ideal_calibration
    (visibility coupling : ℝ) (word : List Bool) :
    robustChronologyFringe (idealCalibration visibility coupling) word =
      visibleChronologyFringe visibility coupling word := by
  simp [robustChronologyFringe, idealCalibration, visibleChronologyFringe,
    visibilitySignal]
  ring

private theorem contrast_sine_deviation_le (v v0 angle angle0 : ℝ) :
    |v * Real.sin angle - v0 * Real.sin angle0| ≤
      |v - v0| + |v0| * |angle - angle0| := by
  have h : v * Real.sin angle - v0 * Real.sin angle0 =
      (v - v0) * Real.sin angle + v0 * (Real.sin angle - Real.sin angle0) := by ring
  rw [h]
  calc
    |_ + _| ≤ |(v - v0) * Real.sin angle| +
        |v0 * (Real.sin angle - Real.sin angle0)| := abs_add _ _
    _ = |v - v0| * |Real.sin angle| +
        |v0| * |Real.sin angle - Real.sin angle0| := by rw [abs_mul, abs_mul]
    _ ≤ |v - v0| * 1 + |v0| * |angle - angle0| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one angle) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left
          (Real.abs_sin_sub_sin_le angle angle0) (abs_nonneg _))
    _ = |v - v0| + |v0| * |angle - angle0| := by ring

/-- Deterministic deviation of one actual fringe from its nominal fringe. -/
theorem robust_fringe_deviation_le
    (cal : RamseyCalibration) (v0 k0 : ℝ) (word : List Bool) :
    |robustChronologyFringe cal word - visibleChronologyFringe v0 k0 word| ≤
      calibrationDeviationBudget cal v0 k0 word := by
  let angle := 2 * cal.coupling * (magnusCenter word : ℝ) + cal.phaseOffset
  let angle0 := 2 * k0 * (magnusCenter word : ℝ)
  have hc := contrast_sine_deviation_le cal.visibility v0 angle angle0
  have ha : angle - angle0 =
      2 * (cal.coupling - k0) * (magnusCenter word : ℝ) + cal.phaseOffset := by
    dsimp [angle, angle0]
    ring
  rw [ha] at hc
  have hre : robustChronologyFringe cal word - visibleChronologyFringe v0 k0 word =
      (cal.baseline - 1 / 2) + cal.closureError +
        (cal.visibility * Real.sin angle - v0 * Real.sin angle0) / 2 := by
    simp [robustChronologyFringe, visibleChronologyFringe, visibilitySignal,
      angle, angle0]
    ring
  rw [hre]
  have hsum1 := abs_add (cal.baseline - 1 / 2) cal.closureError
  have hsum2 := abs_add ((cal.baseline - 1 / 2) + cal.closureError)
    ((cal.visibility * Real.sin angle - v0 * Real.sin angle0) / 2)
  rw [abs_div] at hsum2
  norm_num at hsum2
  unfold calibrationDeviationBudget
  nlinarith

/-- Nominal gap minus the two calibration budgets lower-bounds the actual gap. -/
theorem robust_pair_separation_lower_bound
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool) :
    |visibleChronologyFringe v0 k0 left - visibleChronologyFringe v0 k0 right| -
        calibrationDeviationBudget leftCal v0 k0 left -
        calibrationDeviationBudget rightCal v0 k0 right ≤
      |robustChronologyFringe leftCal left - robustChronologyFringe rightCal right| := by
  have hl := robust_fringe_deviation_le leftCal v0 k0 left
  have hr := robust_fringe_deviation_le rightCal v0 k0 right
  have hl' : |visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left| ≤
      calibrationDeviationBudget leftCal v0 k0 left := by
    simpa [abs_sub_comm] using hl
  have h1 := abs_add
    (visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left)
    (robustChronologyFringe leftCal left - robustChronologyFringe rightCal right)
  have h2 := abs_add
    ((visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left) +
      (robustChronologyFringe leftCal left - robustChronologyFringe rightCal right))
    (robustChronologyFringe rightCal right - visibleChronologyFringe v0 k0 right)
  have htel :
      (visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left) +
        (robustChronologyFringe leftCal left - robustChronologyFringe rightCal right) +
        (robustChronologyFringe rightCal right - visibleChronologyFringe v0 k0 right) =
      visibleChronologyFringe v0 k0 left - visibleChronologyFringe v0 k0 right := by ring
  rw [htel] at h2
  linarith

/-- A nominal gap larger than both certified budgets survives every allowed
perturbation in the two supplied calibration records. -/
theorem robust_fringe_ne_of_nominal_margin
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hmargin : calibrationDeviationBudget leftCal v0 k0 left +
        calibrationDeviationBudget rightCal v0 k0 right <
      |visibleChronologyFringe v0 k0 left - visibleChronologyFringe v0 k0 right|) :
    robustChronologyFringe leftCal left ≠ robustChronologyFringe rightCal right := by
  intro hEq
  have h := robust_pair_separation_lower_bound leftCal rightCal v0 k0 left right
  rw [hEq, sub_self, abs_zero] at h
  linarith

#print axioms robust_fringe_ideal_calibration
#print axioms robust_fringe_deviation_le
#print axioms robust_pair_separation_lower_bound
#print axioms robust_fringe_ne_of_nominal_margin

end
end D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
