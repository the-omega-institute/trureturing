/- GID: D5/S3/Quantum/WeylChronology/GoldenRobustCalibration
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:deterministic-calibration-envelope)
   anchors: []
   digest: Bounded Ramsey baseline, visibility, coupling, phase and closure errors preserve chronology separation when the nominal gap exceeds the perturbation budget. -/

import D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Robust Ramsey calibration

This is a deterministic nuisance-parameter layer over the existing ideal
finite-shot model.  The five coordinates are baseline, visibility, coupling,
phase offset and a probability-level closure/readout residual.  The residual is
a coarse certified interface; no wavefunction-norm-to-probability conversion is
assumed here.

Mathlib's one-Lipschitz sine theorem gives the perturbation estimate.  The
existing `4*abs(m)<=n^2` theorem then removes the hidden Magnus center from a
length-only budget.  Two words may carry different calibration records, so the
pair theorem permits bounded run-to-run drift.

Experimental motivation is direct: Tomita et al., Nat. Commun. 17, 4727
(2026), DOI 10.1038/s41467-026-73348-x, report imperfect Ramsey visibility,
phase wrapping, two analyzer phases and projection-noise scaling; You et al.,
Sci. Rep. 16, 18474 (2026), DOI 10.1038/s41598-026-49820-5, fit coherent phase
modulation and heating in spin-echo Ramsey data.  No stochastic drift law or
new concentration inequality is introduced in this module.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenRobustCalibration

open D5.S3.Quantum.WeylChronology.GoldenInterferometricRecovery
open D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliProbabilityData

noncomputable section

structure RamseyCalibration where
  baseline : ℝ
  visibility : ℝ
  coupling : ℝ
  phaseOffset : ℝ
  closureError : ℝ

/-- The ideal calibration underlying `visibleChronologyFringe`. -/
def idealCalibration (visibility coupling : ℝ) : RamseyCalibration :=
  ⟨1 / 2, visibility, coupling, 0, 0⟩

/-- Perturbed Ramsey plus-port probability. -/
def robustChronologyFringe
    (cal : RamseyCalibration) (word : List Bool) : ℝ :=
  cal.baseline + cal.visibility / 2 *
    Real.sin (2 * cal.coupling * (magnusCenter word : ℝ) + cal.phaseOffset) +
    cal.closureError

/-- Word-level calibration error around nominal visibility and coupling. -/
def calibrationDeviationBudget
    (cal : RamseyCalibration) (nominalVisibility nominalCoupling : ℝ)
    (word : List Bool) : ℝ :=
  |cal.baseline - 1 / 2| + |cal.closureError| +
    |cal.visibility - nominalVisibility| / 2 +
    |nominalVisibility| / 2 *
      |2 * (cal.coupling - nominalCoupling) * (magnusCenter word : ℝ) +
        cal.phaseOffset|

/-- Length-only calibration error budget. -/
def calibrationLengthBudget
    (cal : RamseyCalibration) (nominalVisibility nominalCoupling : ℝ)
    (n : ℕ) : ℝ :=
  |cal.baseline - 1 / 2| + |cal.closureError| +
    |cal.visibility - nominalVisibility| / 2 +
    |nominalVisibility| / 2 *
      (|cal.coupling - nominalCoupling| * (n : ℝ) ^ 2 / 2 +
        |cal.phaseOffset|)

/-- The robust interface specializes exactly to the ideal visibility model. -/
theorem robust_fringe_ideal_calibration
    (visibility coupling : ℝ) (word : List Bool) :
    robustChronologyFringe (idealCalibration visibility coupling) word =
      visibleChronologyFringe visibility coupling word := by
  simp [robustChronologyFringe, idealCalibration, visibleChronologyFringe,
    visibilitySignal]
  ring

private theorem contrast_sine_deviation_le
    (v v0 angle angle0 : ℝ) :
    |v * Real.sin angle - v0 * Real.sin angle0| ≤
      |v - v0| + |v0| * |angle - angle0| := by
  have hdecomp :
      v * Real.sin angle - v0 * Real.sin angle0 =
        (v - v0) * Real.sin angle + v0 * (Real.sin angle - Real.sin angle0) := by
    ring
  rw [hdecomp]
  calc
    |(v - v0) * Real.sin angle + v0 * (Real.sin angle - Real.sin angle0)| ≤
        |(v - v0) * Real.sin angle| +
          |v0 * (Real.sin angle - Real.sin angle0)| := abs_add _ _
    _ = |v - v0| * |Real.sin angle| +
        |v0| * |Real.sin angle - Real.sin angle0| := by rw [abs_mul, abs_mul]
    _ ≤ |v - v0| * 1 + |v0| * |angle - angle0| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one angle) (abs_nonneg _))
        (mul_le_mul_of_nonneg_left
          (Real.abs_sin_sub_sin_le angle angle0) (abs_nonneg _))
    _ = |v - v0| + |v0| * |angle - angle0| := by ring

/-- Exact deterministic deviation from the nominal fringe. -/
theorem robust_fringe_deviation_le
    (cal : RamseyCalibration) (v0 k0 : ℝ) (word : List Bool) :
    |robustChronologyFringe cal word - visibleChronologyFringe v0 k0 word| ≤
      calibrationDeviationBudget cal v0 k0 word := by
  let angle := 2 * cal.coupling * (magnusCenter word : ℝ) + cal.phaseOffset
  let angle0 := 2 * k0 * (magnusCenter word : ℝ)
  have hcontrast := contrast_sine_deviation_le cal.visibility v0 angle angle0
  have hangle : angle - angle0 =
      2 * (cal.coupling - k0) * (magnusCenter word : ℝ) + cal.phaseOffset := by
    dsimp [angle, angle0]
    ring
  rw [hangle] at hcontrast
  have hre :
      robustChronologyFringe cal word - visibleChronologyFringe v0 k0 word =
        (cal.baseline - 1 / 2) + cal.closureError +
          (cal.visibility * Real.sin angle - v0 * Real.sin angle0) / 2 := by
    simp [robustChronologyFringe, visibleChronologyFringe, visibilitySignal,
      angle, angle0]
    ring
  rw [hre]
  calc
    |(cal.baseline - 1 / 2) + cal.closureError +
        (cal.visibility * Real.sin angle - v0 * Real.sin angle0) / 2| ≤
      |cal.baseline - 1 / 2| + |cal.closureError| +
        |cal.visibility * Real.sin angle - v0 * Real.sin angle0| / 2 := by
      rw [abs_div]
      norm_num
      linarith [abs_add (cal.baseline - 1 / 2) cal.closureError,
        abs_add ((cal.baseline - 1 / 2) + cal.closureError)
          ((cal.visibility * Real.sin angle - v0 * Real.sin angle0) / 2)]
    _ ≤ |cal.baseline - 1 / 2| + |cal.closureError| +
        (|cal.visibility - v0| +
          |v0| * |2 * (cal.coupling - k0) * (magnusCenter word : ℝ) +
            cal.phaseOffset|) / 2 := by
      gcongr
    _ = calibrationDeviationBudget cal v0 k0 word := by
      simp [calibrationDeviationBudget]
      ring

/-- The exact word budget is bounded by a quantity depending only on length. -/
theorem calibration_deviation_budget_le_length
    (cal : RamseyCalibration) (v0 k0 : ℝ) (word : List Bool) :
    calibrationDeviationBudget cal v0 k0 word ≤
      calibrationLengthBudget cal v0 k0 word.length := by
  have hc := center_length_bound word
  have hscaled :
      2 * |cal.coupling - k0| * |(magnusCenter word : ℝ)| ≤
        |cal.coupling - k0| * (word.length : ℝ) ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hc
      (div_nonneg (abs_nonneg (cal.coupling - k0)) (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith
  have hp :
      |2 * (cal.coupling - k0) * (magnusCenter word : ℝ) + cal.phaseOffset| ≤
        |cal.coupling - k0| * (word.length : ℝ) ^ 2 / 2 + |cal.phaseOffset| := by
    calc
      |_ + _| ≤ |2 * (cal.coupling - k0) * (magnusCenter word : ℝ)| +
          |cal.phaseOffset| := abs_add _ _
      _ = 2 * |cal.coupling - k0| * |(magnusCenter word : ℝ)| +
          |cal.phaseOffset| := by simp [abs_mul]
      _ ≤ |cal.coupling - k0| * (word.length : ℝ) ^ 2 / 2 +
          |cal.phaseOffset| := by gcongr
  unfold calibrationDeviationBudget calibrationLengthBudget
  gcongr

/-- Nominal pair gap minus the two calibration budgets is a certified lower
bound for the actual pair gap. -/
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
  have ht :
      |visibleChronologyFringe v0 k0 left - visibleChronologyFringe v0 k0 right| ≤
        |visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left| +
        |robustChronologyFringe leftCal left - robustChronologyFringe rightCal right| +
        |robustChronologyFringe rightCal right - visibleChronologyFringe v0 k0 right| := by
    calc
      |_ - _| = |(visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left) +
          (robustChronologyFringe leftCal left - robustChronologyFringe rightCal right) +
          (robustChronologyFringe rightCal right - visibleChronologyFringe v0 k0 right)| := by
        congr 1
        ring
      _ ≤ |visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left| +
          |robustChronologyFringe leftCal left - robustChronologyFringe rightCal right| +
          |robustChronologyFringe rightCal right - visibleChronologyFringe v0 k0 right| := by
        linarith [abs_add
          (visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left)
          (robustChronologyFringe leftCal left - robustChronologyFringe rightCal right),
          abs_add
            ((visibleChronologyFringe v0 k0 left - robustChronologyFringe leftCal left) +
              (robustChronologyFringe leftCal left - robustChronologyFringe rightCal right))
            (robustChronologyFringe rightCal right - visibleChronologyFringe v0 k0 right)]
  linarith

/-- If the nominal gap strictly exceeds both certified budgets, the actual
fringes remain distinct. -/
theorem robust_fringe_ne_of_nominal_margin
    (leftCal rightCal : RamseyCalibration) (v0 k0 : ℝ)
    (left right : List Bool)
    (hmargin :
      calibrationDeviationBudget leftCal v0 k0 left +
          calibrationDeviationBudget rightCal v0 k0 right <
        |visibleChronologyFringe v0 k0 left - visibleChronologyFringe v0 k0 right|) :
    robustChronologyFringe leftCal left ≠ robustChronologyFringe rightCal right := by
  intro hEq
  have h := robust_pair_separation_lower_bound leftCal rightCal v0 k0 left right
  rw [hEq, sub_self, abs_zero] at h
  linarith

/-- Canonical Bool law for the robust fringe. -/
def robustChronologyLaw (cal : RamseyCalibration) (word : List Bool) : Bool → ℝ :=
  positiveBiasLaw (robustChronologyFringe cal word - 1 / 2)

/-- Unit-interval robust fringes are honest probability data. -/
theorem robust_chronology_probability_data
    (cal : RamseyCalibration) (word : List Bool)
    (h0 : 0 ≤ robustChronologyFringe cal word)
    (h1 : robustChronologyFringe cal word ≤ 1) :
    (∀ b, 0 ≤ robustChronologyLaw cal word b) ∧
      ∑ b, robustChronologyLaw cal word b = 1 := by
  have hbias : |robustChronologyFringe cal word - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith
  simpa [robustChronologyLaw] using (bias_laws_probability_data hbias).1

/-- Equality of robust Bool laws is exactly equality of their plus-port
probabilities. -/
theorem robust_law_eq_iff_fringe_eq
    (leftCal rightCal : RamseyCalibration) (left right : List Bool) :
    robustChronology