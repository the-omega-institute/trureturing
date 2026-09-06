/- GID: D5/S3/Quantum/WeylChronology/GoldenRobustCalibration
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:deterministic-calibration-envelope)
   anchors: []
   digest: Bounded Ramsey baseline, visibility, coupling, phase and closure errors preserve chronology separation when the nominal fringe gap exceeds the certified perturbation budget. -/

import D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Robust calibration envelope for the golden Ramsey readout

The ideal finite-shot module assumes a calibrated contrast and phase.  This
file adds a deterministic nuisance-parameter envelope before any new
concentration inequality is introduced.  A calibration record contains five
experiment-facing quantities:

* a baseline probability;
* fringe visibility;
* the chronology coupling;
* an additive phase offset;
* an additive probability-level closure/readout residual.

The last coordinate is deliberately coarse.  It is a certified bound on the
net probability perturbation left after imperfect endpoint closure or readout
correction; this module does not claim to derive that scalar from a particular
wavefunction norm or hardware error model.

For a nominal visibility `V0` and coupling `kappa0`, the actual fringe is
compared with the already-owned `visibleChronologyFringe V0 kappa0`.  The proof
uses Mathlib's one-Lipschitz sine theorem.  The exact word-level deviation is
bounded by baseline error, closure error, visibility error and the phase error

`2*(kappa-kappa0)*m + phaseOffset`.

The existing universal word bound `4*abs(m)<=n^2` then removes the hidden center
from the calibration budget.  For two possibly different calibration records,
which permits drift between the two experimental runs, the actual fringe gap
is at least the nominal gap minus the two certified budgets.  Therefore a
strictly positive remaining margin proves robust law separation.

This interface is motivated by current Ramsey practice rather than by an
invented noise taxonomy.  Tomita et al., Nature Communications 17, 4727
(2026), DOI 10.1038/s41467-026-73348-x, report an approximately 80 percent
Ramsey visibility, phase wrapping, two analyzer phases, and the projection-noise
scaling `Delta phi = 1/(V*sqrt N)`.  You et al., Scientific Reports 16, 18474
(2026), DOI 10.1038/s41598-026-49820-5, explicitly fit coherent phase
modulation and heating in spin-echo Ramsey data.  The earlier trapped-ion
exchange experiment, Nature Communications 15 (2024), DOI
10.1038/s41467-024-45232-z, reports fitted Ramsey contrast and binomial
state-population confidence intervals.

No Gaussian drift law, independence of calibration errors, hardware-specific
likelihood, or robust finite-shot optimality theorem is assumed here.  The
output is a deterministic separation certificate that can be composed later
with the repository's existing testing-error machinery.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenRobustCalibration

open D5.S3.Quantum.WeylChronology.GoldenInterferometricRecovery
open D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliSecondOrder
open D5.S3.TotalVariation.Asymptotics.SymmetricBernoulliProbabilityData
open D5.S3.TotalVariation.Metric

noncomputable section

/-- Experiment-facing nuisance coordinates for one Ramsey acquisition. -/
structure RamseyCalibration where
  baseline : ℝ
  visibility : ℝ
  coupling : ℝ
  phaseOffset : ℝ
  closureError : ℝ

/-- The ideal calibration underlying `visibleChronologyFringe`. -/
def idealCalibration (visibility coupling : ℝ) : RamseyCalibration where
  baseline := 1 / 2
  visibility := visibility
  coupling := coupling
  phaseOffset := 0
  closureError := 0

/-- Ramsey fringe with baseline, contrast, coupling, phase and closure/readout
perturbations exposed as explicit coordinates. -/
def robustChronologyFringe
    (calibration : RamseyCalibration) (word : List Bool) : ℝ :=
  calibration.baseline +
    calibration.visibility / 2 *
      Real.sin (2 * calibration.coupling * (magnusCenter word : ℝ) +
        calibration.phaseOffset) +
    calibration.closureError

/-- Canonical Bool law attached to the robust fringe.  Probability validity is
proved separately from a unit-interval premise, rather than hidden in the
definition. -/
def robustChronologyLaw
    (calibration : RamseyCalibration) (word : List Bool) : Bool → ℝ :=
  positiveBiasLaw (robustChronologyFringe calibration word - 1 / 2)

/-- Exact word-level deterministic calibration budget around nominal
`(visibility, coupling)`. -/
def calibrationDeviationBudget
    (calibration : RamseyCalibration)
    (nominalVisibility nominalCoupling : ℝ) (word : List Bool) : ℝ :=
  |calibration.baseline - 1 / 2| + |calibration.closureError| +
    |calibration.visibility - nominalVisibility| / 2 +
    |nominalVisibility| / 2 *
      |2 * (calibration.coupling - nominalCoupling) *
          (magnusCenter word : ℝ) + calibration.phaseOffset|

/-- Length-only version of the calibration budget, using the existing
`4*abs(m)<=n^2` chronology bound. -/
def calibrationLengthBudget
    (calibration : RamseyCalibration)
    (nominalVisibility nominalCoupling : ℝ) (length : ℕ) : ℝ :=
  |calibration.baseline - 1 / 2| + |calibration.closureError| +
    |calibration.visibility - nominalVisibility| / 2 +
    |nominalVisibility| / 2 *
      (|calibration.coupling - nominalCoupling| * (length : ℝ) ^ 2 / 2 +
        |calibration.phaseOffset|)

/-- The robust interface reduces exactly to the preceding ideal visibility
model at the ideal calibration. -/
theorem robust_fringe_ideal_calibration
    (visibility coupling : ℝ) (word : List Bool) :
    robustChronologyFringe (idealCalibration visibility coupling) word =
      visibleChronologyFringe visibility coupling word := by
  unfold robustChronologyFringe idealCalibration visibleChronologyFringe
    visibilitySignal
  ring

private theorem contrast_sine_deviation_le
    (actualVisibility nominalVisibility actualAngle nominalAngle : ℝ) :
    |actualVisibility * Real.sin actualAngle -
        nominalVisibility * Real.sin nominalAngle| ≤
      |actualVisibility - nominalVisibility| +
        |nominalVisibility| * |actualAngle - nominalAngle| := by
  have hdecomp :
      actualVisibility * Real.sin actualAngle -
          nominalVisibility * Real.sin nominalAngle =
        (actualVisibility - nominalVisibility) * Real.sin actualAngle +
          nominalVisibility *
            (Real.sin actualAngle - Real.sin nominalAngle) := by
    ring
  rw [hdecomp]
  calc
    |(actualVisibility - nominalVisibility) * Real.sin actualAngle +
        nominalVisibility * (Real.sin actualAngle - Real.sin nominalAngle)| ≤
        |(actualVisibility - nominalVisibility) * Real.sin actualAngle| +
          |nominalVisibility *
            (Real.sin actualAngle - Real.sin nominalAngle)| := abs_add _ _
    _ = |actualVisibility - nominalVisibility| * |Real.sin actualAngle| +
        |nominalVisibility| *
          |Real.sin actualAngle - Real.sin nominalAngle| := by
          rw [abs_mul, abs_mul]
    _ ≤ |actualVisibility - nominalVisibility| * 1 +
        |nominalVisibility| * |actualAngle - nominalAngle| := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (Real.abs_sin_le_one actualAngle)
          (abs_nonneg (actualVisibility - nominalVisibility)))
        (mul_le_mul_of_nonneg_left
          (Real.abs_sin_sub_sin_le actualAngle nominalAngle)
          (abs_nonneg nominalVisibility))
    _ = |actualVisibility - nominalVisibility| +
        |nominalVisibility| * |actualAngle - nominalAngle| := by ring

/-- Exact deterministic deviation bound from an arbitrary calibration to the
nominal visible chronology fringe. -/
theorem robust_fringe_deviation_le
    (calibration : RamseyCalibration)
    (nominalVisibility nominalCoupling : ℝ) (word : List Bool) :
    |robustChronologyFringe calibration word -
        visibleChronologyFringe nominalVisibility nominalCoupling word| ≤
      calibrationDeviationBudget calibration
        nominalVisibility nominalCoupling word := by
  let actualAngle : ℝ :=
    2 * calibration.coupling * (magnusCenter word : ℝ) +
      calibration.phaseOffset
  let nominalAngle : ℝ :=
    2 * nominalCoupling * (magnusCenter word : ℝ)
  have hangle :
      actualAngle - nominalAngle =
        2 * (calibration.coupling - nominalCoupling) *
          (magnusCenter word : ℝ) + calibration.phaseOffset := by
    dsimp [actualAngle, nominalAngle]
    ring
  have hcontrast := contrast_sine_deviation_le
    calibration.visibility nominalVisibility actualAngle nominalAngle
  rw [hangle] at hcontrast
  have hrewrite :
      robustChronologyFringe calibration word -
          visibleChronologyFringe nominalVisibility nominalCoupling word =
        (calibration.baseline - 1 / 2) + calibration.closureError +
          (calibration.visibility * Real.sin actualAngle -
            nominalVisibility * Real.sin nominalAngle) / 2 := by
    unfold robustChronologyFringe visibleChronologyFringe visibilitySignal
    dsimp [actualAngle, nominalAngle]
    ring
  rw [hrewrite]
  calc
    |(calibration.baseline - 1 / 2) + calibration.closureError +
        (calibration.visibility * Real.sin actualAngle -
          nominalVisibility * Real.sin nominalAngle) / 2| ≤
        |(calibration.baseline - 1 / 2) + calibration.closureError| +
          |(calibration.visibility * Real.sin actualAngle -
            nominalVisibility * Real.sin nominalAngle) / 2| := abs_add _ _
    _ ≤ (|calibration.baseline - 1 / 2| + |calibration.closureError|) +
          |(calibration.visibility * Real.sin actualAngle -
            nominalVisibility * Real.sin nominalAngle) / 2| := by
      gcongr
      exact abs_add _ _
    _ = |calibration.baseline - 1 / 2| + |calibration.closureError| +
          |calibration.visibility * Real.sin actualAngle -
            nominalVisibility * Real.sin nominalAngle| / 2 := by
      rw [abs_div]
      norm_num
    _ ≤ |calibration.baseline - 1 / 2| + |calibration.closureError| +
          (|calibration.visibility - nominalVisibility| +
            |nominalVisibility| *
              |2 * (calibration.coupling - nominalCoupling) *
                (magnusCenter word : ℝ) + calibration.phaseOffset|) / 2 := by
      gcongr
    _ = calibrationDeviationBudget calibration
        nominalVisibility nominalCoupling word := by
      unfold calibrationDeviationBudget
      ring

/-- The word-level calibration budget is controlled by the known window length. -/
theorem calibration_deviation_budget_le_length
    (calibration : RamseyCalibration)
    (nominalVisibility nominalCoupling : ℝ) (word : List Bool) :
    calibrationDeviationBudget calibration
        nominalVisibility nominalCoupling word ≤
      calibrationLengthBudget calibration
        nominalVisibility nominalCoupling word.length := by
  have hcenter := center_length_bound word
  have hscaled :
      2 * |calibration.coupling - nominalCoupling| *
          |(magnusCenter word : ℝ)| ≤
        |calibration.coupling - nominalCoupling| *
          (word.length : ℝ) ^ 2 / 2 := by
    have h := mul_le_mul_of_nonneg_left hcenter
      (div_nonneg (abs_nonneg (calibration.coupling - nominalCoupling))
        (by norm_num : (0 : ℝ) ≤ 2))
    nlinarith
  have hphase :
      |2 * (calibration.coupling - nominalCoupling) *
          (magnusCenter word : ℝ) + calibration.phaseOffset| ≤
        |calibration.coupling - nominalCoupling| *
            (word.length : ℝ) ^ 2 / 2 +
          |calibration.phaseOffset| := by
    calc
      |2 * (calibration.coupling - nominalCoupling) *
          (magnusCenter word : ℝ) + calibration.phaseOffset| ≤
        |2 * (calibration.coupling - nominalCoupling) *
          (magnusCenter word : ℝ)| + |calibration.phaseOffset| := abs_add _ _
      _ = 2 * |calibration.coupling - nominalCoupling| *
          |(magnusCenter word : ℝ)| + |calibration.phaseOffset| := by
        simp [abs_mul]
      _ ≤ |calibration.coupling - nominalCoupling| *
            (word.length : ℝ) ^ 2 / 2 +
          |calibration.phaseOffset| := by
        gcongr
  unfold calibrationDeviationBudget calibrationLengthBudget
  gcongr

/-- Pairwise robust gap bound.  The two words may be measured under different
calibration records, so this also covers bounded run-to-run drift. -/
theorem robust_pair_separation_lower_bound
    (leftCalibration rightCalibration : RamseyCalibration)
    (nominalVisibility nominalCoupling : ℝ)
    (left right : List Bool) :
    |visibleChronologyFringe nominalVisibility nominalCoupling left -
        visibleChronologyFringe nominalVisibility nominalCoupling right| -
        calibrationDeviationBudget leftCalibration
          nominalVisibility nominalCoupling left -
        calibrationDeviationBudget rightCalibration
          nominalVisibility nominalCoupling right ≤
      |robustChronologyFringe leftCalibration left -
        robustChronologyFringe rightCalibration right| := by
  have hleft := robust_fringe_deviation_le
    leftCalibration nominalVisibility nominalCoupling left
  have hright := robust_fringe_deviation_le
    rightCalibration nominalVisibility nominalCoupling right
  have hleft' :
      |visibleChronologyFringe nominalVisibility nominalCoupling left -
          robustChronologyFringe leftCalibration left| ≤
        calibrationDeviationBudget leftCalibration
          nominalVisibility nominalCoupling left := by
    simpa [abs_sub_comm] using hleft
  have htriangle :
      |visibleChronologyFringe nominalVisibility nominalCoupling left -
          visibleChronologyFringe nominalVisibility nominalCoupling right| ≤
        |visibleChronologyFringe nominalVisibility nominalCoupling left -
          robustChronologyFringe leftCalibration left| +
        |robustChronologyFringe leftCalibration left -
          robustChronologyFringe rightCalibration right| +
        |robustChronologyFringe rightCalibration right -
          visibleChronologyFringe nominalVisibility nominalCoupling right| := by
    calc
      |visibleChronologyFringe nominalVisibility nominalCoupling left -
          visibleChronologyFringe nominalVisibility nominalCoupling right| =
        |(visibleChronologyFringe nominalVisibility nominalCoupling left -
            robustChronologyFringe leftCalibration left) +
          (robustChronologyFringe leftCalibration left -
            robustChronologyFringe rightCalibration right) +
          (robustChronologyFringe rightCalibration right -
            visibleChronologyFringe nominalVisibility nominalCoupling right)| := by
          congr 1
          ring
      _ ≤ |visibleChronologyFringe nominalVisibility nominalCoupling left -
            robustChronologyFringe leftCalibration left| +
          |robustChronologyFringe leftCalibration left -
            robustChronologyFringe rightCalibration right| +
          |robustChronologyFringe rightCalibration right -
            visibleChronologyFringe nominalVisibility nominalCoupling right| := by
        calc
          |_ + _ + _| ≤ |_ + _| + |_| := abs_add _ _
          _ ≤ (|_| + |_|) + |_| := by
            gcongr
            exact abs_add _ _