/- GID: D5/S3/Quantum/WeylChronology/RamseyResidualOverlap
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:physical-overlap-interface)
   anchors: []
   digest: A supplied residual motional overlap damps the Ramsey fringe, and its distance from unit overlap certifies the probability-level closure error used by the robust chronology model. -/

import D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
import Mathlib.Analysis.Complex.Norm

/-!
# Ramsey residual-overlap closure interface

A residual motional mismatch after an intended phase-space closure is represented
here by one complex overlap `gamma`. The interference term is multiplied by
`gamma`, so the plus-port population is

`1/2 + V/2 * Re(gamma * exp(i*(phi-theta)))`.

At `gamma = 1` this reduces exactly to the existing contrast-damped ideal Ramsey
fringe. If `norm gamma <= 1` and `0 <= V <= 1`, the result remains a probability.
Most importantly, the deviation from ideal closure is bounded by

`|V|/2 * norm (gamma - 1)`.

The golden chronology specialization inserts the existing phase
`phi = 2*kappa*magnusCenter(word)` and the pi/2 analyzer. The resulting
probability-level closure residual is then used to build an existing
`RamseyCalibration` record, rather than introducing a second robust-noise model.

The physical interface is aligned with trapped-ion phase-space practice. The
2019 trapped-ion Fock-state Ramsey experiment explicitly maps an imperfectly
undone displacement to a residual phase-space displacement detected through
state overlap. Bowers et al., Phys. Rev. Lett. 137, 080602 (2026), demonstrate
geometric phase gates designed to remain robust against motional occupation and
mode-frequency drift. Contemporary Ramsey measurements also model residual
motional-frequency modulation and contrast loss. These sources motivate the
residual-overlap interface; they do not constitute an experiment of the golden
chronology protocol.

This file does not derive `gamma` from the concrete Schrodinger displacement.
That would require an L2/coherent-state reference and an inner-product theorem,
which the current continuous Weyl module intentionally does not yet own. It also
does not identify the finite environment-record overlap model with this
continuous motional overlap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.RamseyResidualOverlap

open D5.S3.Quantum.WeylChronology.RamseyPhaseReadout
open D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
open D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery

noncomputable section

/-- Ramsey plus-port probability with a supplied complex residual overlap
multiplying the coherent interference term. -/
def overlapRamseyFringe
    (visibility analyzerPhase relativePhase : ℝ) (overlap : ℂ) : ℝ :=
  1 / 2 + visibility / 2 *
    (overlap * Complex.exp ((((relativePhase - analyzerPhase : ℝ) : ℂ) *
      Complex.I))).re

private theorem phase_norm_one (phase : ℝ) :
    ‖Complex.exp ((phase : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- Unit residual overlap recovers exactly the affine contrast damping of the
existing ideal Ramsey probability. -/
theorem overlap_ramsey_fringe_unit
    (visibility analyzerPhase relativePhase : ℝ) :
    overlapRamseyFringe visibility analyzerPhase relativePhase 1 =
      (1 - visibility) / 2 +
        visibility * plusProbability analyzerPhase relativePhase := by
  rw [plus_probability_formula]
  simp [overlapRamseyFringe, Complex.exp_ofReal_mul_I_re]
  ring

/-- A contractive residual overlap and physical visibility keep the overlap-
damped Ramsey fringe inside the probability interval. -/
theorem overlap_ramsey_fringe_mem_unit
    (visibility analyzerPhase relativePhase : ℝ) (overlap : ℂ)
    (hvisibility0 : 0 ≤ visibility)
    (hvisibility1 : visibility ≤ 1)
    (hoverlap : ‖overlap‖ ≤ 1) :
    0 ≤ overlapRamseyFringe visibility analyzerPhase relativePhase overlap ∧
      overlapRamseyFringe visibility analyzerPhase relativePhase overlap ≤ 1 := by
  let phase := Complex.exp ((((relativePhase - analyzerPhase : ℝ) : ℂ) * Complex.I))
  have hphase : ‖phase‖ = 1 := by
    dsimp [phase]
    exact phase_norm_one (relativePhase - analyzerPhase)
  have hre : |(overlap * phase).re| ≤ 1 := by
    have hreNorm := Complex.abs_re_le_norm (overlap * phase)
    rw [norm_mul, hphase, mul_one] at hreNorm
    exact hreNorm.trans hoverlap
  have hreBounds : -1 ≤ (overlap * phase).re ∧ (overlap * phase).re ≤ 1 :=
    abs_le.mp hre
  change 0 ≤ 1 / 2 + visibility / 2 * (overlap * phase).re ∧
    1 / 2 + visibility / 2 * (overlap * phase).re ≤ 1
  constructor <;> nlinarith

/-- The probability deviation caused by residual nonclosure is controlled by
the distance of the complex overlap from the unit-overlap reference. -/
theorem overlap_ramsey_fringe_deviation_le
    (visibility analyzerPhase relativePhase : ℝ) (overlap : ℂ) :
    |overlapRamseyFringe visibility analyzerPhase relativePhase overlap -
        overlapRamseyFringe visibility analyzerPhase relativePhase 1| ≤
      |visibility| / 2 * ‖overlap - 1‖ := by
  let phase := Complex.exp ((((relativePhase - analyzerPhase : ℝ) : ℂ) * Complex.I))
  have hphase : ‖phase‖ = 1 := by
    dsimp [phase]
    exact phase_norm_one (relativePhase - analyzerPhase)
  have hdiff :
      overlapRamseyFringe visibility analyzerPhase relativePhase overlap -
          overlapRamseyFringe visibility analyzerPhase relativePhase 1 =
        visibility / 2 * ((overlap - 1) * phase).re := by
    simp [overlapRamseyFringe, phase, Complex.mul_re, Complex.sub_re] <;>
      ring
  rw [hdiff, abs_mul, abs_div]
  norm_num
  have hre := Complex.abs_re_le_norm ((overlap - 1) * phase)
  rw [norm_mul, hphase, mul_one] at hre
  exact mul_le_mul_of_nonneg_left hre (by positivity)

/-- Golden chronology specialization of the residual-overlap Ramsey fringe. -/
def overlapChronologyFringe
    (visibility coupling : ℝ) (word : List Bool) (overlap : ℂ) : ℝ :=
  overlapRamseyFringe visibility (Real.pi / 2)
    (2 * coupling * (magnusCenter word : ℝ)) overlap

/-- Unit overlap in the physical residual-overlap model is exactly the existing
visible chronology fringe. -/
theorem overlap_chronology_fringe_unit
    (visibility coupling : ℝ) (word : List Bool) :
    overlapChronologyFringe visibility coupling word 1 =
      visibleChronologyFringe visibility coupling word := by
  unfold overlapChronologyFringe
  rw [overlap_ramsey_fringe_unit, plus_probability_formula,
    Real.cos_sub_pi_div_two]
  simp [visibleChronologyFringe, visibilitySignal]
  ring

/-- Contractive residual overlap preserves the probability interpretation of
the golden chronology fringe. -/
theorem overlap_chronology_fringe_mem_unit
    (visibility coupling : ℝ) (word : List Bool) (overlap : ℂ)
    (hvisibility0 : 0 ≤ visibility)
    (hvisibility1 : visibility ≤ 1)
    (hoverlap : ‖overlap‖ ≤ 1) :
    0 ≤ overlapChronologyFringe visibility coupling word overlap ∧
      overlapChronologyFringe visibility coupling word overlap ≤ 1 := by
  exact overlap_ramsey_fringe_mem_unit
    visibility (Real.pi / 2)
    (2 * coupling * (magnusCenter word : ℝ)) overlap
    hvisibility0 hvisibility1 hoverlap

/-- Probability-level closure residual induced by a supplied complex motional
overlap. -/
def overlapClosureError
    (visibility coupling : ℝ) (word : List Bool) (overlap : ℂ) : ℝ :=
  overlapChronologyFringe visibility coupling word overlap -
    visibleChronologyFringe visibility coupling word

/-- The robust model's closure residual is certified directly by the complex
overlap defect. -/
theorem overlap_closure_error_le
    (visibility coupling : ℝ) (word : List Bool) (overlap : ℂ) :
    |overlapClosureError visibility coupling word overlap| ≤
      |visibility| / 2 * ‖overlap - 1‖ := by
  unfold overlapClosureError
  rw [← overlap_chronology_fringe_unit]
  exact overlap_ramsey_fringe_deviation_le
    visibility (Real.pi / 2)
    (2 * coupling * (magnusCenter word : ℝ)) overlap

/-- One-acquisition adapter from a supplied residual overlap into the existing
robust calibration record. The calibration is word-specific because the
closure residual is evaluated at that word's physical phase. -/
def overlapCalibration
    (visibility coupling : ℝ) (word : List Bool) (overlap : ℂ) : RamseyCalibration :=
  { baseline := 1 / 2
    visibility := visibility
    coupling := coupling
    phaseOffset := 0
    closureError := overlapClosureError visibility coupling word overlap }

/-- The robust calibration fringe of the overlap-derived acquisition record is
exactly the overlap-damped physical fringe. -/
theorem robust_fringe_overlap_calibration
    (visibility coupling : ℝ) (word : List Bool) (overlap : ℂ) :
    robustChronologyFringe
        (overlapCalibration visibility coupling word overlap) word =
      overlapChronologyFringe visibility coupling word overlap := by
  simp [robustChronologyFringe, overlapCalibration, overlapClosureError,
    visibleChronologyFringe, visibilitySignal] <;>
    ring

/-- With nominal parameters equal to the acquisition visibility and coupling,
the entire existing calibration deviation budget is the derived closure
residual, and is therefore bounded by the residual-overlap defect. -/
theorem overlap_calibration_budget_le
    (visibility coupling : ℝ) (word : List Bool) (overlap : ℂ) :
    calibrationDeviationBudget
        (overlapCalibration visibility coupling word overlap)
        visibility coupling word ≤
      |visibility| / 2 * ‖overlap - 1‖ := by
  have hclosure := overlap_closure_error_le visibility coupling word overlap
  simpa [calibrationDeviationBudget, overlapCalibration] using hclosure

#print axioms overlap_ramsey_fringe_unit
#print axioms overlap_ramsey_fringe_mem_unit
#print axioms overlap_ramsey_fringe_deviation_le
#print axioms overlap_chronology_fringe_unit
#print axioms overlap_chronology_fringe_mem_unit
#print axioms overlap_closure_error_le
#print axioms robust_fringe_overlap_calibration
#print axioms overlap_calibration_budget_le

end
end D5.S3.Quantum.WeylChronology.RamseyResidualOverlap
