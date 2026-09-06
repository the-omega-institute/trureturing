/- GID: D5/S3/Quantum/WeylChronology/GoldenGaussianClosure
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:concrete-Gaussian-closure)
   anchors: []
   digest: Imperfect count compensation produces an exact Gaussian attenuation and a symplectic phase, giving a physical finite-shot error budget. -/

import D5.S3.Quantum.WeylChronology.GaussianDisplacementOverlap
import D5.S3.Quantum.WeylChronology.RamseyResidualOverlap
import D5.S3.Quantum.WeylChronology.GoldenRobustFiniteShot

/-!
# Actual Gaussian endpoint errors in the chronology interferometer

An erroneous compensator D(-X+dx,-Y+dy), applied after D(X,Y), leaves BOTH
D(dx,dy) and the extra phase X*dy-Y*dx. Neglecting that phase and retaining
only a reduced visibility is generally wrong, even for a centered Gaussian.
The concrete Gaussian overlap proved in the companion module gives

  gamma = exp(i*(X*dy-Y*dx)) * exp(-(s*dx^2+dy^2/s)/2).

This is an actual normalized integral, not a supplied overlap. In the existing
RamseyCalibration owner it becomes visibility V*exp(-cost), coupling a*b/2,
phaseOffset X*dy-Y*dx, and closureError=0. That representation is exact for
one fixed acquisition. The nominal-budget bound is

  |V|/2 * (cost + |X*dy-Y*dx|).

The final finite-shot theorem reuses the existing operational Bayes risk. It
concerns each fixed pair of calibrated probability laws, with independent
repetitions. It is not a single minimax test uniformly valid for all unknown
calibrations, nor a model of shot-to-shot correlated drift.

Physical precedent: Fluehmann and Home, PRL 125,043602 (2020), equations (3)
and (5), read Gaussian displacement characteristic functions by internal-state
interference. The additional compensator phase here follows from the already
owned Weyl composition and the explicitly stated control-error model. No new
quantum advantage, Gaussian physics, or experimental realization is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.WeylChronology.GoldenGaussianClosure

open MeasureTheory
open D5.S3.Quantum.WeylChronology.SchrodingerDisplacement
open D5.S3.Quantum.WeylChronology.GaussianDisplacementOverlap
open D5.S3.Quantum.WeylChronology.GoldenWordInterferometry
open D5.S3.Quantum.WeylChronology.RamseyResidualOverlap
open D5.S3.Quantum.WeylChronology.GoldenFiniteShotVisibility
open D5.S3.Quantum.WeylChronology.GoldenRobustCalibration
open D5.S3.Quantum.WeylChronology.GoldenRobustLawSeparation
open D5.S3.Quantum.WeylChronology.GoldenRobustFiniteShot
open D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
open D5.S3.TotalVariation.Bhattacharyya
open D5.S3.TotalVariation.BhattacharyyaVariationMargin

noncomputable section

/-- The extra central phase created by an inaccurate endpoint compensator. -/
def compensationPhase (a b dx dy : ℝ) (word : List Bool) : ℝ :=
  (a * word.count true) * dy - (b * word.count false) * dx

/-- The literal erroneous compensation applied to the already-defined word action. -/
def residualCompensatedWord (a b dx dy : ℝ) (word : List Bool) (f : ℝ → ℂ) : ℝ → ℂ :=
  displacement (-(a * word.count true) + dx) (-(b * word.count false) + dy)
    (runWord a b word f)

/-- The full remaining overlap factor, including the compensator cocycle. -/
def compensationOverlap (s a b dx dy : ℝ) (word : List Bool) : ℂ :=
  Complex.exp ((compensationPhase a b dx dy word : ℂ) * Complex.I) *
    gaussianOverlap s dx dy

/-- The actual normalized wavefunction expectation after erroneous compensation. -/
def compensatedGaussianExpectation (s a b dx dy : ℝ) (word : List Bool) : ℂ :=
  (∫ q : ℝ, star (gaussianSeed s q) *
    residualCompensatedWord a b dx dy word (gaussianSeed s) q) / gaussianMass s

private theorem phase_mul (u v : ℝ) :
    Complex.exp ((u : ℂ) * Complex.I) * Complex.exp ((v : ℂ) * Complex.I) =
      Complex.exp (((u + v : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem phase_norm (u : ℝ) : ‖Complex.exp ((u : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- Exact endpoint-error normal form. The linear-in-error phase is retained. -/
theorem residual_compensated_word_normal_form (a b dx dy : ℝ)
    (word : List Bool) (f : ℝ → ℂ) :
    residualCompensatedWord a b dx dy word f =
      Complex.exp ((((a * b * (magnusCenter word : ℝ) +
        compensationPhase a b dx dy word) : ℝ) : ℂ) * Complex.I) •
        displacement dx dy f := by
  unfold residualCompensatedWord
  rw [run_word_normal_form, displacement_smul, displacement_comp, smul_smul, phase_mul]
  have hx : -(a * (word.count true : ℝ)) + dx + a * (word.count true : ℝ) = dx := by ring
  have hy : -(b * (word.count false : ℝ)) + dy + b * (word.count false : ℝ) = dy := by ring
  have hphase :
      (-(b * (word.count false : ℝ)) + dy) * (a * (word.count true : ℝ)) -
        (-(a * (word.count true : ℝ)) + dx) * (b * (word.count false : ℝ)) =
        compensationPhase a b dx dy word := by
    unfold compensationPhase
    ring
  rw [hx, hy, hphase]

/-- The normalized integral gives the chronology phase times the derived
compensator-overlap factor. No overlap is assumed as input. -/
theorem compensated_gaussian_expectation_factorizes (s a b dx dy : ℝ)
    (word : List Bool) :
    compensatedGaussianExpectation s a b dx dy word =
      Complex.exp (((a * b * (magnusCenter word : ℝ) : ℝ) : ℂ) * Complex.I) *
        compensationOverlap s a b dx dy word := by
  unfold compensatedGaussianExpectation
  rw [residual_compensated_word_normal_form]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hfun :
      (fun q : ℝ => star (gaussianSeed s q) *
        (Complex.exp ((((a * b * (magnusCenter word : ℝ) +
          compensationPhase a b dx dy word) : ℝ) : ℂ) * Complex.I) *
            displacement dx dy (gaussianSeed s) q)) =
      (fun q : ℝ => Complex.exp ((((a * b * (magnusCenter word : ℝ) +
          compensationPhase a b dx dy word) : ℝ) : ℂ) * Complex.I) *
        (star (gaussianSeed s q) * displacement dx dy (gaussianSeed s) q)) := by
    funext q
    ring
  rw [hfun, integral_const_mul, mul_div_assoc]
  change _ * gaussianOverlap s dx dy = _
  rw [compensationOverlap, ← mul_assoc, phase_mul]

/-- The residual factor is exactly a Gaussian attenuation times a geometric phase. -/
theorem compensation_overlap_exact (s a b dx dy : ℝ) (word : List Bool) (hs : 0 < s) :
    compensationOverlap s a b dx dy word =
      Complex.exp ((compensationPhase a b dx dy word : ℂ) * Complex.I) *
        (Real.exp (-displacementCost s dx dy) : ℂ) := by
  rw [compensationOverlap, gaussian_overlap_exact s dx dy hs]

/-- Contractivity is now a consequence of the physical Gaussian construction. -/
theorem compensation_overlap_contracts (s a b dx dy : ℝ) (word : List Bool)
    (hs : 0 < s) : ‖compensationOverlap s a b dx dy word‖ ≤ 1 := by
  rw [compensationOverlap, norm_mul, phase_norm, one_mul]
  exact gaussian_overlap_norm_le_one s dx dy hs

/-- The same physical overlap in the canonical Ramsey readout. Coupling is
ab/2 because this is compensated-word, not word-versus-reversal interference. -/
def gaussianClosureFringe (s a b dx dy visibility : ℝ) (word : List Bool) : ℝ :=
  overlapChronologyFringe visibility (a * b / 2) word
    (compensationOverlap s a b dx dy word)

/-- An exact acquisition record in the existing calibration model. No additive
probability-level residual is required for this Gaussian control-error model. -/
def gaussianClosureCalibration (s a b dx dy visibility : ℝ)
    (word : List Bool) : RamseyCalibration :=
  { baseline := 1 / 2
    visibility := visibility * Real.exp (-displacementCost s dx dy)
    coupling := a * b / 2
    phaseOffset := compensationPhase a b dx dy word
    closureError := 0 }

private theorem overlap_fringe_rotated_real (visibility analyzer phase angle radius : ℝ) :
    overlapRamseyFringe visibility analyzer phase
      (Complex.exp ((angle : ℂ) * Complex.I) * (radius : ℂ)) =
      1 / 2 + (visibility * radius) / 2 * Real.cos (phase + angle - analyzer) := by
  have hprod :
      (Complex.exp ((angle : ℂ) * Complex.I) * (radius : ℂ)) *
        Complex.exp (((phase - analyzer : ℝ) : ℂ) * Complex.I) =
      (radius : ℂ) * Complex.exp (((phase + angle - analyzer : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = (radius : ℂ) * (Complex.exp ((angle : ℂ) * Complex.I) *
          Complex.exp (((phase - analyzer : ℝ) : ℂ) * Complex.I)) := by ring
      _ = _ := by
        rw [phase_mul]
        have he : angle + (phase - analyzer) = phase + angle - analyzer := by ring
        rw [he]
  unfold overlapRamseyFringe
  rw [hprod]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
  ring

/-- Exact visibility and phase-offset interpretation of the derived Gaussian overlap. -/
theorem gaussian_closure_fringe_eq_calibration (s a b dx dy visibility : ℝ)
    (word : List Bool) (hs : 0 < s) :
    gaussianClosureFringe s a b dx dy visibility word =
      robustChronologyFringe (gaussianClosureCalibration s a b dx dy visibility word) word := by
  unfold gaussianClosureFringe overlapChronologyFringe
  rw [compensation_overlap_exact s a b dx dy word hs,
    overlap_fringe_rotated_real, Real.cos_sub_pi_div_two]
  simp [robustChronologyFringe, gaussianClosureCalibration]

/-- Validity of the acquired probability follows from normalized Gaussian overlap. -/
theorem gaussian_closure_fringe_mem_unit (s a b dx dy visibility : ℝ)
    (word : List Bool) (hs : 0 < s) (hv0 : 0 ≤ visibility) (hv1 : visibility ≤ 1) :
    0 ≤ gaussianClosureFringe s a b dx dy visibility word ∧
      gaussianClosureFringe s a b dx dy visibility word ≤ 1 := by
  exact overlap_chronology_fringe_mem_unit visibility (a * b / 2) word
    (compensationOverlap s a b dx dy word) hv0 hv1
    (compensation_overlap_contracts s a b dx dy word hs)

/-- Physical probability-budget bound: quadratic attenuation plus the
compensator's first-order geometric phase. -/
theorem gaussian_closure_budget_le (s a b dx dy visibility : ℝ)
    (word : List Bool) (hs : 0 < s) :
    calibrationDeviationBudget (gaussianClosureCalibration s a b dx dy visibility word)
        visibility (a * b / 2) word ≤
      |visibility| / 2 *
        (displacementCost s dx dy + |compensationPhase a b dx dy word|) := by
  have hcost := displacement_cost_nonneg s dx dy hs
  have he : Real.exp (-displacementCost s dx dy) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr hcost)
  have hb : 1 - Real.exp (-displacementCost s dx dy) ≤ displacementCost s dx dy := by
    linarith [Real.one_sub_le_exp_neg (displacementCost s dx dy)]
  have hmul := mul_le_mul_of_nonneg_left hb (abs_nonneg visibility)
  have habs : |visibility * Real.exp (-displacementCost s dx dy) - visibility| =
      |visibility| * (1 - Real.exp (-displacementCost s dx dy)) := by
    rw [← mul_sub_one, abs_mul, abs_of_nonpos (sub_nonpos.mpr he)]
    ring
  simp only [calibrationDeviationBudget, gaussianClosureCalibration,
    sub_self, abs_zero, zero_add, mul_zero, zero_mul, add_zero]
  rw [habs]
  nlinarith

/-- Physical closure bounds feed the already-owned finite-shot Bayes risk.
The classifier is optimized for each fixed pair of acquired laws. -/
theorem gaussian_closure_finite_shot_bound
    (s a b dxL dyL dxR dyR visibility margin : ℝ)
    (left right : List Bool) (hs : 0 < s)
    (hv0 : 0 ≤ visibility) (hv1 : visibility ≤ 1) (hm0 : 0 ≤ margin)
    (hgap : margin +
        |visibility| / 2 * (displacementCost s dxL dyL +
          |compensationPhase a b dxL dyL left|) +
        |visibility| / 2 * (displacementCost s dxR dyR +
          |compensationPhase a b dxR dyR right|) ≤
      |visibleChronologyFringe visibility (a * b / 2) left -
        visibleChronologyFringe visibility (a * b / 2) right|)
    (shots : ℕ) :
    robustRepeatedOptimalError
        (gaussianClosureCalibration s a b dxL dyL visibility left)
        (gaussianClosureCalibration s a b dxR dyR visibility right)
        left right shots ≤ Real.sqrt (1 - margin ^ 2) ^ shots / 2 := by
  let cl := gaussianClosureCalibration s a b dxL dyL visibility left
  let cr := gaussianClosureCalibration s a b dxR dyR visibility right
  have hl := gaussian_closure_fringe_mem_unit s a b dxL dyL visibility left hs hv0 hv1
  have hr := gaussian_closure_fringe_mem_unit s a b dxR dyR visibility right hs hv0 hv1
  rw [gaussian_closure_fringe_eq_calibration s a b dxL dyL visibility left hs] at hl
  rw [gaussian_closure_fringe_eq_calibration s a b dxR dyR visibility right hs] at hr
  have hbl := gaussian_closure_budget_le s a b dxL dyL visibility left hs
  have hbr := gaussian_closure_budget_le s a b dxR dyR visibility right hs
  have htv := robust_total_variation_lower_bound cl cr visibility (a * b / 2) left right
  have hmTV : margin ≤ D5.S3.TotalVariation.Pinsker.totalVariation
      (robustChronologyLaw cl left) (robustChronologyLaw cr right) := by
    dsimp only [cl, cr] at htv ⊢
    linarith
  have hp := robust_chronology_probability_data cl left hl.1 hl.2
  have hq := robust_chronology_probability_data cr right hr.1 hr.2
  have ha := bhattacharyya_le_sqrt_one_sub_margin_sq
    (robustChronologyLaw cl left) (robustChronologyLaw cr right) hp hq margin hm0 hmTV
  have ha0 : 0 ≤ bhattacharyya (robustChronologyLaw cl left) (robustChronologyLaw cr right) := by
    unfold bhattacharyya
    exact Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)
  have hpow := pow_le_pow_left₀ ha0 ha shots
  have he := robust_repeated_optimal_error_le_bhattacharyya_power
    cl cr left right hl.1 hl.2 hr.1 hr.2 shots
  change robustRepeatedOptimalError cl cr left right shots ≤ _
  linarith

#print axioms residual_compensated_word_normal_form
#print axioms compensated_gaussian_expectation_factorizes
#print axioms compensation_overlap_exact
#print axioms gaussian_closure_fringe_eq_calibration
#print axioms gaussian_closure_budget_le
#print axioms gaussian_closure_finite_shot_bound

end
end D5.S3.Quantum.WeylChronology.GoldenGaussianClosure
