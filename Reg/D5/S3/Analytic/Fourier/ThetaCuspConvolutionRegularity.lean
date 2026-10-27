import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity
import D5.S3.Zeros.Jensen.OriginalPrimalTailResponse
import Reg.Support.SingleDependentReadout
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open _root_.D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity
open _root_.D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open LeanInformationAudit Real Set MeasureTheory
open private fullJet actual_fullJet_eq_phi_iterated_all from
  D5.S3.Analytic.Fourier.ThetaRadialCurvature
open private tailJet_summable_ray from
  D5.S3.Zeros.Jensen.OriginalPrimalTailProjection
open private jet_one from D5.S3.Zeros.Jensen.OriginalPrimalTailResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity

/-- The source density is the sole varying state; the output keeps its full
function shape so the registered readout can select a pointwise source value. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℝ (fun _ => ℝ → ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ y b => b y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The arena retains the complete source hypotheses and both C2 conclusions.
Only the explicit jump observation is intervened on; every convolution
retains the original density. A nonzero actual cusp charge rejects zero readout. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {a : ℝ} (ha : 0 ≤ a) {b : ℝ → ℝ}
    (hb : Integrable b) (hbc : Continuous b),
    ContDiff ℝ 2 (fun x : ℝ =>
      ∫ y : ℝ, romikPhi (a + |x - y|) * b y) ∧
      ∀ x : ℝ,
        deriv (deriv (fun u : ℝ =>
          ∫ y : ℝ, romikPhi (a + |u - y|) * b y)) x =
            (∫ y : ℝ, iteratedDeriv 2 romikPhi (a + |x - y|) * b y) +
              2 * iteratedDeriv 1 romikPhi a * R.readout () x b

private theorem first_polynomial_negative {z : ℝ} (hz : 6 ≤ z) :
    -8*z^3 + 30*z^2 - 15*z < 0 := by
  have hzpos : 0 < z := by linarith
  have hlin : 0 < 8*z - 30 := by linarith
  have hfac : 0 < z*(8*z - 30) + 15 := by positivity
  have hprod := mul_pos hzpos hfac
  nlinarith

private theorem first_jet_negative_at_log_two (m : ℕ) (hm : 1 ≤ m) :
    primalJet 1 m (Real.log 2 / 2) < 0 := by
  have he : exp (2 * (Real.log 2 / 2)) = 2 := by
    rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmsq : (1 : ℝ) ≤ (m : ℝ)^2 := by nlinarith
  have hscale : Real.pi ≤ modeScale m := by
    dsimp [modeScale]
    simpa using mul_le_mul_of_nonneg_left hmsq Real.pi_pos.le
  have hz : 6 ≤ modeScale m * exp (2 * (Real.log 2 / 2)) := by
    rw [he]
    nlinarith [Real.pi_gt_three]
  have hp : (jetPolynomial 1).eval
      (modeScale m * exp (2 * (Real.log 2 / 2))) < 0 := by
    rw [jet_one]
    exact first_polynomial_negative hz
  exact mul_neg_of_pos_of_neg
    (mul_pos (exp_pos _) (exp_pos _)) hp

private theorem phi_derivative_log_two_negative :
    deriv romikPhi (Real.log 2 / 2) < 0 := by
  have hdelta : 0 < Real.log 2 / 2 :=
    div_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (by norm_num)
  have hs := tailJet_summable_ray 1 1 (by omega) hdelta.le
  have ht : tailJet 1 1 (Real.log 2 / 2) ≤ 0 := by
    have hsum := hs.tsum_le_tsum
      (fun j => (first_jet_negative_at_log_two (1 + j + 1) (by omega)).le)
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
    simpa only [tailJet, tsum_zero] using hsum
  have hfull : fullJet 1 (Real.log 2 / 2) < 0 :=
    add_neg_of_neg_of_nonpos (first_jet_negative_at_log_two 1 (by omega)) ht
  rw [actual_fullJet_eq_phi_iterated_all 1 (Real.log 2 / 2)] at hfull
  simpa only [iteratedDeriv_one] using hfull

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let gauss : ℝ → ℝ := fun x => Real.exp (-x^2)
  have hgauss : Integrable gauss := by
    simpa only [gauss, neg_one_mul, one_mul] using
      (integrable_exp_neg_mul_sq (b := (1 : ℝ)) (by norm_num))
  have hgauss_cont : Continuous gauss := by
    dsimp [gauss]
    fun_prop
  have hh := h (a := Real.log 2 / 2) (b := gauss)
    (by positivity) hgauss hgauss_cont
  have hz := hh.2 0
  have hneg : iteratedDeriv 1 romikPhi (Real.log 2 / 2) < 0 := by
    simpa only [iteratedDeriv_one] using phi_derivative_log_two_negative
  have hx := (actual_phi_shifted_cusp_convolution_C2
    (a := Real.log 2 / 2) (by positivity) hgauss hgauss_cont).2 0
  change deriv (deriv (fun u : ℝ =>
      ∫ y : ℝ, romikPhi (Real.log 2 / 2 + |u - y|) * gauss y)) 0 =
    (∫ y : ℝ, iteratedDeriv 2 romikPhi (Real.log 2 / 2 + |0 - y|) * gauss y) +
      2 * iteratedDeriv 1 romikPhi (Real.log 2 / 2) * 0 at hz
  simp only [mul_zero, add_zero] at hz
  have hval : gauss 0 = 1 := by simp [gauss]
  rw [hval] at hx
  nlinarith [hz, hx]


private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ : ℝ => 0), (fun x : ℝ => Real.exp (-x^2)), ?_⟩
  simp only [actual, realize]
  norm_num

def evidence : Registration arena
    (type_of% @actual_phi_shifted_cusp_convolution_C2) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_phi_shifted_cusp_convolution_C2, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_phi_shifted_cusp_convolution_C2)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity.cuspUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ y b => b y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity
