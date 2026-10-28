import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Fourier.ThetaCuspApproximation
import Reg.Support.SingleDependentReadout

/-! The original WeilTestFunction state carrier is retained. Only its
   pointwise observation in the weighted L1 clause is intervened on; the
   zeroth/second jet budget and common envelope retain their original form.

   The raw selection targets DFunLike.coe (g_n) x, whose state operand is
   under fn/arg. Ancestor binders are C, a, ha, n, x, so x has ordinal 4.
   The existential C precedes the complete nonnegative shift family. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Analytic.Fourier.ThetaCuspApproximation

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Fourier.ThetaCuspApproximation
open _root_.D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open _root_.D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open _root_.D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open _root_.D5.S3.Weil.TestFunctions
open _root_.D5.S3.Weil.TestFunctions.FourierLaplaceClosedStripDecay
open LeanInformationAudit MeasureTheory Real Filter
open scoped Topology

open private exponential_half_integrable target_bound cPhi from
  D5.S3.Analytic.Fourier.ThetaCuspApproximation
open private fullConstant from
  D5.S3.Analytic.Fourier.ThetaCuspConvolutionRegularity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℝ (fun _ => WeilTestFunction) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ x g => g x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : ℝ, 0 ≤ a →
      (∀ n : ℕ, closedStripJetBudget (gaussianCuspApproximation a n) (1/2) ≤ C) ∧
      Tendsto (fun n => ∫ x : ℝ, exp (|x|/2) *
        ‖R.readout () x (gaussianCuspApproximation a n) -
          ((((Real.pi^(1/4 : ℝ)/4) * romikPhi (a+|x|) : ℝ) : ℂ))‖)
        atTop (𝓝 0) ∧
      (∀ n : ℕ, ∀ x : ℝ,
        ‖gaussianCuspApproximation a n x‖ ≤ C * exp (-|x|))

private def targetMass : ℝ :=
  ∫ x : ℝ, exp (|x|/2) * ‖(((cPhi * romikPhi |x| : ℝ) : ℂ))‖

private theorem targetMass_pos : 0 < targetMass := by
  have hphi : Continuous romikPhi := by
    have heq : romikPhi = sourceThetaKernel := funext romikPhi_eq_source
    rw [heq]
    exact source_theta_continuous
  have hc : 0 < cPhi := by
    dsimp only [cPhi]
    exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (by norm_num)
  have hphi0 : 0 < romikPhi 0 := by
    rw [romikPhi_eq_source]
    exact (source_theta_gaussian_bound 0).1
  have hcont : Continuous (fun x : ℝ =>
      exp (|x|/2) * ‖(((cPhi * romikPhi |x| : ℝ) : ℂ))‖) :=
    (by fun_prop : Continuous (fun x : ℝ => exp (|x|/2))).mul
      ((Complex.continuous_ofReal.comp
        (continuous_const.mul (hphi.comp continuous_abs))).norm)
  have hi : Integrable (fun x : ℝ =>
      exp (|x|/2) * ‖(((cPhi * romikPhi |x| : ℝ) : ℂ))‖) := by
    apply (exponential_half_integrable.const_mul (|cPhi| * fullConstant 0)).mono'
      hcont.aestronglyMeasurable
    apply Eventually.of_forall
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hb := target_bound (a := (0 : ℝ)) (by norm_num) x
    simp only [zero_add] at hb
    calc
      _ ≤ exp (|x|/2) * ((|cPhi| * fullConstant 0)*exp (-|x|)) :=
        mul_le_mul_of_nonneg_left hb (exp_pos _).le
      _ = _ := by
        rw [show exp (|x|/2) * ((|cPhi| * fullConstant 0)*exp (-|x|)) =
            (|cPhi| * fullConstant 0)*(exp (|x|/2)*exp (-|x|)) by ring,
          ← exp_add]
        congr 2
        ring
  apply integral_pos_of_integrable_nonneg_nonzero hcont hi (fun _ => by positivity)
    (x := (0 : ℝ))
  have hprod : cPhi * romikPhi 0 ≠ 0 := (mul_pos hc hphi0).ne'
  have hnorm : ‖((cPhi * romikPhi 0 : ℝ) : ℂ)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Complex.ofReal_ne_zero.mpr hprod)
  simpa only [abs_zero, zero_div, exp_zero, one_mul] using hnorm

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨C, hC, hall⟩ := h
  obtain ⟨hbudget, hlim, henvelope⟩ := hall (0 : ℝ) (by norm_num)
  have hlim' : Tendsto (fun _ : ℕ => targetMass) atTop (𝓝 (0 : ℝ)) := by
    simpa only [rejected, realize, zero_sub, norm_neg, zero_add, targetMass, cPhi] using hlim
  have hz : targetMass = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => targetMass) atTop (𝓝 targetMass)) hlim'
  exact targetMass_pos.ne' hz

private def zeroTest : WeilTestFunction where
  toFun _ := 0
  contDiff' := contDiff_const
  hasCompactSupport' := HasCompactSupport.zero
  even' _ := rfl

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, zeroTest, standardTestFunction, ?_⟩
  change (0 : ℂ) ≠ standardTestFunction 0
  rw [standardTestFunction_zero]
  norm_num

def evidence : Registration arena
    (type_of% @actual_gaussian_cusp_compact_approximation) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_gaussian_cusp_compact_approximation, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_gaussian_cusp_compact_approximation)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.ThetaCuspApproximation.approximationUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.ThetaCuspApproximation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x g => g x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.ThetaCuspApproximation
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "arg", "fn", "arg",
        "fn", "fn", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Analytic.Fourier.ThetaCuspApproximation
