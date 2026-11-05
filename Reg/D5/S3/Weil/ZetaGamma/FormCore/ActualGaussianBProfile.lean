import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile
import Reg.Support.SingleDependentReadout

/-! The complete original source telescope is retained. Only the terminal
actual even-B readout is intervened on. Actual theta-profile integrability
and every translated weighted-tail domain remain unchanged. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile
open _root_.D5.S3.Weil.ZetaGamma.FormCore.ActualSuzukiDomainCounterexample
open _root_.D5.S3.Weil.ZetaGamma.FormCore.RightExponentialTail
open _root_.D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open _root_.D5.S3.Zeros.Jensen.SourceThetaMomentBounds
open _root_.D5.S3.Zeros.Jensen.NormalizedJensenDegreeLowering
open LeanInformationAudit MeasureTheory Real Set

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℝ (fun _ => ℝ → ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ r F => actualSuzukiEvenBProfile F r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {a : ℝ}, 0 ≤ a →
    Integrable (actualGammaProfile (fun x : ℝ =>
      (exp ((9 / 2 : ℝ) * a - exp (2 * a) * x) : ℂ))) ∧
    (∀ t : ℝ, 0 ≤ t →
      IntegrableOn (fun s : ℝ => (exp (-(5 / 4 : ℝ) * s) : ℂ) *
        actualGammaProfile (fun x : ℝ =>
          (exp ((9 / 2 : ℝ) * a - exp (2 * a) * x) : ℂ)) (t + s)) (Ioi 0)) ∧
    ∀ r : ℝ, R.readout () r (fun x : ℝ =>
        (exp ((9 / 2 : ℝ) * a - exp (2 * a) * x) : ℂ)) =
      (((Real.pi ^ (1 / 4 : ℝ) / 4) * romikPhi (a + |r|) : ℝ) : ℂ)

private theorem target_zero_ne :
    (((Real.pi ^ (1 / 4 : ℝ) / 4) * romikPhi 0 : ℝ) : ℂ) ≠ 0 := by
  have hphi : 0 < romikPhi 0 := by
    rw [romikPhi_eq_source]
    exact (source_theta_gaussian_bound 0).1
  apply Complex.ofReal_ne_zero.mpr
  exact (mul_pos (by positivity) hphi).ne'

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := (h (a := 0) (by norm_num)).2.2 0
  change (0 : ℂ) = (((Real.pi ^ (1 / 4 : ℝ) / 4) * romikPhi (0 + |0|) : ℝ) : ℂ) at hz
  simp only [abs_zero, zero_add] at hz
  exact target_zero_ne hz.symm

private theorem zero_evenB (r : ℝ) :
    actualSuzukiEvenBProfile (fun _ : ℝ => (0 : ℂ)) r = 0 := by
  simp [actualSuzukiEvenBProfile, actualSuzukiBProfile, actualGammaProfile,
    fullTheta, physicalTerm, rightExponentialTail]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, (fun _ : ℝ => (0 : ℂ)),
    (fun x : ℝ => (exp ((9 / 2 : ℝ) * 0 - exp (2 * 0) * x) : ℂ)), ?_⟩
  change actualSuzukiEvenBProfile (fun _ : ℝ => (0 : ℂ)) 0 ≠
    actualSuzukiEvenBProfile
      (fun x : ℝ => (exp ((9 / 2 : ℝ) * 0 - exp (2 * 0) * x) : ℂ)) 0
  rw [zero_evenB, (actual_gaussian_suzuki_evenB (a := 0) (by norm_num)).2.2 0]
  simpa only [abs_zero, zero_add] using target_zero_ne.symm

def evidence : Registration arena (type_of% @actual_gaussian_suzuki_evenB) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_gaussian_suzuki_evenB, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_gaussian_suzuki_evenB) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile.unit
  realizationName := `Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ r F => actualSuzukiEvenBProfile F r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.ZetaGamma.FormCore.ActualGaussianBProfile
