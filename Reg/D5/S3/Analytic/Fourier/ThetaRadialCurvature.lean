import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Analytic.Fourier.ThetaRadialCurvature
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Analytic.Fourier.ThetaDifferentialKernel
open _root_.D5.S3.Analytic.Fourier.ThetaRadialCurvature
open LeanInformationAudit Real Set
open private actual_fullJet_eq_phi_iterated_all actual_fullJet_odd_origin from
  D5.S3.Analytic.Fourier.ThetaRadialCurvature

noncomputable section
namespace Reg.D5.S3.Analytic.Fourier.ThetaRadialCurvature

/-- The original radial-curvature scalar is observed as a whole. -/
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x =>
    x * ((iteratedDeriv 1 romikPhi x) ^ 2 -
      romikPhi x * iteratedDeriv 2 romikPhi x) +
        romikPhi x * iteratedDeriv 1 romikPhi x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Both original conclusions and every binder are retained. The intervention
    changes only the selected scalar observation in the first conclusion. -/
def arena : Arena where
  signature := signature
  Law R :=
    (∀ x : ℝ, 0 < x → 0 < R.readout () () x) ∧
    StrictConcaveOn ℝ (Ioi (0 : ℝ))
      (fun r : ℝ => Real.log (romikPhi (Real.sqrt r)))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hn := h.1 1 (by norm_num)
  change (0 : ℝ) < 0 at hn
  exact (lt_irrefl 0) hn

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have hzero : iteratedDeriv 1 romikPhi 0 = 0 := by
    rw [← actual_fullJet_eq_phi_iterated_all 1 0]
    exact actual_fullJet_odd_origin.1
  have hp := actual_phi_radial_curvature_and_square_concavity.1 1 (by norm_num)
  simpa only [actual, realize, zero_mul, zero_add, hzero, mul_zero] using ne_of_lt hp

def evidence : Registration arena
    (type_of% @actual_phi_radial_curvature_and_square_concavity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_phi_radial_curvature_and_square_concavity, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def registration_1 : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@actual_phi_radial_curvature_and_square_concavity)
    (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Analytic.Fourier.ThetaRadialCurvature.radialUnit
  realizationName := `Reg.D5.S3.Analytic.Fourier.ThetaRadialCurvature.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x =>
    x * ((iteratedDeriv 1 romikPhi x) ^ 2 -
      romikPhi x * iteratedDeriv 2 romikPhi x) +
        romikPhi x * iteratedDeriv 1 romikPhi x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Fourier.ThetaRadialCurvature
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end Reg.D5.S3.Analytic.Fourier.ThetaRadialCurvature
