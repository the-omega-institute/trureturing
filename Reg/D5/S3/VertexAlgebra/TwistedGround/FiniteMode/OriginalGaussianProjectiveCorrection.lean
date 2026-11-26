import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection
import Reg.Support.SingleDependentReadout

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open scoped Topology

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection
open _root_.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianFiniteCandidateModes (k)
open _root_.D5.S3.Analytic.OriginalHalfBinomialWronskian (tau)
open _root_.D5.S3.Analytic.AbelRatioSchwarzian (preSchwarzian)

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ z => -z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z => -z + 1) (fun e => nomatch e)

/-- The complete original telescope and all conclusions; only the selected
native observation is varied. -/
def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℂ) (hr : ‖r‖ < 1) (hc : ‖1 - r‖ < 1) ,
    preSchwarzian tau r = R.readout () () (1 - 2 * r + 2 * k r) / (r * (1 - r)) ∧
      k r = (2 * r - 1) / 2 - r * (1 - r) * preSchwarzian tau r / 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (1 / 2) (by norm_num) (by norm_num)).1
  have ha := (original_correction_projective (r := 1 / 2) (by norm_num) (by norm_num)).1
  change preSchwarzian tau (1 / 2) =
    (-(1 - 2 * (1 / 2) + 2 * k (1 / 2)) + 1) / ((1 / 2) * (1 - 1 / 2)) at hh
  norm_num at hh ha
  have he : (4 : ℂ) = 0 := by linear_combination ha - hh
  norm_num at he


private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% @original_correction_projective) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by
    intro r hr hc
    exact original_correction_projective hr hc,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_correction_projective) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => -z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.VertexAlgebra.TwistedGround.FiniteMode.OriginalGaussianProjectiveCorrection
