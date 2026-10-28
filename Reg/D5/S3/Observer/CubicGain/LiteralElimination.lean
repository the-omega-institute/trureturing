import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.LiteralElimination
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000
noncomputable section

namespace Reg.D5.S3.Observer.CubicGain.LiteralElimination

open Polynomial
open _root_.D5.S3.Observer.CubicGain.SelectedRootCommonZero
open _root_.D5.S3.Observer.CubicGain.LiteralElimination
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℝ (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ t b => 45*sourceD t b*(sourceE2 b).eval (t*b))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ t b => 45*sourceD t b*(sourceE2 b).eval (t*b)+1)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ t b : ℝ, R.readout () t b =
    b^7*(sourceBt 1 t b*sourceBb 2 t b-sourceBb 1 t b*sourceBt 2 t b)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h 0 0
  norm_num [rejected,realize,sourceD,sourceN,sourceJ] at hz

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0,0,1,?_⟩
  norm_num [actual,realize,sourceE2,sourceD,sourceN,sourceJ,
    eval_add,eval_mul,eval_pow,eval_C,eval_X]

def source_registration :
    Registration arena (type_of% @source_e2_normalization) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨source_e2_normalization,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@source_e2_normalization) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.LiteralElimination.source_e2_normalization.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.LiteralElimination.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ t b => 45*sourceD t b*(sourceE2 b).eval (t*b)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.LiteralElimination
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Observer.CubicGain.LiteralElimination
