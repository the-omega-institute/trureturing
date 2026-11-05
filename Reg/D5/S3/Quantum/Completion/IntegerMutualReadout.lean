import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Completion.IntegerMutualReadout
import Reg.Support.UniverseSingleReadout

/-! The complete source telescope, with the original kernel observed in the integer budget. -/

namespace Reg.D5.S3.Quantum.Completion.IntegerMutualReadout

open _root_.D5.S3.Quantum.Completion.IntegerMutualReadout
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

abbrev signature : Signature :=
  Reg.Support.UniverseSingleReadout.signature (Type u)
    (fun X => X → X → ℂ) (fun X => X → X → ℂ)

def actual : Realization signature.{u} :=
  realize signature (fun _ _ K => K) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} (K : X → X → ℂ),
    (Budget (fun z : GaussianInt => (z : ℂ)) (R.readout () X K) ↔ (Matrix.of K).PosSemidef) ∧
    (Budget rationalComplex K ↔ (Matrix.of K).PosSemidef) ∧
    (Budget id K ↔ (Matrix.of K).PosSemidef)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let X := ULift.{u} Unit
  let K : X → X → ℂ := fun _ _ => -1
  have hz : Budget (fun z : GaussianInt => (z : ℂ)) (fun _ _ : X => 0) :=
    (mutual_budget_iff_positive_type _).1.mpr Matrix.PosSemidef.zero
  have hp : (Matrix.of K).PosSemidef := (h K).1.mp hz
  have hneg := hp.diag_nonneg (i := ⟨()⟩)
  norm_num [K] at hneg

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h ⟨()⟩) ⟨()⟩
  exact zero_ne_one he

def source_registration : Registration arena.{u}
    (type_of% @mutual_budget_iff_positive_type.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mutual_budget_iff_positive_type, rejected, rejected_law⟩
  sensitivity := Reg.Support.UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@mutual_budget_iff_positive_type.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.Quantum.Completion.IntegerMutualReadout.mutual_budget_iff_positive_type.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Completion.IntegerMutualReadout.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ K => K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Completion.IntegerMutualReadout
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.Completion.IntegerMutualReadout
