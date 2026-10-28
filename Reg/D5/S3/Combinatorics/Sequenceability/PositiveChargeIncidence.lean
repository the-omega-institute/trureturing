import D5.S3.Combinatorics.Sequenceability.PositiveChargeIncidence
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent
open _root_.D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.PositiveChargeGeometry
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace Reg.D5.S3.Combinatorics.Sequenceability.PositiveChargeGeometry
universe u
abbrev signature : Signature where
  Params := Σ X : Type u, DecidableEq X
  State p := Finset p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p S => @row p.1 p.2 S) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type u} [DecidableEq X] {M : Submodule ℤ (X → ℤ)}
    (S : Finset X), (∑ x ∈ S, quotientLabel M x) = 0 ↔
      R.readout () ⟨X,inferInstance⟩ S ∈ M

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let a : ULift.{u} Unit := ⟨()⟩
  have hz := (h (M := (⊥ : Submodule ℤ (ULift.{u} Unit → ℤ))) {a}).mpr
    (by simp [rejected,realize])
  have hm := (quotient_zero_iff (M := (⊥ : Submodule ℤ (ULift.{u} Unit → ℤ))) {a}).mp hz
  have he : row ({a} : Finset (ULift.{u} Unit)) = 0 := by simpa using hm
  have he' := congrFun he a
  simpa [row] using he'

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let a : ULift.{u} Unit := ⟨()⟩
  refine ⟨⟨ULift.{u} Unit,inferInstance⟩,∅,{a},?_⟩
  intro he
  have hx := congrFun he a
  simpa [actual,realize,row] using hx

def quotient_family : Registration arena.{u} (type_of% (@quotient_zero_iff.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@quotient_zero_iff.{u},rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def quotient_audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quotient_zero_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Sequenceability.PrivatePairBooleanDescent.PositiveChargeGeometry.quotient_zero_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Sequenceability.PositiveChargeGeometry.quotient_family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨quotient_family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p S => @row p.1 p.2 S) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Sequenceability.PositiveChargeIncidence
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","arg","arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Reg.D5.S3.Combinatorics.Sequenceability.PositiveChargeGeometry
