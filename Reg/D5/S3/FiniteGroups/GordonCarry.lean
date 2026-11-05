import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.GordonCarry
import Reg.Support.DependentFamily

/-! Source-specific predecessor-carry readout and whole-family intervention. -/

namespace Reg.D5.S3.FiniteGroups.GordonCarry

open _root_.D5.S3.FiniteGroups.Gordon
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature where
  Params := List OddRadix
  State := Box
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := Box
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ ds x => carry ds x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private def three : OddRadix := ⟨3, by decide, by decide⟩

private theorem rejected_injective : ¬ (∀ ds, Function.Injective (rejected.readout () ds)) := by
  intro h
  have he := h [three] (a₁ := ((0 : ZMod 3), PUnit.unit))
    (a₂ := ((1 : ZMod 3), PUnit.unit)) rfl
  exact (by decide : (0 : ZMod 3) ≠ 1) (congrArg Prod.fst he)

private theorem rejected_zero : ¬ (∀ ds x, rejected.readout () ds x = 0 ↔ x = 0) := by
  intro h
  have he := (h [three] ((1 : ZMod 3), PUnit.unit)).mp rfl
  exact (by decide : (1 : ZMod 3) ≠ 0) (congrArg Prod.fst he)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨[three], ((0 : ZMod 3), PUnit.unit), ((1 : ZMod 3), PUnit.unit), ?_⟩
  intro he
  have hh := carry_injective [three] he
  exact (by decide : (0 : ZMod 3) ≠ 1) (congrArg Prod.fst hh)

def injectiveArena : Arena where
  signature := signature
  Law R := ∀ ds, Function.Injective (R.readout () ds)

def zeroArena : Arena where
  signature := signature
  Law R := ∀ ds x, R.readout () ds x = 0 ↔ x = 0

def injectiveSource : Registration injectiveArena (type_of% (@carry_injective)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨carry_injective, rejected, rejected_injective⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_injective⟩
      intro j hj
      have hji : j = i := by
        exact @Subsingleton.elim Unit (inferInstance : Subsingleton Unit) j i
      exact (hj hji).elim
    · intro e
      exact nomatch e
  dependence := dependence

def zeroSource : Registration zeroArena (type_of% (@carry_eq_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨carry_eq_zero, rejected, rejected_zero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_zero⟩
      intro j hj
      have hji : j = i := by
        exact @Subsingleton.elim Unit (inferInstance : Subsingleton Unit) j i
      exact (hj hji).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def injectiveRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@carry_injective) (Realization signature) (List OddRadix → Type) Unit := {
  unitName := `D5.S3.FiniteGroups.GordonCarry.carry_injective.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GordonCarry.injectiveSource
  realizationSource := none
  generated := false
  arena := .source ⟨injectiveArena⟩
  objectArena := .source ⟨injectiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source injectiveArena ⟨injectiveSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ds x => carry ds x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GordonCarry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

noncomputable def zeroRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@carry_eq_zero) (Realization signature) (List OddRadix → Type) Unit := {
  unitName := `D5.S3.FiniteGroups.GordonCarry.carry_eq_zero.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.GordonCarry.zeroSource
  realizationSource := none
  generated := false
  arena := .source ⟨zeroArena⟩
  objectArena := .source ⟨zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source zeroArena ⟨zeroSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ ds x => carry ds x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.GordonCarry
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.FiniteGroups.GordonCarry
