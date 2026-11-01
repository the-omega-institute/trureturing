import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedWords
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the actual level-zero word observation. -/

set_option autoImplicit false

namespace Reg.D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedWords.WordZero

open _root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Bool) (fun _ => List Bool)

def actual : Realization signature :=
  realize signature (fun _ _ a => balancedWord 0 a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => []) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : Bool, R.readout () () a = [a]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh : ([] : List Bool) = [false] := h false
  cases hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), false, true, ?_⟩
  change balancedWord 0 false ≠ balancedWord 0 true
  decide

def family : Registration arena
    (type_of% (@_root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced.balancedWord_zero)) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced.balancedWord_zero, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := dependence

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced.balancedWord_zero)
    (type_of% actual) Unit Unit where
  unitName := `D5.S1.Dynamics.Symbolic.PermutativeLifts.Balanced.balancedWord_zero.__information_unit
  realizationName :=
    `Reg.D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedWords.WordZero.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a => balancedWord 0 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedWords
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family

end Reg.D5.S1.Dynamics.Symbolic.PermutativeLifts.BalancedWords.WordZero
