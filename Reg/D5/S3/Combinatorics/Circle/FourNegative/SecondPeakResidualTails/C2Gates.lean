import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Gates
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails

namespace Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Gates
namespace c2_scalar_drops

abbrev signature : Signature where
  Params := ℤ × Fin 4
  State _ := ℤ
  Role := Fin 4
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun role p h => if role = 0 ∨ role = 2 then c2OldDrop h p.1 p.2
      else c2NewDrop h p.1 p.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h t : ℤ) (r : Fin 4),
    2*R.readout 0 (t,r) h = c2OldSuccessor h t r-c2N h t ∧
    2*R.readout 1 (t,r) h = c2NewSuccessor h t r-c2Q h t ∧
    (c2OldSuccessor h t r-c2N h t)/2 = R.readout 2 (t,r) h ∧
    (c2NewSuccessor h t r-c2Q h t)/2 = R.readout 3 (t,r) h

private theorem actual_law : arena.Law actual := by
  simpa only [arena, actual, realize, Fin.reduceEq, true_or, or_true,
    ite_true, false_or, ite_false] using c2_scalar_drops

private theorem actual_sensitivity : Sensitivity arena actual := by
  constructor
  · intro i
    let bad : Realization signature := realize signature
      (fun j p h => if j = i then 0 else actual.readout j p h)
      (fun e => nomatch e)
    refine ⟨bad, ?_, rfl, ?_⟩
    · intro j hji
      funext p h
      simp [bad, realize, hji]
    · intro hh
      have h := hh 0 0 0
      fin_cases i <;>
        norm_num [bad, actual, realize, c2OldSuccessor, c2NewSuccessor,
          c2N, c2Q, c2OldHead, c2NewHead] at h
  · intro e
    exact nomatch e

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(0,0),0,1,?_⟩
  fin_cases i <;> norm_num [actual, realize, c2OldDrop, c2NewDrop] <;> decide +kernel

def source_registration : Registration arena
    (type_of% (@_root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.c2_scalar_drops)) where
  actual := actual
  bridge := by
    change (∀ (h t : ℤ) (r : Fin 4), _) ↔ _
    simp only [arena, actual, realize, Fin.reduceEq, true_or, or_true,
      ite_true, false_or, ite_false]
  variation := ⟨actual_law, (actual_sensitivity.1 0).choose,
    (actual_sensitivity.1 0).choose_spec.2.2⟩
  sensitivity := actual_sensitivity
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.c2_scalar_drops)
    (type_of% (realize signature
      (fun role p h => if role = 0 ∨ role = 2 then c2OldDrop h p.1 p.2
        else c2NewDrop h p.1 p.2) (fun e => nomatch e))) Nat Unit := {
  unitName := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.c2_scalar_drops.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Gates.c2_scalar_drops.source_registration
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
    (fun role p h => if role = 0 ∨ role = 2 then c2OldDrop h p.1 p.2
      else c2NewDrop h p.1 p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Gates
    definition := none
    coordinates := #[1,2]
    readouts := #[{
      path := #["body","body","body","fn","arg","fn","arg","arg"]
      stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }, {
      path := #["body","body","body","arg","fn","arg","fn","arg","arg"]
      stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }, {
      path := #["body","body","body","arg","arg","fn","arg","arg"]
      stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }, {
      path := #["body","body","body","arg","arg","arg","arg"]
      stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms audit
end c2_scalar_drops
end Reg.D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Gates
