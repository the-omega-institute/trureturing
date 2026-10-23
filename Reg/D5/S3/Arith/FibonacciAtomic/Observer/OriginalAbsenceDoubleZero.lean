import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.OriginalAbsenceDoubleZero
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalAbsenceDoubleZero

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open Observer.DelayedOriginalReadout (rights)
open Observer.OriginalAbsenceDoubleZero (original_absence_double_zero)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev probeSignature : Signature where
  Params := Nat × Address
  State _ := Source
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def probeActual : Realization probeSignature :=
  realize probeSignature
    (fun role q u => if role then
      readout (q.2 ++ rights q.1 ++ [false]) (substitution^[2*q.1] u)
    else readout (q.2 ++ rights (q.1-1) ++ [false, false]) (substitution^[2*q.1] u))
    (fun e => nomatch e)

abbrev probeArena : Arena where
  signature := probeSignature
  Law R := ∀ (u : Source) (k : Nat) (p : Address),
    1 ≤ k → readout p u = .absent →
    R.readout false (k,p) u = .absent ∧ R.readout true (k,p) u = .absent

def probeFamily : Registration probeArena (type_of% (@original_absence_double_zero)) where
  actual := probeActual
  bridge := Iff.rfl
  variation := by
    refine ⟨@original_absence_double_zero,
      realize probeSignature (fun _ _ _ => .alpha) (fun e => nomatch e), ?_⟩
    intro h
    have wrong := (h (.of true) 1 [false] (by decide) rfl).1
    change Reply.alpha = Reply.absent at wrong
    cases wrong
  sensitivity := by
    constructor
    · intro i
      let bad : Realization probeSignature := realize probeSignature
        (fun j q u => if j = i then .alpha else probeActual.readout j q u)
        (fun e => nomatch e)
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro j hj
        funext q u
        simp [bad, realize, hj]
      · intro h
        have wrong := h (.of true) 1 [false] (by decide) rfl
        cases i
        · have hzero := wrong.1
          change Reply.alpha = Reply.absent at hzero
          cases hzero
        · have hzero := wrong.2
          change Reply.alpha = Reply.absent at hzero
          cases hzero
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1, []), .of true, .mul (.of true) (.of true), ?_⟩
    cases i <;> change Reply.absent ≠ Reply.beta <;> decide

def original_absence_double_zero_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@original_absence_double_zero) (Realization probeSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.OriginalAbsenceDoubleZero.original_absence_double_zero.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalAbsenceDoubleZero.probeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨probeArena⟩
  objectArena := .source ⟨probeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source probeArena ⟨probeFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize probeSignature
    (fun role q u => if role then
      readout (q.2 ++ rights q.1 ++ [false]) (substitution^[2*q.1] u)
    else readout (q.2 ++ rights (q.1-1) ++ [false, false]) (substitution^[2*q.1] u))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.OriginalAbsenceDoubleZero
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.OriginalAbsenceDoubleZero
