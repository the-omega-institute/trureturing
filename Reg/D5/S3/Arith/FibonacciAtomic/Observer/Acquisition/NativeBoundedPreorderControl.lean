import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source composition)
open Observer.Acquisition.NativeBoundedPreorderControl
open Observer.Acquisition.NativeBoundedPreorderRows (canonical rowParameters rowInitial)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution (Run)
open _root_.D5.S3.ObserverMemory.Algorithms.TwoBankInstalledWord (sourceProgram actualObservation)

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Source) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ u => decide ((composition u).2 % 2 = 1)) (fun e => nomatch e)

def bad : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (h T t : Nat) (u : Source), u.length = h → t ≤ T →
    (T = 0 ∨ h % 2 = 0) → ∀ active : Bool,
    Specification h T t u active (R.readout () () u)

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have wrong := law 1 0 0 (.of true) rfl (by decide) (Or.inl rfl) false
  have correct := native_bounded_preorder_control 1 0 0 (.of true) rfl
    (by decide) (Or.inl rfl) false
  let P := rowParameters 1 0 false
  let e := indexWidth 1 0 false
  let obs := actualObservation (.of true)
  have wrongRun : Run (sourceProgram (rowTable P e)) obs
      (encode P.h e (rowInitial 0 false)) 0 (encode P.h e (canonical .halt1)) 0 :=
    wrong.2.2.2.2.2.1
  have correctRun : Run (sourceProgram (rowTable P e)) obs
      (encode P.h e (rowInitial 0 false)) 0 (encode P.h e (canonical .halt0)) 0 :=
    correct.2.2.2.2.2.1
  have wrongHalt : (rowTable P e).instruction (encode P.h e (canonical .halt1)) = .halt true :=
    wrong.2.2.2.2.2.2.1
  have correctHalt : (rowTable P e).instruction (encode P.h e (canonical .halt0)) = .halt false :=
    correct.2.2.2.2.2.2.1
  have same := _root_.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution.run_halt_unique
    wrongRun correctRun (by simp [sourceProgram, wrongHalt]) (by simp [sourceProgram, correctHalt])
  rw [same.1] at wrongHalt
  cases correctHalt.symm.trans wrongHalt

def family : Registration arena (type_of% (@native_bounded_preorder_control)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_bounded_preorder_control, bad, bad_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ bad_law
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    change (false : Bool) ≠ true
    decide

def native_bounded_preorder_control_registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@native_bounded_preorder_control) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl.unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition.NativeBoundedPreorderControl
