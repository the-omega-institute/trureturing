import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source)
open Observer.DelayedOriginalReadout (rightClock)
open ActualTreeReadoutAcquisition (Address Reply)
open Observer.NativePollingAlignment
open _root_.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Source) (fun _ => Nat → Address → Reply)

def actual : Realization signature :=
  realize signature (fun _ _ u => observations u) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => observations (.of false)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : Nat) (u : Source), rightClock u ≤ 2 * K + 1 →
    ∀ (b : Bool) (N : Nat), Run (program K) (R.readout () () u) .poll 0 (.done b) N ↔
      b = decide (rightClock u % 2 = 1) ∧ N = 2 * (K - rightClock u / 2)

private theorem positive : arena.Law actual := by
  intro K u bound b N
  exact native_polling_alignment K u bound b N

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have wrong : Run (program 0) (observations (.of false))
      .poll 0 (.done false) 0 :=
    (law 0 (.of true) (by decide) false 0).mpr (by decide)
  have impossible : false = true :=
    ((native_polling_alignment 0 (.of false) (by decide) false 0).mp wrong).1
  cases impossible

def evidence : Registration arena (type_of% (@native_polling_alignment)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨positive, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ negative
  dependence := by
    intro i
    refine ⟨(), .of true, .of false, ?_⟩
    intro same
    have root := congrFun (congrFun same 0) []
    change Reply.alpha = Reply.beta at root
    cases root

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_polling_alignment) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment.native_polling_alignment.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg",
        "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePollingAlignment
