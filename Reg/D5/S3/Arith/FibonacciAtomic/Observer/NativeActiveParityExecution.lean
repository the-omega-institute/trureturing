import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution

open _root_.D5.S3.Arith.FibonacciAtomic
open ActualTreeReadoutAcquisition (Address Reply)
open GenealogicalFiberTransport (Source)
open Observer.NativeActiveParityExecution
open _root_.D5.S3.ObserverMemory.Algorithms.GuardedPhaseExecution
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev Parameters := Σ _ : Source, Nat
abbrev signature := Reg.Support.SingleDependentReadout.signature Parameters
  (fun p => Fin p.1.length → Bool) (fun _ => Nat → Address → Reply)

def actual : Realization signature :=
  realize signature (fun _ p x => observations (chartOf p.1) p.2 x) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => Reply.alpha) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (S : Source) (x : Fin S.length → Bool)
    (t K : Nat), t ≤ 2 * K → (S.length % 2 = 0 ∨ t = 0) →
    ∀ (b : Bool) (N : Nat),
    Run (program (chartOf S) K) (R.readout () ⟨S, t⟩ x)
      (start S.length) 0 (endpoint S.length b) N ↔
      b = parity (labels x) S.length ∧
        N = 2 * (K - (t + bit (x ⟨0, S.length_pos⟩)) / 2) ∧
        output (endpoint S.length b) = some (parity (labels x) S.length)

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have run : Run (program (chartOf (.of true)) 0) (fun _ _ => Reply.alpha)
      (start 1) 0 (endpoint 1 false) 0 := by
    apply Run.read (p := []) (k := dispatch ⟨0, by decide⟩ false)
      (by simp [program, start, chartOf, locator, Observer.DelayedOriginalReadout.rights])
    change Run (program (chartOf (.of true)) 0) (fun _ _ => Reply.alpha)
      (.b ⟨0, by decide⟩ false false) 0 (endpoint 1 false) 0
    apply Run.read (p := []) (k := fun _ =>
      if false = false then .c ⟨0, by decide⟩ false else .b ⟨0, by decide⟩ false false) rfl
    apply Run.read (p := []) (k := fun _ => next ⟨0, by decide⟩ false) rfl
    exact .refl _ _
  have bad := (law (.of true) (fun _ => true) 0 0
    (by decide) (Or.inr rfl) false 0).mp run
  have impossible : false = true := by simpa [parity, labels] using bad.1
  cases impossible

def evidence : Registration arena (type_of% (@native_active_parity_execution)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_active_parity_execution, rejected, negative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ negative
  dependence := by
    intro i
    refine ⟨⟨.of true, 0⟩, (fun _ => false), (fun _ => true), ?_⟩
    intro same
    have root := congrFun (congrFun same 0) []
    change Reply.alpha = Reply.beta at root
    cases root

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_active_parity_execution) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.native_active_parity_execution.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.evidence
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution
    definition := none
    coordinates := #[0,2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn", "fn", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration


abbrev coneParameters := Σ h : Nat, Σ _ : Chart h, Nat
abbrev coneSignature := Reg.Support.SingleDependentReadout.signature coneParameters
  (fun p => Fin p.1 → Bool) (fun _ => Nat → Address → Reply)
def coneActual : Realization coneSignature :=
  realize coneSignature (fun _ p x => observations p.2.1 p.2.2 x) (fun e => nomatch e)
def coneRejected : Realization coneSignature :=
  realize coneSignature (fun _ _ _ _ _ => .alpha) (fun e => nomatch e)
abbrev coneArena : Arena where
  signature := coneSignature
  Law R := ∀ {h : Nat} (C : Chart h) (x : Fin h → Bool)
    (t j : Nat) (i : Fin h) (p : Address),
    R.readout () ⟨h,C,t⟩ x j (C.address i ++ p) =
      ActualTreeReadoutAcquisition.readout p (atom (t+j+bit (x i)))
private theorem coneNegative : ¬ coneArena.Law coneRejected := by
  intro law
  have bad := law (chartOf (.of true)) (fun _ => true) 0 0 ⟨0,by decide⟩ []
  change Reply.alpha = Reply.beta at bad
  cases bad
def coneEvidence : Registration coneArena (type_of% (@cone_read)) where
  actual := coneActual
  bridge := Iff.rfl
  variation := ⟨@cone_read,coneRejected,coneNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ coneNegative
  dependence := by
    intro i
    refine ⟨⟨1,chartOf (.of true),0⟩,(fun _ => false),(fun _ => true),?_⟩
    intro same
    have raw := congrFun (congrFun same 0) []
    change Reply.alpha = Reply.beta at raw
    cases raw

def coneRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.cone_read) (Realization coneSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.cone_read.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.coneEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coneArena⟩
  objectArena := .source ⟨coneArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coneArena ⟨coneEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coneSignature coneActual.readout coneActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution
    definition := none
    coordinates := #[0,1,3]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg","fn","fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev shiftSignature := Reg.Support.SingleDependentReadout.signature Nat
  (fun _ => Nat → Bool) (fun _ => Bool)
def shiftActual : Realization shiftSignature :=
  realize shiftSignature (fun _ n x => parity x n) (fun e => nomatch e)
def shiftRejected : Realization shiftSignature :=
  realize shiftSignature (fun _ _ _ => false) (fun e => nomatch e)
abbrev shiftArena : Arena where
  signature := shiftSignature
  Law R := ∀ (x : Nat → Bool) (b : Bool) (n : Nat),
    R.readout () n (fun i => xor b (x i)) =
      xor (decide (n%2=1) && b) (parity x n)
private theorem shiftNegative : ¬ shiftArena.Law shiftRejected := by
  intro law
  have bad := law (fun _ => true) false 1
  change false = true at bad
  cases bad
def shiftEvidence : Registration shiftArena (type_of% (@shifted_parity)) where
  actual := shiftActual
  bridge := Iff.rfl
  variation := ⟨shifted_parity,shiftRejected,shiftNegative⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ _ _ shiftNegative
  dependence := by
    intro i
    refine ⟨1,(fun _ => false),(fun _ => true),?_⟩
    intro same
    change false = true at same
    cases same

def shiftRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.shifted_parity) (Realization shiftSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.shifted_parity.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution.shiftEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨shiftArena⟩
  objectArena := .source ⟨shiftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shiftArena ⟨shiftEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize shiftSignature shiftActual.readout shiftActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms coneEvidence
#print axioms shiftEvidence
end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeActiveParityExecution
