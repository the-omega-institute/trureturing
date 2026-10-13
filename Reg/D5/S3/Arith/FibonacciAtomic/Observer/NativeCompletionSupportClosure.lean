import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeUniformResidualRealization (RankedExpr)
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure

abbrev signature : Signature where
  Params := Address
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a T => completionReadout a T) (fun e => nomatch e)

def bad : Realization signature := realize signature (fun _ _ _ => .alpha) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k m : Nat) (P : (Fin k → Nat) → Prop)
    (pairs : List (RankedExpr k m × RankedExpr k m))
    (limit : Fin k → Option Nat) (T : Fin m → CompletionTree),
    (∀ (bound : Fin k → Nat) (height : Fin m → Nat),
      ∃ (n : Fin k → Nat) (z : Fin m → Source), ScalarNear limit bound n ∧ P n ∧
        Negatives pairs n z ∧ ∀ (i : Fin m) (a : Address), a.length ≤ height i →
          readout a (z i) = R.readout () a (T i)) ↔
      ∀ bound : Fin k → Nat, ∃ n : Fin k → Nat,
        ScalarNear limit bound n ∧ Support P pairs T n

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  let n : Fin 0 → Nat := fun i => nomatch i
  let limit : Fin 0 → Option Nat := fun i => nomatch i
  let T : Fin 1 → CompletionTree := fun _ => embed (.of false)
  have support : ∀ bound : Fin 0 → Nat, ∃ v : Fin 0 → Nat,
      ScalarNear limit bound v ∧ Support (fun _ => True) [] T v := by
    intro bound
    refine ⟨n, (fun i => nomatch i), trivial, (fun _ => .of false), ?_, ?_⟩
    · simp [Negatives]
    · intro i t ht
      apply _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition.source_foundation.2.2.1 t (.of false)
      intro a _
      have h := congrArg (completionReadout a) ht
      simpa only [T, embed_readout] using h.symm
  obtain ⟨v, z, _, _, _, pref⟩ :=
    (law 0 1 (fun _ => True) [] limit T).mpr support n (fun _ => 1)
  have root := pref 0 [] (by simp)
  have child := pref 0 [false] (by simp)
  change readout [] (z 0) = Reply.alpha at root
  change readout [false] (z 0) = Reply.alpha at child
  cases hz : z 0 with
  | of b => rw [hz] at child; cases child
  | mul l r => rw [hz] at root; cases root

def proof : Registration arena (type_of% (@support_closure_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨support_closure_iff, bad, bad_law⟩
  sensitivity := ⟨fun i => ⟨bad, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, bad_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[], leaf true, leaf false, ?_⟩
    intro h
    change Reply.alpha = Reply.beta at h
    cases h

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.support_closure_iff)
    (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.support_closure_iff
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ a T => completionReadout a T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure
    definition := none
    coordinates := #[11]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg",
        "body","body","arg","body","arg","body","arg","arg","arg",
        "body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure
