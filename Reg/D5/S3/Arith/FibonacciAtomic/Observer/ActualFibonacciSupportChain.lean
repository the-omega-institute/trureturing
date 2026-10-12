import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open Observer.ActualFibonacciSupportChain
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature := Reg.Support.SingleDependentReadout.signature
  Unit (fun _ => Nat) (fun _ => Set Address)

def actual : Realization signature :=
  realize signature
    (fun _ _ j => {q : Address | readout q (substitution^[j] (FreeMagma.of true)) ≠ .absent})
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : Nat) (_hk : 1 ≤ k),
    let T := fun j : Nat => substitution^[j] (FreeMagma.of true)
    let S := fun j : Nat => R.readout () () j
    let H := {q : Address | readout q (FreeMagma.mul (T (2*k)) (T (2*k))) ≠ .absent}
    S (2*k) ⊂ S (2*k+1) ∧ S (2*k+1) ⊂ H ∧
      ∀ q : Address, q.length ≤ k →
        (q ∈ S (2*k) ↔ q ∈ S (2*k+1)) ∧ (q ∈ S (2*k+1) ↔ q ∈ H)

def family : Registration arena (type_of% (@actual_fibonacci_support_chain)) where
  actual := actual
  bridge := Iff.rfl
  variation := by
    refine ⟨@actual_fibonacci_support_chain, rejected, ?_⟩
    intro h
    have impossible := (h 1 (by decide)).1
    exact (Set.ssubset_iff_subset_ne.mp impossible).2 rfl
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected (by
    intro h
    exact (Set.ssubset_iff_subset_ne.mp (h 1 (by decide)).1).2 rfl)
  dependence := by
    intro i
    refine ⟨(), 0, 2, ?_⟩
    intro h
    have fresh : [false] ∈ actual.readout i () 2 := by
      change readout [false] (substitution^[2] (FreeMagma.of true)) ≠ .absent
      decide
    rw [← h] at fresh
    exact fresh rfl

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_fibonacci_support_chain) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain.actual_fibonacci_support_chain.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain.family
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
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain

#print axioms Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain.family
#print axioms Reg.D5.S3.Arith.FibonacciAtomic.Observer.ActualFibonacciSupportChain.registration
