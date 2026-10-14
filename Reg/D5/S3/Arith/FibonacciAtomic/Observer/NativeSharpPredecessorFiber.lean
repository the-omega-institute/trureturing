import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Observer.ActualCutPartitionRecovery
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber

abbrev signature : Signature where
  Params := Σ n : Nat, {z : Fin (n + 1) → Source // Function.Injective z}
  State p := Option (Fin (p.1 + 1))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := LiteralRow
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p a => canonicalRow (cut p.1) (origin p.1 p.2.val a)) (fun e => nomatch e)

def bad : Realization signature := realize signature
  (fun _ _ _ => .of (.inl true)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (n : Nat) (z : Fin (n + 1) → Source) (hz : Function.Injective z),
    Sharp n z (fun a => R.readout () ⟨n,⟨z,hz⟩⟩ a)

theorem bridge : (type_of% (@native_sharp_predecessor_fiber)) ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual := @native_sharp_predecessor_fiber

private theorem one_tag : Function.Injective (fun _ : Fin 1 => (FreeMagma.of true : Source)) := by
  intro a b _; exact Subsingleton.elim a b

private theorem bad_law : ¬ arena.Law bad := by
  intro law
  have inj := (law 0 (fun _ => .of true) one_tag).2.2.2.2.1
  have eq := inj (a₁ := none) (a₂ := some 0) rfl
  cases eq

def proof : Registration arena (type_of% (@native_sharp_predecessor_fiber)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    refine ⟨⟨0,⟨(fun _ => .of true),one_tag⟩⟩,none,some 0,?_⟩
    intro eq
    have role : i = () := Subsingleton.elim _ _
    rw [role] at eq
    have inj := (actual_law 0 (fun _ => .of true) one_tag).2.2.2.2.1
    have impossible := inj eq
    cases impossible

noncomputable def native_sharp_predecessor_fiber_registration :
    LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber.native_sharp_predecessor_fiber)
    (Realization signature)
    ((n : Nat) → (z : Fin (n + 1) → Source) → Function.Injective z → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber.native_sharp_predecessor_fiber
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p a => canonicalRow (cut p.1) (origin p.1 p.2.val a)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "arg", "body"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms proof
#print axioms native_sharp_predecessor_fiber_registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSharpPredecessorFiber
