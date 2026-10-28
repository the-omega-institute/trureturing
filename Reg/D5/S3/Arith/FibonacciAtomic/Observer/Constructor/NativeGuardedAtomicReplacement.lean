import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement
import Reg.Support.DependentFamily

/-! The observed output is the whole native value of an expression at a state
assignment. The source law retains both solutions and all bounded hypotheses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedFreeExtension
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionPrefixLifting
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionHomogeneousFixedPoints
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement

noncomputable section

abbrev signature : Signature where
  Params := Σ k : Nat, Σ m : Nat, (Fin k → Nat) × Expression k m
  State q := Fin q.2.1 → CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature := realize signature
  (fun _ q v => evaluate q.2.2.1 v q.2.2.2) (fun e => nomatch e)

abbrev rejected : Realization signature := realize signature
  (fun _ _ _ => leaf false) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k m : Nat} (S : System k m) (p : Fin k → Nat), Guarded S →
    ∀ v w : Fin m → CompletionTree, Satisfies S p v → Satisfies S p w →
    ∀ B : Nat,
    (∀ i, S i = none → ∀ j, j ≤ B → v i = atomic j → w i = v i) →
    ∀ (E : Expression k m) j, j ≤ B → evaluate p v E = atomic j →
      R.readout () ⟨k, m, p, E⟩ w = evaluate p v E

private theorem actual_law : arena.Law actual := @atomic_replacement

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have bad : leaf false = leaf true :=
    law (Fin.elim0 : System 0 0) Fin.elim0 (by intro i; exact Fin.elim0 i)
      Fin.elim0 Fin.elim0 (by intro i; exact Fin.elim0 i)
      (by intro i; exact Fin.elim0 i) 0 (by intro i; exact Fin.elim0 i)
      (.ground (.of true)) 0 le_rfl rfl
  have tag := leaf_inj bad
  cases tag

private theorem readout_depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0, 1, Fin.elim0, .var 0 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
  intro eq
  have tag := leaf_inj eq
  cases tag

def evidence : Registration arena (type_of% (@atomic_replacement)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := readout_depends

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@atomic_replacement) (Realization signature) (Nat → Type) Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement.atomic_replacement.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q v => evaluate q.2.2.1 v q.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (fun m : Nat => Fin m → CompletionTree)
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement
    definition := none
    coordinates := #[0, 1, 3, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement
