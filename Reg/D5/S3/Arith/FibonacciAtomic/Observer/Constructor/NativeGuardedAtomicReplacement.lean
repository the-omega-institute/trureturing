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
  have tag := congrArg (fun X => (PFunctor.M.dest X).1) bad
  cases tag

private theorem readout_depends : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0, 1, Fin.elim0, .var 0 0⟩, (fun _ => leaf true), (fun _ => leaf false), ?_⟩
  intro eq
  have tag := congrArg (fun X => (PFunctor.M.dest X).1) eq
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
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement

open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeImageSaturationInterface
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.CompletionPositiveDriftRegion (atomic_finite omega_not_finite)

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement.ExposedSuppliers
noncomputable section

abbrev completionSignature : Signature where
  Params := Unit
  State _ := CompletionTree
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := CompletionTree
  Anchor := Empty
  finiteAnchor := inferInstance
abbrev actual : Realization completionSignature :=
  realize completionSignature (fun _ _ X => X) (fun e => nomatch e)
abbrev rejected : Realization completionSignature :=
  realize completionSignature (fun _ _ _ => Omega) (fun e => nomatch e)
def observed (R : Realization completionSignature) (X : CompletionTree) : CompletionTree :=
  R.readout () () X
private theorem dependence : ObservationalDependence completionSignature actual := by
  intro role
  refine ⟨(),leaf true,leaf false,?_⟩
  intro eq
  have tag := congrArg (fun X => (PFunctor.M.dest X).1) eq
  cases tag

namespace Pair
abbrev arena : Arena where
  signature := completionSignature
  Law R := ∀ n : Nat, observed R (atomic (n+2)) = node (atomic (n+1)) (atomic n)
private theorem actual_law : arena.Law actual := @atomic_pair
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have eq : Omega = atomic 2 := (law 0).trans (atomic_pair 0).symm
  exact omega_not_finite (eq.symm ▸ atomic_finite 2)

def evidence : Registration arena (type_of% (@atomic_pair)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@atomic_pair) (Realization completionSignature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement.atomic_pair.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement.ExposedSuppliers.Pair.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize completionSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some CompletionTree
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Pair

namespace Predecessor
abbrev arena : Arena where
  signature := completionSignature
  Law R := ∀ (a j : Nat) (X : CompletionTree), rho^[a] X = atomic j →
    ∃ l, l+a = j ∧ observed R X = atomic l
private theorem actual_law : arena.Law actual := @atomic_predecessor
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨l,rank,eq⟩ := law 0 0 (leaf true) rfl
  exact omega_not_finite (eq.symm ▸ atomic_finite l)

def evidence : Registration arena (type_of% (@atomic_predecessor)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@atomic_predecessor) (Realization completionSignature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement.atomic_predecessor.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement.ExposedSuppliers.Predecessor.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize completionSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some CompletionTree
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Predecessor

namespace Parse
abbrev arena : Arena where
  signature := completionSignature
  Law R := ∀ {U V : CompletionTree} {j : Nat}, node U V = atomic j →
    ∃ n, j = n+2 ∧ observed R U = atomic (n+1) ∧ observed R V = atomic n
private theorem actual_law : arena.Law actual := @pair_atomic
private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨n,rank,eq,left⟩ := law (atomic_pair 0).symm
  exact omega_not_finite (eq.symm ▸ atomic_finite (n+1))

def evidence : Registration arena (type_of% (@pair_atomic)) where
  actual := actual
  bridge := by rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j h => (h (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@pair_atomic) (Realization completionSignature) Type Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement.pair_atomic.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement.ExposedSuppliers.Parse.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize completionSignature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some CompletionTree
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Parse

end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedAtomicReplacement.ExposedSuppliers
