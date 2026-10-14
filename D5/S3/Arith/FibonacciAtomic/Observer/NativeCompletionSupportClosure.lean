/- GID: D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionSupportClosure
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Exact native signed support controls every finite scalar and tree neighborhood. -/

import D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionBranchExistence
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure

open GenealogicalFiberTransport (Source)
open ActualTreeReadoutAcquisition (Address readout leaves source_foundation)
open NativeUniformResidualRealization (RankedExpr rankedEval)
open NativePrefixIdentityReflection (MixedExpr eval)
open NativeSimultaneousPrefixSeparation (bind eval_bind fixedEval)
open NativeCompletionPrefixLifting
open NativeCompletionBranchExistence (infinite_of_not_finite)

/-- None is the divergent scalar point; every supplied bound is simultaneous. -/
def ScalarNear {k : Nat} (limit : Fin k → Option Nat) (bound n : Fin k → Nat) : Prop :=
  ∀ i, match limit i with
    | some a => n i = a
    | none => bound i ≤ n i

/-- All finite negatives are interpreted jointly on one actual residual tuple. -/
def Negatives {k m : Nat} (pairs : List (RankedExpr k m × RankedExpr k m))
    (n : Fin k → Nat) (z : Fin m → Source) : Prop :=
  ∀ e ∈ pairs, rankedEval n z e.1 ≠ rankedEval n z e.2

/-- Exactly the finite coordinates of the completion are held fixed. -/
def Support {k m : Nat} (P : (Fin k → Nat) → Prop)
    (pairs : List (RankedExpr k m × RankedExpr k m)) (T : Fin m → CompletionTree)
    (n : Fin k → Nat) : Prop :=
  P n ∧ ∃ z : Fin m → Source, Negatives pairs n z ∧
    ∀ (i : Fin m) (t : Source), embed t = T i → z i = t

/-- Closure in the explicit finite scalar and complete-prefix neighborhoods. -/
def JointClosure {k m : Nat} (P : (Fin k → Nat) → Prop)
    (pairs : List (RankedExpr k m × RankedExpr k m))
    (limit : Fin k → Option Nat) (T : Fin m → CompletionTree) : Prop :=
  ∀ (bound : Fin k → Nat) (height : Fin m → Nat),
    ∃ (n : Fin k → Nat) (z : Fin m → Source), ScalarNear limit bound n ∧ P n ∧
      Negatives pairs n z ∧ ∀ (i : Fin m) (a : Address), a.length ≤ height i →
        readout a (z i) = completionReadout a (T i)

theorem embed_injective : Function.Injective embed := by
  intro s t h
  apply source_foundation.2.2.1 t s
  intro a _
  rw [← embed_readout, ← embed_readout, h]

private theorem finite_isolating_height (T : CompletionTree) :
    ∃ h : Nat, ∀ z : Source,
      (∀ a : Address, a.length ≤ h → readout a z = completionReadout a T) →
      ∀ t : Source, embed t = T → z = t := by
  classical
  by_cases finite : ∃ t : Source, embed t = T
  · obtain ⟨t, rfl⟩ := finite
    refine ⟨(leaves t).toFinset.sup List.length, fun z table u hu => ?_⟩
    have fixed : z = t := by
      apply source_foundation.2.2.1 t z
      intro a ha
      simpa only [embed_readout] using table a (Finset.le_sup (by simpa using ha))
    exact fixed.trans (embed_injective hu).symm
  · exact ⟨0, fun _ _ t ht => (finite ⟨t, ht⟩).elim⟩

private def reindex {k m q : Nat} (σ : Fin m → Fin q) (E : RankedExpr k m) :
    RankedExpr k q := bind (fun i => match i with
      | .inl j => .residual 0 (.inl j)
      | .inr j => .residual 0 (.inr (σ j))) E

private theorem eval_reindex {k m q : Nat} (σ : Fin m → Fin q)
    (n : Fin k → Nat) (z : Fin q → Source) (E : RankedExpr k m) :
    rankedEval n z (reindex σ E) = rankedEval n (z ∘ σ) E := by
  unfold rankedEval reindex
  rw [eval_bind]
  congr 1
  funext i
  cases i <;> rfl

private def assemble {q r s : Nat} (e : Fin (r + s) ≃ Fin q)
    (f : Fin r → Source) (z : Fin s → Source) : Fin q → Source :=
  Sum.elim f z ∘ finSumFinEquiv.symm ∘ e.symm

private theorem split_prefix_lift {k q r s : Nat}
    (e : Fin (r + s) ≃ Fin q)
    (pairs : List (RankedExpr k q × RankedExpr k q)) (n : Fin k → Nat)
    (seed : Fin q → Source) (T : Fin q → CompletionTree)
    (fixed : ∀ i : Fin r, embed (seed (e (finSumFinEquiv (.inl i)))) =
      T (e (finSumFinEquiv (.inl i))))
    (infinite : ∀ i : Fin s, HasInfiniteBranch (T (e (finSumFinEquiv (.inr i)))))
    (feasible : Negatives pairs n seed) (height : Fin q → Nat) :
    ∃ z : Fin q → Source, Negatives pairs n z ∧
      ∀ (i : Fin q) (a : Address), a.length ≤ height i →
        readout a (z i) = completionReadout a (T i) := by
  let f : Fin r → Source := fun i => seed (e (finSumFinEquiv (.inl i)))
  let seed' : Fin s → Source := fun i => seed (e (finSumFinEquiv (.inr i)))
  let transformed := pairs.map fun p => (reindex e.symm p.1, reindex e.symm p.2)
  have evaluate (z : Fin s → Source) (E : RankedExpr k q) :
      fixedEval n f z (reindex e.symm E) = rankedEval n (assemble e f z) E :=
    eval_reindex e.symm n (Sum.elim f z ∘ finSumFinEquiv.symm) E
  have restored : assemble e f seed' = seed := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases j <;> simp [assemble, f, seed']
  have seed_witness : ∃ z : Fin s → Source, ∀ p ∈ transformed,
      fixedEval n f z p.1 ≠ fixedEval n f z p.2 := by
    refine ⟨seed', ?_⟩
    intro p hp
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp
      (show p ∈ pairs.map (fun q => (reindex e.symm q.1, reindex e.symm q.2)) from hp)
    subst p
    simpa only [evaluate, restored] using feasible q hq
  obtain ⟨z, pref, neq⟩ := simultaneous_prefix_disequality k r s transformed n f
    seed_witness (fun i => T (e (finSumFinEquiv (.inr i)))) infinite
    (fun i => height (e (finSumFinEquiv (.inr i))))
  refine ⟨assemble e f z, ?_, ?_⟩
  · intro p hp
    have h := neq (reindex e.symm p.1, reindex e.symm p.2)
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa only [evaluate] using h
  · intro i a ha
    obtain ⟨j, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
    cases j with
    | inl j =>
      simp only [assemble, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
      rw [← embed_readout, fixed]
    | inr j =>
      simpa only [assemble, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
        using pref j a ha

/-- Full signed local-prefix closure is exactly closure of the complete finite-coordinate support. -/
theorem support_closure_iff (k m : Nat) (P : (Fin k → Nat) → Prop)
    (pairs : List (RankedExpr k m × RankedExpr k m))
    (limit : Fin k → Option Nat) (T : Fin m → CompletionTree) :
    (∀ (bound : Fin k → Nat) (height : Fin m → Nat),
      ∃ (n : Fin k → Nat) (z : Fin m → Source), ScalarNear limit bound n ∧ P n ∧
        Negatives pairs n z ∧ ∀ (i : Fin m) (a : Address), a.length ≤ height i →
          readout a (z i) = completionReadout a (T i)) ↔
      ∀ bound : Fin k → Nat, ∃ n : Fin k → Nat,
        ScalarNear limit bound n ∧ Support P pairs T n := by
  classical
  change JointClosure P pairs limit T ↔ _
  constructor
  · intro joint bound
    choose height isolate using fun i => finite_isolating_height (T i)
    obtain ⟨n, z, scalar, hp, negatives, pref⟩ := joint bound height
    exact ⟨n, scalar, hp, z, negatives, fun i t ht => isolate i (z i) (pref i) t ht⟩
  · intro support bound height
    obtain ⟨n, scalar, hp, seed, negatives, fixed⟩ := support bound
    let finite : Fin m → Prop := fun i => ∃ t : Source, embed t = T i
    let F := {i : Fin m // finite i}
    let I := {i : Fin m // ¬ finite i}
    let r := Fintype.card F
    let s := Fintype.card I
    let eF : Fin r ≃ F := (Fintype.equivFin F).symm
    let eI : Fin s ≃ I := (Fintype.equivFin I).symm
    let e : Fin (r + s) ≃ Fin m :=
      finSumFinEquiv.symm.trans ((eF.sumCongr eI).trans (Equiv.sumCompl finite))
    have eLeft (i : Fin r) : e (finSumFinEquiv (.inl i)) = (eF i).val := by
      simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
        Sum.map_inl]
      rfl
    have eRight (i : Fin s) : e (finSumFinEquiv (.inr i)) = (eI i).val := by
      simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.sumCongr_apply,
        Sum.map_inr]
      rfl
    have hf (i : Fin r) : embed (seed (e (finSumFinEquiv (.inl i)))) =
        T (e (finSumFinEquiv (.inl i))) := by
      have hi : finite (e (finSumFinEquiv (.inl i))) := by
        rw [eLeft]
        exact (eF i).property
      obtain ⟨t, ht⟩ := hi
      rw [fixed _ t ht]
      exact ht
    have hinf (i : Fin s) : HasInfiniteBranch (T (e (finSumFinEquiv (.inr i)))) := by
      apply infinite_of_not_finite
      rw [eRight]
      exact (eI i).property
    obtain ⟨z, hz, pref⟩ := split_prefix_lift e pairs n seed T hf hinf negatives height
    exact ⟨n, z, scalar, hp, hz, pref⟩

#print axioms support_closure_iff

end D5.S3.Arith.FibonacciAtomic.Observer.NativeCompletionSupportClosure
