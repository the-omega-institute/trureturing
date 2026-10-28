/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeGuardedAtomicReplacement
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Bounded atomic terminals survive simultaneous guarded free-value replacement. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeGuardedFreeExtension

/-! Bounded atomic observations are preserved by simultaneous replacement of
the arbitrary completed boundary values of one guarded system. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement

open NativeCompletionPrefixLifting CompletionHomogeneousFixedPoints
open NativeGuardedFreeExtension
open GenealogicalFiberTransport (Source substitution)

private theorem atomic_pair (n : Nat) :
    atomic (n + 2) = node (atomic (n + 1)) (atomic n) := by
  unfold atomic
  change rho^[n + 2] (embed (.of true)) =
    node (rho^[n + 1] (embed (.of true))) (rho^[n] (embed (.of true)))
  rw [iterate_embed, iterate_embed, iterate_embed,
    NativeRankedEqualityCompiler.atomic_pair]
  rfl

/-- An actual power can equal a finite atomic terminal only at its exact
nonnegative atomic predecessor. Infinite native inputs are not excluded. -/
private theorem atomic_predecessor (a j : Nat) (X : CompletionTree)
    (eq : rho^[a] X = atomic j) : ∃ l, l + a = j ∧ X = atomic l := by
  obtain ⟨t, ht⟩ := (finite_iterate_iff a X).mp
    (eq.symm ▸ CompletionPositiveDriftRegion.atomic_finite j)
  have he : substitution^[a] t = substitution^[j] (.of true) := by
    apply NativeCompletionSupportClosure.embed_injective
    rw [← iterate_embed, ht]
    exact eq
  have zero : NativePrefixIdentityReflection.gamma t = 0 := by
    have h := congrArg NativePrefixIdentityReflection.gamma he
    simpa only [NativePrefixIdentityReflection.gamma_iterate,
      NativePrefixIdentityReflection.gamma] using h
  have rank : NativePrefixIdentityReflection.atomicRank t ≠ none := by
    intro bad
    have pos := (NativePrefixIdentityReflection.gamma_positive t).mpr bad
    omega
  obtain ⟨l, hl⟩ := Option.ne_none_iff_exists'.mp rank
  have et : X = atomic l := by
    rw [← ht, atomic, show leaf true = embed (.of true) from rfl, iterate_embed,
      atomicRank_sound t l hl]
  refine ⟨l, ?_, et⟩
  apply CompletionPositiveDriftRegion.atomic_injective
  rw [← eq, et]
  simpa only [atomic, Nat.add_comm] using
    (Function.iterate_add_apply rho a l (leaf true))

private theorem pair_atomic {U V : CompletionTree} {j : Nat}
    (eq : node U V = atomic j) :
    ∃ n, j = n + 2 ∧ U = atomic (n + 1) ∧ V = atomic n := by
  cases j with
  | zero =>
    have h := congrArg (fun X => (PFunctor.M.dest X).1) eq
    simp [atomic, leaf, node] at h
  | succ j =>
    cases j with
    | zero =>
      have first : atomic 1 = leaf false := rho_alpha
      rw [first] at eq
      have h := congrArg (fun X => (PFunctor.M.dest X).1) eq
      simp [leaf, node] at h
    | succ n =>
      rw [show n + 1 + 1 = n + 2 from rfl, atomic_pair] at eq
      exact ⟨n, rfl, node_inj eq⟩

private theorem expression_atomic_preserved {k m : Nat} (p : Fin k → Nat)
    (v w : Fin m → CompletionTree) (B : Nat)
    (states : ∀ i j, j ≤ B → v i = atomic j → w i = v i)
    (E : Expression k m) :
    ∀ j, j ≤ B → evaluate p v E = atomic j → evaluate p w E = evaluate p v E := by
  induction E with
  | ground t => intros; rfl
  | token i c => intros; rfl
  | var a i =>
    intro j bound eq
    obtain ⟨l, hl, hx⟩ := atomic_predecessor a j (v i) eq
    change rho^[a] (w i) = rho^[a] (v i)
    rw [states i l (by omega) hx]
  | pair A B' ihA ihB =>
    intro j bound eq
    obtain ⟨n, rfl, hA, hB⟩ := pair_atomic eq
    exact congrArg₂ node (ihA (n + 1) (by omega) hA) (ihB n (by omega) hB)

/-- For two actual solutions of the same guarded system at the same parameter,
preserving small atomic free states preserves every small atomic expression.
No assertion is made that the two solutions agree at infinite values. -/
theorem atomic_replacement {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (guarded : Guarded S) (v w : Fin m → CompletionTree)
    (satV : Satisfies S p v) (satW : Satisfies S p w) (B : Nat)
    (free : ∀ i, S i = none → ∀ j, j ≤ B → v i = atomic j → w i = v i) :
    ∀ (E : Expression k m) j, j ≤ B → evaluate p v E = atomic j →
      evaluate p w E = evaluate p v E := by
  have states : ∀ j, j ≤ B → ∀ i, v i = atomic j → w i = v i := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro bound i eq
      cases defn : S i with
      | none => exact free i defn j bound eq
      | some E =>
        rw [satW i E defn, satV i E defn]
        have valueEq : evaluate p v E = atomic j := (satV i E defn).symm.trans eq
        cases E with
        | ground t => rfl
        | token i c => rfl
        | var a i' => exact (guarded i a i' defn).elim
        | pair A B' =>
          obtain ⟨n, rfl, hA, hB⟩ := pair_atomic valueEq
          exact congrArg₂ node
            (expression_atomic_preserved p v w (n + 1)
              (fun i l hl => ih l (by omega) (by omega) i) A (n + 1) le_rfl hA)
            (expression_atomic_preserved p v w n
              (fun i l hl => ih l (by omega) (by omega) i) B' n le_rfl hB)
  exact expression_atomic_preserved p v w B (fun i j hj => states j hj i)

end D5.S3.Arith.FibonacciAtomic.Observer.NativeGuardedAtomicReplacement
