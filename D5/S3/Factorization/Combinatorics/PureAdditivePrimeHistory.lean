/- GID: D5/S3/Factorization/Combinatorics/PureAdditivePrimeHistory
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/PureAdditivePrimeHistory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pure additive prime words evaluate to prime sums and their endpoint counts equal shifted ordered tuple counts. -/

import D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.PureAdditivePrimeHistory

open D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- An ordered tuple of primes at most X, with repetition allowed. -/
abbrev PrimeTuple (X k : ℕ) := Fin k → {p : ℕ // p ∈ Nat.primesLE X}

/-- The integer sum of the prime labels in a tuple. -/
def tupleSum {X k : ℕ} (a : PrimeTuple X k) : ℤ := ∑ i, ((a i).val : ℤ)

/-- The number of ordered bounded prime tuples with the specified integer sum. -/
noncomputable def tupleCount (X k : ℕ) (N : ℤ) : ℕ :=
  Nat.card {a : PrimeTuple X k // tupleSum a = N}

/-- Encode a tuple as a word of additive prime letters in the same order. -/
def tupleWord {X k : ℕ} (a : PrimeTuple X k) : List PrimeLetter :=
  List.ofFn (fun i => Sum.inl ⟨(a i).val, Nat.prime_of_mem_primesLE (a i).property⟩)

/-- Applying additive prime letters adds their sum to the initial state. -/
theorem pure_additive_run (qs : List Nat.Primes) (m : ℕ) :
    runWord primeStep (qs.map Sum.inl) m = m + (qs.map Subtype.val).sum := by
  induction qs generalizing m with
  | nil => rfl
  | cons q qs ih =>
    change runWord primeStep (qs.map Sum.inl) (m + q.val) =
      m + (q.val + (qs.map Subtype.val).sum)
    rw [ih]
    omega

set_option backward.isDefEq.respectTransparency false in
/-- Additive words starting at one are counted by tuples whose sum is one less than the endpoint. -/
theorem additive_tuple_count (X k : ℕ) (N : ℕ) :
    Nat.card {w : List PrimeLetter //
      (∃ a : PrimeTuple X k, tupleWord a = w) ∧ endpoint w = N} =
        tupleCount X k ((N : ℤ) - 1) := by
  classical
  have injective : Function.Injective (@tupleWord X k) := by
    intro a b hab
    have h : (fun i => (Sum.inl
        ⟨(a i).val, Nat.prime_of_mem_primesLE (a i).property⟩ : PrimeLetter)) =
        (fun i => (Sum.inl
          ⟨(b i).val, Nat.prime_of_mem_primesLE (b i).property⟩ : PrimeLetter)) :=
      List.ofFn_injective hab
    funext i
    apply Subtype.ext
    exact congrArg (fun q : Nat.Primes => q.val) (Sum.inl.inj (congrFun h i))
  have endpoint_sum (a : PrimeTuple X k) :
      (endpoint (tupleWord a) : ℤ) = 1 + tupleSum a := by
    have h := pure_additive_run (List.ofFn (fun i : Fin k =>
      (⟨(a i).val, Nat.prime_of_mem_primesLE (a i).property⟩ : Nat.Primes))) 1
    have hh : endpoint (tupleWord a) = 1 + ∑ i, (a i).val := by
      rw [List.map_ofFn, List.map_ofFn, List.sum_ofFn] at h
      exact h
    unfold tupleSum
    exact_mod_cast hh
  let encode : {a : PrimeTuple X k // tupleSum a = (N : ℤ) - 1} →
      {w : List PrimeLetter //
        (∃ a : PrimeTuple X k, tupleWord a = w) ∧ endpoint w = N} := fun a =>
    ⟨tupleWord a.val, ⟨a.val, rfl⟩, by
      have he := endpoint_sum a.val
      have hs := a.property
      have hn : (endpoint (tupleWord a.val) : ℤ) = (N : ℤ) := by omega
      exact_mod_cast hn⟩
  have encode_injective : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    exact injective (congrArg Subtype.val hab)
  have encode_surjective : Function.Surjective encode := by
    rintro ⟨w, ⟨a, rfl⟩, hw⟩
    refine ⟨⟨a, ?_⟩, rfl⟩
    have he := endpoint_sum a
    rw [hw] at he
    omega
  exact Nat.card_congr (Equiv.ofBijective encode
    ⟨encode_injective, encode_surjective⟩).symm

end D5.S3.Factorization.Combinatorics.PureAdditivePrimeHistory
