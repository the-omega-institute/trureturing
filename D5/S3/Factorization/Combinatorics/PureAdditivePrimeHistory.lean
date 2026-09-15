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

/-- Additive words starting at one are counted by tuples whose sum is one less than the endpoint. -/
theorem additive_tuple_count (X k : ℕ) (N : ℕ) :
    Nat.card {w : List PrimeLetter //
      (∃ a : PrimeTuple X k, tupleWord a = w) ∧ endpoint w = N} =
        tupleCount X k ((N : ℤ) - 1) := by
  sorry

end D5.S3.Factorization.Combinatorics.PureAdditivePrimeHistory
