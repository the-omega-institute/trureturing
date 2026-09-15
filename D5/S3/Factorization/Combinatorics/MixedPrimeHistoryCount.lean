/- GID: D5/S3/Factorization/Combinatorics/MixedPrimeHistoryCount
   generality: G
   mirror-B: D5/B/S3/Factorization/Combinatorics/MixedPrimeHistoryCount
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Typed additive and multiplicative prime histories reach every positive integer and obey finite last-letter counting recurrences. -/

import D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount

open D5.S3.ObserverMemory.Prediction.ControlledBehaviorUniversality

/-- A prime label tagged as addition or multiplication. -/
abbrev PrimeLetter := Sum Nat.Primes Nat.Primes

/-- Add the labelled prime or multiply by it, according to the tag. -/
def primeStep : PrimeLetter → ℕ → ℕ
  | .inl q, n => n + q.val
  | .inr q, n => q.val * n

/-- Execute a typed word from left to right, starting at one. -/
def endpoint (w : List PrimeLetter) : ℕ := runWord primeStep w 1

/-- All typed words whose final state is the specified integer. -/
def historyFibre (n : ℕ) : Set (List PrimeLetter) := {w | endpoint w = n}

/-- The number of distinct typed histories ending at an integer. -/
noncomputable def historyCount (n : ℕ) : ℕ := (historyFibre n).ncard

/-- The number of histories of a specified length and endpoint. -/
noncomputable def lengthCount (k n : ℕ) : ℕ :=
  Nat.card {w : List PrimeLetter // endpoint w = n ∧ w.length = k}

/-- Every positive integer is reached by a nonempty finite set of typed histories. -/
set_option maxHeartbeats 800000 in
theorem reachable_finite (n : ℕ) (hn : 0 < n) :
    (historyFibre n).Nonempty ∧ (historyFibre n).Finite := by
  sorry

/-- Splitting at the last typed letter gives the total history recurrence. -/
set_option maxHeartbeats 800000 in
theorem history_recurrence (n : ℕ) (hn : 2 ≤ n) :
    historyCount n =
      (∑ q ∈ (Finset.range n).filter Nat.Prime, historyCount (n - q)) +
      (∑ q ∈ n.primeFactors, historyCount (n / q)) := by
  sorry

/-- Splitting at the last typed letter decreases the specified length by one. -/
set_option maxHeartbeats 800000 in
theorem length_recurrence (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    lengthCount k n =
      (∑ q ∈ (Finset.range n).filter Nat.Prime, lengthCount (k - 1) (n - q)) +
      (∑ q ∈ n.primeFactors, lengthCount (k - 1) (n / q)) := by
  sorry

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
