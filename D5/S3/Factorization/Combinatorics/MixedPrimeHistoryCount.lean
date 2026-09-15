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

set_option maxHeartbeats 800000 in
/-- Every positive integer is reached by a nonempty finite set of typed histories. -/
theorem reachable_finite (n : ℕ) (hn : 0 < n) :
    (historyFibre n).Nonempty ∧ (historyFibre n).Finite := by
  classical
  let label : PrimeLetter → ℕ := Sum.elim Subtype.val Subtype.val
  have growth (a : PrimeLetter) (m : ℕ) (hm : 0 < m) :
      m + 1 ≤ primeStep a m ∧ label a ≤ primeStep a m := by
    cases a with
    | inl q =>
        have hq := q.property.two_le
        change m + 1 ≤ m + q.val ∧ q.val ≤ m + q.val
        omega
    | inr q =>
        have hq := q.property.two_le
        change m + 1 ≤ q.val * m ∧ q.val ≤ q.val * m
        constructor <;> nlinarith
  have bounds (w : List PrimeLetter) (m : ℕ) (hm : 0 < m) :
      m + w.length ≤ runWord primeStep w m ∧
      ∀ a ∈ w, label a ≤ runWord primeStep w m := by
    induction w generalizing m with
    | nil => simp [runWord]
    | cons a w ih =>
        have hg := growth a m hm
        have hi := ih (primeStep a m) (by omega)
        simp only [runWord, List.length_cons]
        constructor
        · omega
        · intro b hb
          rcases List.mem_cons.mp hb with rfl | hb
          · omega
          · exact hi.2 b hb
  have append_run (u v : List PrimeLetter) (m : ℕ) :
      runWord primeStep (u ++ v) m = runWord primeStep v (runWord primeStep u m) := by
    induction u generalizing m with
    | nil => rfl
    | cons a u ih => simpa only [List.cons_append, runWord] using ih (primeStep a m)
  have reachable (n : ℕ) (hn : 0 < n) : (historyFibre n).Nonempty := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases h1 : n = 1
        · subst n; exact ⟨[], rfl⟩
        by_cases h2 : n = 2
        · subst n; exact ⟨[.inr ⟨2, Nat.prime_two⟩], rfl⟩
        have hsub : 0 < n - 2 := by omega
        obtain ⟨w, hw⟩ := ih (n-2) (by omega) hsub
        refine ⟨w ++ [.inl ⟨2, Nat.prime_two⟩], ?_⟩
        change runWord primeStep (w ++ [.inl ⟨2, Nat.prime_two⟩]) 1 = n
        rw [append_run]
        change endpoint w + 2 = n
        change endpoint w = n-2 at hw
        omega
  refine ⟨reachable n hn, ?_⟩
  let smallPrimes : Set Nat.Primes := {q | q.val ≤ n}
  have smallFinite : smallPrimes.Finite :=
    Set.Finite.preimage Subtype.val_injective.injOn (Set.finite_le_nat n)
  let : Fintype smallPrimes := smallFinite.fintype
  let alphabet := Sum smallPrimes smallPrimes
  let forget : alphabet → PrimeLetter := Sum.map Subtype.val Subtype.val
  have boundedWords := List.finite_length_le alphabet n
  apply (boundedWords.image (List.map forget)).subset
  intro w hw
  have he : endpoint w = n := hw
  have hb := bounds w 1 (by omega)
  change 1 + w.length ≤ endpoint w ∧ (∀ a ∈ w, label a ≤ endpoint w) at hb
  rw [he] at hb
  let lift : {a // a ∈ w} → alphabet := fun a =>
    match h : a.val with
    | .inl q => .inl ⟨q, by have hl := hb.2 a.val a.property; rw [h] at hl; exact hl⟩
    | .inr q => .inr ⟨q, by have hl := hb.2 a.val a.property; rw [h] at hl; exact hl⟩
  refine ⟨w.attach.map lift, ?_, ?_⟩
  · change (w.attach.map lift).length ≤ n
    simpa using (show w.length ≤ n by omega)
  · rw [List.map_map]
    have hf : (fun a : {a // a ∈ w} => forget (lift a)) = Subtype.val := by
      funext a
      simp only [lift, forget]
      split <;> simp_all
    simp only [Function.comp_def, hf, List.attach_map_subtype_val]

set_option maxHeartbeats 800000 in
/-- Splitting at the last typed letter gives the total history recurrence. -/
theorem history_recurrence (n : ℕ) (hn : 2 ≤ n) :
    historyCount n =
      (∑ q ∈ (Finset.range n).filter Nat.Prime, historyCount (n - q)) +
      (∑ q ∈ n.primeFactors, historyCount (n / q)) := by
  sorry

set_option maxHeartbeats 800000 in
/-- Splitting at the last typed letter decreases the specified length by one. -/
theorem length_recurrence (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    lengthCount k n =
      (∑ q ∈ (Finset.range n).filter Nat.Prime, lengthCount (k - 1) (n - q)) +
      (∑ q ∈ n.primeFactors, lengthCount (k - 1) (n / q)) := by
  sorry

end D5.S3.Factorization.Combinatorics.MixedPrimeHistoryCount
