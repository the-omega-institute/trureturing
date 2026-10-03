/- GID: D5/S3/Arith/Primes/FiniteFibonacciRankClosure
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FiniteFibonacciRankClosure
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Fibonacci ranks generate a bounded least prime-support closure. -/

import Mathlib
import D5.S3.Arith.FibonacciRank

namespace D5.S3.Arith.Primes.FiniteFibonacciRankClosure

open D5.S3.Arith.GoldenApparition

/-- The least positive zero index of the original Fibonacci sequence modulo a prime. -/
def rankWitness (p : ℕ) (hp : p.Prime) :
    {r : ℕ // 0 < r ∧ p ∣ Nat.fib r ∧
      ∀ n, 0 < n → p ∣ Nat.fib n → r ≤ n} := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hex : ∃ n : ℕ, 0 < n ∧ p ∣ Nat.fib n := by
    by_cases hp5 : p = 5
    · subst p
      exact ⟨5, by decide, by decide⟩
    have hpNotDvdFive : ¬ p ∣ 5 := by
      intro h
      exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)
    have hentry := (fibonacci_apparition_entry_point hp hpNotDvdFive).1
    have hpOne : 1 ≤ p := hp.one_le
    have hpTwo : 2 ≤ p := hp.two_le
    by_cases heps : legendreSym 5 p = 1
    · refine ⟨p - 1, by omega, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff]
      have hindex : (p : ℤ) - legendreSym 5 p = ((p - 1 : ℕ) : ℤ) := by
        rw [heps]
        omega
      rw [hindex, Int.fib_natCast, Int.cast_natCast] at hentry
      exact hentry
    · have hpModFive : (p : ZMod 5) ≠ 0 := by
        rw [ne_eq, ZMod.natCast_eq_zero_iff]
        intro hFiveDvd
        exact hp5 (((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hFiveDvd).symm)
      have hepsNeg : legendreSym 5 p = -1 :=
        (legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ)) hpModFive).resolve_left heps
      refine ⟨p + 1, by omega, ?_⟩
      rw [← ZMod.natCast_eq_zero_iff]
      have hindex : (p : ℤ) - legendreSym 5 p = ((p + 1 : ℕ) : ℤ) := by
        rw [hepsNeg]
        omega
      rw [hindex, Int.fib_natCast, Int.cast_natCast] at hentry
      exact hentry
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro n hn hz
  exact Nat.find_min' hex ⟨hn, hz⟩

/-- The original Fibonacci entry rank on primes, with value one off the primes. -/
def fibonacciRank (p : ℕ) : ℕ :=
  if hp : p.Prime then (rankWitness p hp).val else 1

/-- Initial small primes together with the prescribed exceptional primes. -/
def rankClosureSeed (S : Finset ℕ) : Finset ℕ := insert 2 (insert 3 (insert 5 S))

/-- Adjoin the prime support of each current member's actual Fibonacci rank. -/
def rankClosureStep (H : Finset ℕ) : Finset ℕ :=
  H ∪ H.biUnion (fun p => (fibonacciRank p).primeFactors)

/-- Iterate the rank-support operation once per prime in the bounded universe. -/
def fibonacciRankClosure (S : Finset ℕ) : Finset ℕ :=
  let B := max 5 (S.sup id)
  let U := (Finset.range (B + 1)).filter Nat.Prime
  rankClosureStep^[U.card] (rankClosureSeed S)

/-- The iterated closure is bounded, stable and least among rank-support closed sets. -/
theorem finite_fibonacci_rank_closure (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ 5 < p) :
    let H := fibonacciRankClosure S
    rankClosureSeed S ⊆ H ∧
    (∀ p ∈ H, p.Prime) ∧
    (∀ p ∈ H, p ≤ max 5 (S.sup id)) ∧
    rankClosureStep H = H ∧
    (∀ K : Finset ℕ, rankClosureSeed S ⊆ K → rankClosureStep K ⊆ K →
      H ⊆ K) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  dsimp only
  let B := max 5 (S.sup id)
  let U := (Finset.range (B + 1)).filter Nat.Prime
  let H0 := rankClosureSeed S
  let V (n : ℕ) := rankClosureStep^[n] H0
  have hB5 : 5 ≤ B := le_max_left 5 _
  have hInit : H0 ⊆ U := by
    intro p hp
    have hpCases : p = 2 ∨ p = 3 ∨ p = 5 ∨ p ∈ S := by
      simpa only [H0, rankClosureSeed, Finset.mem_insert] using hp
    rcases hpCases with h2 | h3 | h5 | hs
    · subst p
      simp only [U, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_two⟩
    · subst p
      simp only [U, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_three⟩
    · subst p
      simp only [U, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Nat.prime_five⟩
    · have hp' := hS p hs
      have hpBound : p ≤ S.sup id := by simpa using (Finset.le_sup (f := id) hs)
      simp only [U, Finset.mem_filter, Finset.mem_range]
      exact ⟨by dsimp [B]; omega, hp'.1⟩
  have hStepBound {A : Finset ℕ} (hAU : A ⊆ U) : rankClosureStep A ⊆ U := by
    intro q hq
    rcases Finset.mem_union.mp hq with hqA | hqNew
    · exact hAU hqA
    · obtain ⟨p, hpA, hqp⟩ := Finset.mem_biUnion.mp hqNew
      have hpU := hAU hpA
      have hpPrime : p.Prime := (Finset.mem_filter.mp hpU).2
      have hpBound : p ≤ B := by
        have hpRange := (Finset.mem_filter.mp hpU).1
        simp only [Finset.mem_range] at hpRange
        omega
      have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hqp
      have hqRank : q ∣ (rankWitness p hpPrime).val := by
        simpa [fibonacciRank, hpPrime] using Nat.dvd_of_mem_primeFactors hqp
      have hqBound : q ≤ B := by
        by_cases hpLarge : 5 < p
        · have hpNeFive : p ≠ 5 := by omega
          have hrdvd := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound
            hpPrime hpNeFive (rankWitness p hpPrime).property.1
            (rankWitness p hpPrime).property.2.1 (rankWitness p hpPrime).property.2.2
          have hqLt : q < p := by
            by_cases heps : legendreSym 5 p = 1
            · have hqDvd : q ∣ p - 1 := dvd_trans hqRank (by simpa [heps] using hrdvd)
              have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hqDvd
              omega
            · have hqDvd : q ∣ p + 1 := dvd_trans hqRank (by simpa [heps] using hrdvd)
              have hle : q ≤ p + 1 := Nat.le_of_dvd (by omega) hqDvd
              have hneP : q ≠ p := by
                intro heq
                subst q
                have hpOne : p ∣ 1 := (Nat.dvd_add_self_left).mp hqDvd
                have hsmall : p ≤ 1 := Nat.le_of_dvd (by decide) hpOne
                omega
              have hnePSucc : q ≠ p + 1 := by
                intro heq
                have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
                have hqOdd : Odd q := hqPrime.odd_of_ne_two (by omega)
                rcases hpOdd with ⟨a, ha⟩
                rcases hqOdd with ⟨b, hb⟩
                omega
              omega
          omega
        · have hcand : ∃ n : ℕ, n ≤ 5 ∧ 0 < n ∧ p ∣ Nat.fib n := by
            have hpTwo : 2 ≤ p := hpPrime.two_le
            interval_cases p
            · exact ⟨3, by decide, by decide, by decide⟩
            · exact ⟨4, by decide, by decide, by decide⟩
            · norm_num at hpPrime
            · exact ⟨5, by decide, by decide, by decide⟩
          obtain ⟨n, hn5, hnpos, hnzero⟩ := hcand
          have hrle : (rankWitness p hpPrime).val ≤ n :=
            (rankWitness p hpPrime).property.2.2 n hnpos hnzero
          have hqle : q ≤ 5 :=
            (Nat.le_of_dvd (rankWitness p hpPrime).property.1 hqRank).trans
            (hrle.trans hn5)
          omega
      simp only [U, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hqPrime⟩
  have hIter (n : ℕ) : V n ⊆ U := by
    induction n with
    | zero => simpa [V] using hInit
    | succ n ih =>
        simpa only [V, Function.iterate_succ_apply'] using hStepBound ih
  have hInc (n : ℕ) : V n ⊆ V (n + 1) := by
    simp only [V, Function.iterate_succ_apply']
    exact Finset.subset_union_left
  have hCardMono : Monotone (fun n => (V n).card) :=
    monotone_nat_of_le_succ (fun n => Finset.card_le_card (hInc n))
  have hCardBound (n : ℕ) : (V n).card ≤ U.card :=
    Finset.card_le_card (hIter n)
  have hCardFlat (n : ℕ) (h : (V n).card = (V (n + 1)).card) :
      (V (n + 1)).card = (V (n + 2)).card := by
    have hEq : V n = V (n + 1) :=
      Finset.eq_of_subset_of_card_le (hInc n) (by omega)
    have hEqNext : V (n + 1) = V (n + 2) := by
      simpa only [V, Function.iterate_succ_apply'] using congrArg rankClosureStep hEq
    exact congrArg Finset.card hEqNext
  have hCardStop : (V (U.card + 1)).card = (V U.card).card :=
    Nat.stabilises_of_monotone hCardMono hCardBound hCardFlat
      (Nat.le_succ U.card)
  have hSetStop : V U.card = V (U.card + 1) :=
    Finset.eq_of_subset_of_card_le (hInc _) (by omega)
  have hFixed : rankClosureStep (V U.card) = V U.card := by
    simpa only [V, Function.iterate_succ_apply'] using hSetStop.symm
  have hClosure : fibonacciRankClosure S = V U.card := by rfl
  rw [hClosure]
  refine ⟨?_, ?_, ?_, hFixed, ?_⟩
  · have h0 (n : ℕ) : H0 ⊆ V n := by
      induction n with
      | zero => simp [V]
      | succ n ih => exact ih.trans (hInc n)
    exact h0 U.card
  · intro p hp
    exact (Finset.mem_filter.mp (hIter U.card hp)).2
  · intro p hp
    have hU := hIter U.card hp
    have hRange := (Finset.mem_filter.mp hU).1
    simp only [Finset.mem_range] at hRange
    dsimp [B] at *
    omega
  · intro K hH0 hKClosed
    have hAll (n : ℕ) : V n ⊆ K := by
      induction n with
      | zero => simpa [V] using hH0
      | succ n ih =>
          have hStep : rankClosureStep (V n) ⊆ rankClosureStep K := by
            intro q hq
            rcases Finset.mem_union.mp hq with hqOld | hqNew
            · exact Finset.mem_union_left _ (ih hqOld)
            · obtain ⟨p, hpOld, hqp⟩ := Finset.mem_biUnion.mp hqNew
              exact Finset.mem_union_right _
                (Finset.mem_biUnion.mpr ⟨p, ih hpOld, hqp⟩)
          simpa only [V, Function.iterate_succ_apply'] using
            hStep.trans hKClosed
    exact hAll U.card
end D5.S3.Arith.Primes.FiniteFibonacciRankClosure
