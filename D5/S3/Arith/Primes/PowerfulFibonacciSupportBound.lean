/- GID: D5/S3/Arith/Primes/PowerfulFibonacciSupportBound
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/PowerfulFibonacciSupportBound
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Original odd-depth support bounds powerful Fibonacci indices. -/

import D5.S3.Arith.Primes.OriginalOddDepthSupport
import D5.S3.Arith.Powerful.PowerfulNumber

namespace D5.S3.Arith.Primes.PowerfulFibonacciSupportBound

open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.OriginalOddDepthSupport
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
open D5.S3.Arith.Powerful.PowerfulNumber

/-- Prime support occurring to odd multiplicity in the original Fibonacci value. -/
def oddPrimeSupport (n : ℕ) : Finset ℕ :=
  (Nat.fib n).primeFactors.filter
    (fun p => Odd (padicValNat p (Nat.fib n)))

/-- Positive powerful Fibonacci indices whose odd original depths above two lie in `S`. -/
def supportedPowerfulIndex (S : Finset ℕ) (n : ℕ) : Prop :=
  0 < n ∧ Powerful (Nat.fib n) ∧
    ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib (fibonacciRank p))) →
      3 ≤ padicValNat p (Nat.fib (fibonacciRank p)) → p ∈ S

private theorem finite_support_exception_budget
    (H B E : Finset ℕ) (K : ℕ → Finset ℕ) (Good : ℕ → Prop)
    (hBH : B ⊆ H) (hBcard : B.card = 3) (hEcard : E.card = 4)
    (hSupport : ∀ n, Good n → K n ⊆ H)
    (hSmall : ∀ n, Good n → K n ⊆ B → n ∈ E)
    (hUnique : ∀ n m, Good n → Good m → ¬ K n ⊆ B → K n = K m → n = m) :
    ∃ A : Finset ℕ, (∀ n, n ∈ A ↔ Good n) ∧ A.card ≤ 2 ^ H.card - 4 := by
  classical
  let G : Set ℕ := {n | Good n}
  let Gsmall : Set ℕ := {n | Good n ∧ K n ⊆ B}
  let Glarge : Set ℕ := {n | Good n ∧ ¬ K n ⊆ B}
  have hSmallFinite : Gsmall.Finite :=
    E.finite_toSet.subset (by
      intro n hn
      exact hSmall n hn.1 hn.2)
  have hLargeImage : (K '' Glarge).Finite :=
    (H.powerset).finite_toSet.subset (by
      rintro k ⟨n, hn, rfl⟩
      exact Finset.mem_powerset.mpr (hSupport n hn.1))
  have hLargeInj : Set.InjOn K Glarge := by
    intro n hn m hm hnm
    exact hUnique n m hn.1 hm.1 hn.2 hnm
  have hLargeFinite : Glarge.Finite :=
    Set.Finite.of_finite_image hLargeImage hLargeInj
  have hGFinite : G.Finite :=
    (hSmallFinite.union hLargeFinite).subset (by
      intro n hn
      by_cases h : K n ⊆ B
      · exact Or.inl ⟨hn, h⟩
      · exact Or.inr ⟨hn, h⟩)
  let A := hGFinite.toFinset
  have hA (n : ℕ) : n ∈ A ↔ Good n := by
    simp [A, G]
  let As := A.filter (fun n => K n ⊆ B)
  let Al := A.filter (fun n => ¬ K n ⊆ B)
  have hAsSubset : As ⊆ E := by
    intro n hn
    have hnf := Finset.mem_filter.mp hn
    exact hSmall n ((hA n).mp hnf.1) hnf.2
  have hAsCard : As.card ≤ 4 := by
    rw [← hEcard]
    exact Finset.card_le_card hAsSubset
  have hAlMaps : Set.MapsTo K (Al : Set ℕ)
      ((H.powerset \ B.powerset : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro n hn
    have hnf := Finset.mem_filter.mp hn
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_powerset.mpr (hSupport n ((hA n).mp hnf.1)),
        fun hsmall => hnf.2 (Finset.mem_powerset.mp hsmall)⟩
  have hAlInj : Set.InjOn K (Al : Set ℕ) := by
    intro n hn m hm hnm
    have hnn := Finset.mem_filter.mp hn
    have hmn := Finset.mem_filter.mp hm
    exact hUnique n m ((hA n).mp hnn.1) ((hA m).mp hmn.1) hnn.2 hnm
  have hAlCard : Al.card ≤ (H.powerset \ B.powerset).card :=
    Finset.card_le_card_of_injOn K hAlMaps hAlInj
  have hPowerSubset : B.powerset ⊆ H.powerset :=
    Finset.powerset_mono.mpr hBH
  have hPowerB : B.powerset.card = 8 := by
    rw [Finset.card_powerset, hBcard]
    decide
  have hPowerH : H.powerset.card = 2 ^ H.card := Finset.card_powerset H
  have hEight : 8 ≤ 2 ^ H.card := by
    rw [← hPowerB, ← hPowerH]
    exact Finset.card_le_card hPowerSubset
  have hSlots : (H.powerset \ B.powerset).card = 2 ^ H.card - 8 := by
    rw [Finset.card_sdiff_of_subset hPowerSubset, hPowerH, hPowerB]
  have hPartition : As.card + Al.card = A.card := by
    exact Finset.card_filter_add_card_filter_not (fun n => K n ⊆ B)
  refine ⟨A, hA, ?_⟩
  rw [← hPartition]
  rw [hSlots] at hAlCard
  omega

/-- Assuming the prime-index, five-smooth classification, and square-class
premises, the supported powerful indices form a set of at most
`2 ^ |H(S)| - 4` elements. -/
theorem powerful_fibonacci_support_bound
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 < p)
    (hBlock : ∀ n, PrimeIndexOddFactor n)
    (hFiveSmooth : ∀ n, 0 < n → Powerful (Nat.fib n) →
      (∀ p, p.Prime → p ∣ n → p ≤ 5) →
      n ∈ ({1, 2, 6, 12} : Finset ℕ))
    (hSquareUnique : ∀ n m, 0 < n → 0 < m →
      ¬ oddPrimeSupport n ⊆ ({2, 3, 5} : Finset ℕ) →
      oddPrimeSupport n = oddPrimeSupport m → n = m) :
    ∃ A : Finset ℕ,
      (∀ n, n ∈ A ↔ supportedPowerfulIndex S n) ∧
      A.card ≤ 2 ^ (fibonacciRankClosure S).card - 4 := by
  classical
  let B : Finset ℕ := {2, 3, 5}
  let E : Finset ℕ := {1, 2, 6, 12}
  let H := fibonacciRankClosure S
  have hBH : B ⊆ H := by
    intro p hp
    have hSeed := (finite_fibonacci_rank_closure S hS).1
    have hpCases : p = 2 ∨ p = 3 ∨ p = 5 := by
      simpa [B] using hp
    rcases hpCases with h2 | h3 | h5
    · exact hSeed (by simp [rankClosureSeed, h2])
    · exact hSeed (by simp [rankClosureSeed, h3])
    · exact hSeed (by simp [rankClosureSeed, h5])
  have hHPrime : ∀ p ∈ H, p.Prime :=
    (finite_fibonacci_rank_closure S hS).2.1
  have hSupport : ∀ n, supportedPowerfulIndex S n → oddPrimeSupport n ⊆ H := by
    intro n hn p hpK
    rcases hn with ⟨hnpos, hpower, hT⟩
    have hExternal : ∀ q : ℕ, q.Prime → 5 < q → q ∣ Nat.fib n → ¬ q ∣ n →
        Odd (padicValNat q (Nat.fib (fibonacciRank q))) → q ∈ S := by
      intro q hq hq5 hqFib hqN hqOdd
      have : Fact q.Prime := ⟨hq⟩
      have hFib0 : Nat.fib n ≠ 0 := (Nat.fib_pos.mpr hnpos).ne'
      have hDepthTwo : 2 ≤ padicValNat q (Nat.fib n) :=
        (padicValNat_dvd_iff_le (p := q) (n := 2) hFib0).mp
          (hpower.2 q hq hqFib)
      have hDepthThree : 3 ≤ padicValNat q (Nat.fib (fibonacciRank q)) := by
        have hOddN : Odd (padicValNat q (Nat.fib n)) := by
          rw [fibonacci_original_rank_valuation q n hq hqFib hqN]
          exact hqOdd
        rw [← fibonacci_original_rank_valuation q n hq hqFib hqN]
        rcases hOddN with ⟨k, hk⟩
        omega
      exact hT q hq hq5 hqFib hqOdd hDepthThree
    have hKernel := (original_odd_depth_support S hS n hnpos
      (hBlock n) hExternal).2
    have hpDvdK : p ∣ oddDepthKernel n := by
      change p ∣ (oddPrimeSupport n).prod id
      exact Finset.dvd_prod_of_mem id hpK
    have hpPrime : p.Prime :=
      (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpK).1).1
    obtain ⟨q, hqH, hpDvdQ⟩ :=
      (hpPrime.prime.dvd_finsetProd_iff id).mp (hpDvdK.trans hKernel)
    have hpEqQ := (Nat.prime_dvd_prime_iff_eq hpPrime (hHPrime q hqH)).mp hpDvdQ
    simpa [hpEqQ] using hqH
  have hSmall : ∀ n, supportedPowerfulIndex S n → oddPrimeSupport n ⊆ B → n ∈ E := by
    intro n hn hKSmall
    rcases hn with ⟨hnpos, hpower, _⟩
    have hExternalEmpty : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
        Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ (∅ : Finset ℕ) := by
      intro p hp hp5 hpFib hpN hpOdd
      have hOddN : Odd (padicValNat p (Nat.fib n)) := by
        rw [fibonacci_original_rank_valuation p n hp hpFib hpN]
        exact hpOdd
      have hpK : p ∈ oddPrimeSupport n := by
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_primeFactors.mpr ⟨hp, hpFib, (Nat.fib_pos.mpr hnpos).ne'⟩, hOddN⟩
      have hpCases : p = 2 ∨ p = 3 ∨ p = 5 := by
        simpa [B] using hKSmall hpK
      omega
    have hIndexSupport :=
      (original_odd_depth_support ∅ (by simp) n hnpos
        (hBlock n) hExternalEmpty).1
    have hIndexSmall : ∀ p, p.Prime → p ∣ n → p ≤ 5 := by
      intro p hp hpN
      have hpH := hIndexSupport p hp hpN
      have hpBound := (finite_fibonacci_rank_closure ∅ (by simp)).2.2.1 p hpH
      simpa using hpBound
    exact hFiveSmooth n hnpos hpower hIndexSmall
  have hBudget := finite_support_exception_budget H B E oddPrimeSupport
    (supportedPowerfulIndex S) hBH (by decide) (by decide) hSupport hSmall
    (by
      intro n m hn hm hlarge hsame
      exact hSquareUnique n m hn.1 hm.1 hlarge hsame)
  simpa only [H] using hBudget

#print axioms powerful_fibonacci_support_bound

end D5.S3.Arith.Primes.PowerfulFibonacciSupportBound
