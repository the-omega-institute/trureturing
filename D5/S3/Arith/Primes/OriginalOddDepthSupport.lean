/- GID: D5/S3/Arith/Primes/OriginalOddDepthSupport
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/OriginalOddDepthSupport
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd original depth bounds both Fibonacci index and squarefree-kernel support. -/

import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

namespace D5.S3.Arith.Primes.OriginalOddDepthSupport

open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

/-- A prime-index block contributes an odd-depth factor. This is the explicit
classical nonsquare input to the support descent. -/
def PrimeIndexOddFactor (n : ℕ) : Prop :=
  ∀ ell : ℕ, ell.Prime → 5 < ell → ell ∣ n →
    ∃ p : ℕ, p.Prime ∧ p ∣ Nat.fib ell ∧ Odd (padicValNat p (Nat.fib ell))

/-- The product of the prime factors occurring to odd multiplicity in F_n. -/
def oddDepthKernel (n : ℕ) : ℕ :=
  ((Nat.fib n).primeFactors.filter
    (fun p => Odd (padicValNat p (Nat.fib n)))).prod id

/-- The largest prime dividing an index outside the rank closure leads to an
external odd-original-depth factor. -/
private theorem support_descent_core
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 < p)
    (n : ℕ) (hn : 0 < n) (hBlock : PrimeIndexOddFactor n)
    (hExternal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
      Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ S) :
    ∀ ell : ℕ, ell.Prime → ell ∣ n → ell ∈ fibonacciRankClosure S := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let H := fibonacciRankClosure S
  have hSeed : rankClosureSeed S ⊆ H :=
    (finite_fibonacci_rank_closure S hS).1
  have hFixed : rankClosureStep H = H :=
    (finite_fibonacci_rank_closure S hS).2.2.2.1
  let A := n.primeFactors.filter (fun p => p ∉ H)
  by_contra h
  push Not at h
  obtain ⟨r, hrPrime, hrDiv, hrOut⟩ := h
  have hrA : r ∈ A := by
    simp only [A, Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hrPrime, hrDiv, hn.ne'⟩, hrOut⟩
  have hA : A.Nonempty := ⟨r, hrA⟩
  let ell := A.max' hA
  have hEllA : ell ∈ A := Finset.max'_mem A hA
  have hEllPrime : ell.Prime := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hEllA).1).1
  have hEllDiv : ell ∣ n := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hEllA).1).2.1
  have hEllOut : ell ∉ H := (Finset.mem_filter.mp hEllA).2
  have hEllLarge : 5 < ell := by
    by_contra hnot
    have hsmall : ell = 2 ∨ ell = 3 ∨ ell = 5 := by
      have htwo := hEllPrime.two_le
      have hneFour : ell ≠ 4 := by
        intro heq
        rw [heq] at hEllPrime
        norm_num at hEllPrime
      omega
    rcases hsmall with h2 | h3 | h5
    · exact (hEllOut (hSeed (by simp [rankClosureSeed, h2]))).elim
    · exact (hEllOut (hSeed (by simp [rankClosureSeed, h3]))).elim
    · exact (hEllOut (hSeed (by simp [rankClosureSeed, h5]))).elim
  obtain ⟨p, hpPrime, hpFibEll, hpOdd⟩ :=
    hBlock ell hEllPrime hEllLarge hEllDiv
  let rank := rankWitness p hpPrime
  have hRankPos : 0 < rank.val := rank.property.1
  have hRankZero : p ∣ Nat.fib rank.val := rank.property.2.1
  have hRankMin : ∀ k, 0 < k → p ∣ Nat.fib k → rank.val ≤ k :=
    rank.property.2.2
  have hRankDiv : rank.val ∣ ell :=
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      hRankPos hRankZero hRankMin).mp hpFibEll
  have hRankTwo : 2 ≤ rank.val := by
    by_contra hlt
    have hOne : rank.val = 1 := by omega
    have hpOne : p ∣ 1 := by simpa [hOne] using hRankZero
    exact hpPrime.ne_one (Nat.dvd_one.mp hpOne)
  have hRankEq : rank.val = ell :=
    (Nat.dvd_prime_two_le hEllPrime hRankTwo).mp hRankDiv
  have hFibRank : fibonacciRank p = ell := by
    simpa [fibonacciRank, hpPrime, rank] using hRankEq
  have hpNeFive : p ≠ 5 := by
    intro hpFive
    subst p
    have hle : rank.val ≤ 5 := hRankMin 5 (by decide) (by decide)
    omega
  have hRankBound := D5.S3.Arith.FibonacciRank.fibonacci_rank_dvd_prime_bound
    hpPrime hpNeFive hRankPos hRankZero hRankMin
  rw [hRankEq] at hRankBound
  have hpLarge : ell < p := by
    have hpTwo : 2 ≤ p := hpPrime.two_le
    by_cases heps : legendreSym 5 p = 1
    · have hdvd : ell ∣ p - 1 := by simpa [heps] using hRankBound
      have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hdvd
      omega
    · have hdvd : ell ∣ p + 1 := by simpa [heps] using hRankBound
      have hle : ell ≤ p + 1 := Nat.le_of_dvd (by omega) hdvd
      have hne : p ≠ ell := by
        intro heq
        have hEllDvd : ell ∣ ell + 1 := by simpa [heq] using hdvd
        have hOne : ell ∣ 1 := (Nat.dvd_add_self_left).mp hEllDvd
        have hsmall : ell ≤ 1 := Nat.le_of_dvd (by decide) hOne
        omega
      have hpOdd : Odd p := hpPrime.odd_of_ne_two (by omega)
      have hEllOdd : Odd ell := hEllPrime.odd_of_ne_two (by omega)
      rcases hpOdd with ⟨a, ha⟩
      rcases hEllOdd with ⟨b, hb⟩
      omega
  have hpFive : 5 < p := by omega
  have hpFibN : p ∣ Nat.fib n :=
    hpFibEll.trans (Nat.fib_dvd ell n hEllDiv)
  have hpNotDivN : ¬ p ∣ n := by
    intro hpDivN
    have hpH : p ∈ H := by
      by_contra hpOut
      have hpA : p ∈ A := by
        simp only [A, Finset.mem_filter, Nat.mem_primeFactors]
        exact ⟨⟨hpPrime, hpDivN, hn.ne'⟩, hpOut⟩
      have hle : p ≤ ell := Finset.le_max' A p hpA
      omega
    have hEllFactor : ell ∈ (fibonacciRank p).primeFactors := by
      rw [hFibRank]
      exact Nat.mem_primeFactors.mpr ⟨hEllPrime, dvd_refl _, by omega⟩
    have hEllStep : ell ∈ rankClosureStep H := by
      exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨p, hpH, hEllFactor⟩)
    rw [hFixed] at hEllStep
    exact hEllOut hEllStep
  have hpOddRank : Odd (padicValNat p (Nat.fib (fibonacciRank p))) := by
    rw [hFibRank]
    exact hpOdd
  have hpS := hExternal p hpPrime hpFive hpFibN hpNotDivN hpOddRank
  have hpH : p ∈ H := hSeed (by simp [rankClosureSeed, hpS])
  have hEllFactor : ell ∈ (fibonacciRank p).primeFactors := by
    rw [hFibRank]
    exact Nat.mem_primeFactors.mpr ⟨hEllPrime, dvd_refl _, by omega⟩
  have hEllStep : ell ∈ rankClosureStep H := by
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨p, hpH, hEllFactor⟩)
  rw [hFixed] at hEllStep
  exact hEllOut hEllStep

/-- Odd original depth outside a prescribed finite set controls both the
index support and the squarefree kernel of the original Fibonacci value. -/
theorem original_odd_depth_support
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 5 < p)
    (n : ℕ) (hn : 0 < n) (hBlock : PrimeIndexOddFactor n)
    (hExternal : ∀ p : ℕ, p.Prime → 5 < p → p ∣ Nat.fib n → ¬ p ∣ n →
      Odd (padicValNat p (Nat.fib (fibonacciRank p))) → p ∈ S) :
    let H := fibonacciRankClosure S
    (∀ ell : ℕ, ell.Prime → ell ∣ n → ell ∈ H) ∧
    oddDepthKernel n ∣ H.prod id := by
  dsimp only
  have hSupport := support_descent_core S hS n hn hBlock hExternal
  refine ⟨hSupport, ?_⟩
  unfold oddDepthKernel
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  have hpFactor := Finset.mem_filter.mp hp
  have hpPrime : p.Prime := (Nat.mem_primeFactors.mp hpFactor.1).1
  have hpFib : p ∣ Nat.fib n := (Nat.mem_primeFactors.mp hpFactor.1).2.1
  have hpOdd := hpFactor.2
  have hSeed : rankClosureSeed S ⊆ fibonacciRankClosure S :=
    (finite_fibonacci_rank_closure S hS).1
  by_cases hpSmall : p ≤ 5
  · have hpCases : p = 2 ∨ p = 3 ∨ p = 5 := by
      have hpTwo := hpPrime.two_le
      have hpNeFour : p ≠ 4 := by
        intro heq
        rw [heq] at hpPrime
        norm_num at hpPrime
      omega
    rcases hpCases with h2 | h3 | h5
    · exact hSeed (by simp [rankClosureSeed, h2])
    · exact hSeed (by simp [rankClosureSeed, h3])
    · exact hSeed (by simp [rankClosureSeed, h5])
  · have hpLarge : 5 < p := by omega
    by_cases hpIndex : p ∣ n
    · exact hSupport p hpPrime hpIndex
    · have hpOriginal : Odd (padicValNat p (Nat.fib (fibonacciRank p))) := by
        rw [← fibonacci_original_rank_valuation p n hpPrime hpFib hpIndex]
        exact hpOdd
      have hpS := hExternal p hpPrime hpLarge hpFib hpIndex hpOriginal
      exact hSeed (by simp [rankClosureSeed, hpS])

end D5.S3.Arith.Primes.OriginalOddDepthSupport
