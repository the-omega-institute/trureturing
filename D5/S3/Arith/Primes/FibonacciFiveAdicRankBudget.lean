/- GID: D5/S3/Arith/Primes/FibonacciFiveAdicRankBudget
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciFiveAdicRankBudget
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd Fibonacci support bounds five-adic index depth by the rank lcm plus one. -/

import D5.S3.Arith.Primes.FibonacciOddTwentyfiveNonsquare
import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget

open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciOddTwentyfiveNonsquare
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- Odd prime support of a Fibonacci value bounds the five-adic depth of
its index by one more than the rank lcm of that support. -/
theorem fibonacci_five_adic_rank_budget (H : Finset ℕ) (n : ℕ)
    (hH : ∀ p ∈ H, p.Prime) (_hFive : 5 ∈ H) (_hn : 0 < n)
    (hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
    (hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H) :
    padicValNat 5 n ≤ padicValNat 5 (H.lcm fibonacciRank) + 1 := by
  let R := H.lcm fibonacciRank
  let a := padicValNat 5 R
  let e := padicValNat 5 n
  have hRpos : 0 < R := by
    apply Nat.pos_of_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro p hp
    simp only [fibonacciRank, hH p hp, dite_true]
    exact (rankWitness p (hH p hp)).property.1.ne'
  by_contra hBound
  change ¬ e ≤ a + 1 at hBound
  have heLarge : a + 2 ≤ e := by omega
  have heIndex : 5 ^ e ∣ n := pow_padicValNat_dvd
  let M := 5 ^ a
  let N := 5 ^ (a + 2)
  have hMpos : 0 < M := pow_pos (by decide) _
  have hNpos : 0 < N := pow_pos (by decide) _
  have hMN : 25 * M = N := by
    dsimp [M, N]
    rw [pow_add]
    norm_num
    ring
  have hModd : Odd M := (by decide : Odd (5 : ℕ)).pow
  obtain ⟨d, hTwentyfive, _, hdNonsquare⟩ :=
    fibonacci_odd_twentyfive_normalized_nonsquare M hMpos hModd
  have hProduct : Nat.fib N = 25 * Nat.fib M * d := by
    simpa only [hMN] using hTwentyfive
  have hFMpos : 0 < Nat.fib M := Nat.fib_pos.mpr hMpos
  have hFNpos : 0 < Nat.fib N := Nat.fib_pos.mpr hNpos
  have hdpos : 0 < d := by
    by_contra hnot
    have hd0 : d = 0 := by omega
    rw [hd0] at hProduct
    simp at hProduct
    omega
  have hFiveM : padicValNat 5 (Nat.fib M) = a := by
    rw [D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth M hMpos]
    simp [M]
  have hFiveN : padicValNat 5 (Nat.fib N) = a + 2 := by
    rw [D5.S3.Arith.Primes.FibonacciFiveAdicDepth.fibonacci_five_adic_depth N hNpos]
    simp [N]
  have hFiveTwentyfive : padicValNat 5 25 = 2 := by
    rw [show (25 : ℕ) = 5 ^ 2 by norm_num, padicValNat.pow, padicValNat_self]
  have hFiveProduct : padicValNat 5 (Nat.fib N) =
      padicValNat 5 25 + padicValNat 5 (Nat.fib M) + padicValNat 5 d := by
    rw [hProduct, padicValNat.mul (mul_ne_zero (by decide : (25 : ℕ) ≠ 0)
      hFMpos.ne') hdpos.ne',
      padicValNat.mul (by decide : (25 : ℕ) ≠ 0) hFMpos.ne']
  have hFiveD : padicValNat 5 d = 0 := by
    rw [hFiveN, hFiveTwentyfive, hFiveM] at hFiveProduct
    omega
  have hOddPrime : ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Odd (padicValNat p d) := by
    by_contra hNone
    have hEven (p : ℕ) (hp : p ∈ d.primeFactors) :
        Even (d.factorization p) := by
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpDiv := Nat.dvd_of_mem_primeFactors hp
      have hpNotOdd : ¬ Odd (padicValNat p d) := by
        intro hpOdd
        exact hNone ⟨p, hpPrime, hpDiv, hpOdd⟩
      rw [Nat.factorization_def d hpPrime]
      exact Nat.not_odd_iff_even.mp hpNotOdd
    let s := ∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2)
    have hSquare : d = s ^ 2 := by
      rw [Nat.prod_primeFactors_pow_factorization hdpos.ne']
      dsimp only [s]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      obtain ⟨k, hk⟩ := hEven p hp
      omega
    exact hdNonsquare ⟨s, by simpa [pow_two] using hSquare⟩
  obtain ⟨p, hpPrime, hpD, hpOddD⟩ := hOddPrime
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpNotFive : p ≠ 5 := by
    intro heq
    subst p
    have hPositive := one_le_padicValNat_of_dvd hdpos.ne' hpD
    omega
  have hpNotPow (k : ℕ) : ¬ p ∣ 5 ^ k := by
    intro hpPow
    have hpFive : p ∣ 5 := hpPrime.dvd_of_dvd_pow hpPow
    exact hpNotFive ((Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_five).mp hpFive)
  have hpNotTwentyfive : ¬ p ∣ 25 := by
    simpa only [show (25 : ℕ) = 5 ^ 2 by norm_num] using hpNotPow 2
  have hpTwentyfiveVal : padicValNat p 25 = 0 :=
    padicValNat.eq_zero_of_not_dvd hpNotTwentyfive
  have hpFN : p ∣ Nat.fib N := by
    rw [hProduct]
    exact dvd_mul_of_dvd_right hpD _
  have hPProduct : padicValNat p (Nat.fib N) =
      padicValNat p (Nat.fib M) + padicValNat p d := by
    calc
      padicValNat p (Nat.fib N) = padicValNat p (25 * Nat.fib M * d) := by
        rw [hProduct]
      _ = (padicValNat p 25 + padicValNat p (Nat.fib M)) +
          padicValNat p d := by
        rw [padicValNat.mul (mul_ne_zero (by decide : (25 : ℕ) ≠ 0)
          hFMpos.ne') hdpos.ne',
          padicValNat.mul (by decide : (25 : ℕ) ≠ 0) hFMpos.ne']
      _ = _ := by rw [hpTwentyfiveVal]; omega
  let r := rankWitness p hpPrime
  have hrDivN : r.val ∣ N :=
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      r.property.1 r.property.2.1 r.property.2.2).mp hpFN
  obtain ⟨j, hjLe, hjEq⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hrDivN
  have hjLarge : a < j := by
    by_contra hnot
    have hjSmall : j ≤ a := by omega
    have hrDivM : r.val ∣ M := by
      rw [hjEq]
      exact pow_dvd_pow 5 hjSmall
    have hpFM : p ∣ Nat.fib M :=
      (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
        r.property.1 r.property.2.1 r.property.2.2).mpr hrDivM
    have hValN := fibonacci_original_rank_valuation p N hpPrime hpFN
      (hpNotPow (a + 2))
    have hValM := fibonacci_original_rank_valuation p M hpPrime hpFM
      (hpNotPow a)
    have hSame : padicValNat p (Nat.fib N) = padicValNat p (Nat.fib M) :=
      hValN.trans hValM.symm
    have hDpositive := one_le_padicValNat_of_dvd hdpos.ne' hpD
    omega
  have hrEq : fibonacciRank p = 5 ^ j := by
    simpa only [fibonacciRank, hpPrime, dite_true, r] using hjEq
  have hpNotH : p ∉ H := by
    intro hpH
    have hrR : fibonacciRank p ∣ R := Finset.dvd_lcm hpH
    rw [hrEq] at hrR
    have hjSmall : j ≤ a :=
      (padicValNat_dvd_iff_le (p := 5) hRpos.ne').mp hrR
    omega
  have hpNotFM : ¬ p ∣ Nat.fib M := by
    intro hpFM
    have hrDivM : r.val ∣ M :=
      (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
        r.property.1 r.property.2.1 r.property.2.2).mp hpFM
    rw [hjEq] at hrDivM
    have hjSmall : j ≤ a :=
      (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (5 : ℕ))).mp hrDivM
    omega
  have hValFM : padicValNat p (Nat.fib M) = 0 :=
    padicValNat.eq_zero_of_not_dvd hpNotFM
  have hValFN : padicValNat p (Nat.fib N) = padicValNat p d := by
    simpa only [hValFM, zero_add] using hPProduct
  have hNIndex : N ∣ n :=
    (pow_dvd_pow 5 heLarge).trans heIndex
  have hpFibN : p ∣ Nat.fib n :=
    hpFN.trans (Nat.fib_dvd N n hNIndex)
  have hpNotIndex : ¬ p ∣ n := by
    intro hpIndex
    exact hpNotH (hIndex p hpPrime hpIndex)
  have hValIndex := fibonacci_original_rank_valuation p n hpPrime hpFibN hpNotIndex
  have hValN := fibonacci_original_rank_valuation p N hpPrime hpFN
    (hpNotPow (a + 2))
  have hOddIndex : Odd (padicValNat p (Nat.fib n)) := by
    rw [hValIndex, ← hValN, hValFN]
    exact hpOddD
  exact hpNotH (hOdd p hpPrime hpFibN hOddIndex)

#print axioms fibonacci_five_adic_rank_budget

end D5.S3.Arith.Primes.FibonacciFiveAdicRankBudget
