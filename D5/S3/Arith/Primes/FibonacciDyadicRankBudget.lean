/- GID: D5/S3/Arith/Primes/FibonacciDyadicRankBudget
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciDyadicRankBudget
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd Fibonacci support bounds dyadic index depth by ranks in finite prime support. -/

import D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

namespace D5.S3.Arith.Primes.FibonacciDyadicRankBudget

open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

/-- The two-adic depth of an index is bounded by the least common multiple of
the Fibonacci ranks in its prescribed prime support, provided that support
also contains every prime occurring to odd order in its Fibonacci number. -/
theorem fibonacci_dyadic_rank_budget (H : Finset ℕ) (n : ℕ)
    (hH : ∀ p ∈ H, p.Prime) (hThree : 3 ∈ H) (hn : 0 < n)
    (hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
    (hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H) :
    padicValNat 2 n ≤ padicValNat 2 (H.lcm fibonacciRank) := by
  let R := H.lcm fibonacciRank
  let e := padicValNat 2 n
  have hThreeEntry (m : ℕ) : 3 ∣ Nat.fib m ↔ 4 ∣ m := by
    apply D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      (by decide : 0 < 4) (by decide : 3 ∣ Nat.fib 4)
    intro j hj hFib
    by_contra hle
    have hjSmall : j = 1 ∨ j = 2 ∨ j = 3 := by omega
    rcases hjSmall with rfl | rfl | rfl <;> norm_num at hFib
  have hRankThree : fibonacciRank 3 = 4 := by
    let r := rankWitness 3 Nat.prime_three
    have hrDiv : 4 ∣ r.val := (hThreeEntry r.val).mp r.property.2.1
    have hrLe : r.val ≤ 4 := r.property.2.2 4 (by decide) (by decide)
    have hrEq : r.val = 4 :=
      Nat.le_antisymm hrLe (Nat.le_of_dvd r.property.1 hrDiv)
    simpa only [fibonacciRank, Nat.prime_three, dite_true, r] using hrEq
  have hFourR : 4 ∣ R := by
    simpa only [R, ← hRankThree] using
      (Finset.dvd_lcm (f := fibonacciRank) hThree)
  have hRpos : 0 < R := by
    apply Nat.pos_of_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro p hp
    simp only [fibonacciRank, hH p hp, dite_true]
    exact (rankWitness p (hH p hp)).property.1.ne'
  have hRtwo : 2 ≤ padicValNat 2 R := by
    have hTwoPow : 2 ^ 2 ∣ R := by simpa using hFourR
    exact (padicValNat_dvd_iff_le (p := 2) hRpos.ne').mp hTwoPow
  by_contra hBound
  change ¬ e ≤ padicValNat 2 R at hBound
  have heLarge : 3 ≤ e := by omega
  have heIndex : 2 ^ e ∣ n := by
    exact pow_padicValNat_dvd
  have hTwoEntry (m : ℕ) : 2 ∣ Nat.fib m ↔ 3 ∣ m := by
    apply D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      (by decide : 0 < 3) (by decide : 2 ∣ Nat.fib 3)
    intro j hj hFib
    by_contra hle
    have hjSmall : j = 1 ∨ j = 2 := by omega
    rcases hjSmall with rfl | rfl <;> norm_num at hFib
  let M := 2 ^ (e - 1)
  let N := 2 ^ e
  let FM := Nat.fib M
  let FN := Nat.fib N
  let C := FN / FM
  have hEeq : e - 1 + 1 = e := by omega
  have hMpos : 0 < M := pow_pos (by decide) _
  have hNpos : 0 < N := pow_pos (by decide) _
  have hFMpos : 0 < FM := Nat.fib_pos.mpr hMpos
  have hFNpos : 0 < FN := Nat.fib_pos.mpr hNpos
  have hMN : M ∣ N := by
    dsimp [M, N]
    exact pow_dvd_pow 2 (by omega)
  have hFMFN : FM ∣ FN := Nat.fib_dvd M N hMN
  have hMul : FM * C = FN := Nat.mul_div_cancel' hFMFN
  have hCpos : 0 < C := Nat.div_pos (Nat.le_of_dvd hFNpos hFMFN) hFMpos
  have hCnotSquare : ¬ IsSquare C := by
    simpa only [C, FN, FM, N, M, hEeq] using
      (fibonacci_dyadic_quotient_nonsquare (e - 1) (by omega)).2.2
  have hOddPrime : ∃ p : ℕ, p.Prime ∧ p ∣ C ∧ Odd (padicValNat p C) := by
    by_contra hNone
    have hEven (p : ℕ) (hp : p ∈ C.primeFactors) :
        Even (C.factorization p) := by
      have hpPrime := Nat.prime_of_mem_primeFactors hp
      have hpDiv := Nat.dvd_of_mem_primeFactors hp
      have hpNotOdd : ¬ Odd (padicValNat p C) := by
        intro hpOdd
        exact hNone ⟨p, hpPrime, hpDiv, hpOdd⟩
      rw [Nat.factorization_def C hpPrime]
      exact Nat.not_odd_iff_even.mp hpNotOdd
    let s := ∏ p ∈ C.primeFactors, p ^ (C.factorization p / 2)
    have hSquare : C = s ^ 2 := by
      rw [Nat.prod_primeFactors_pow_factorization hCpos.ne']
      dsimp only [s]
      rw [← Finset.prod_pow]
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul]
      congr 1
      obtain ⟨j, hj⟩ := hEven p hp
      omega
    apply hCnotSquare
    exact ⟨s, by simpa [pow_two] using hSquare⟩
  obtain ⟨p, hpPrime, hpC, hpOddC⟩ := hOddPrime
  letI : Fact p.Prime := ⟨hpPrime⟩
  have hpFN : p ∣ FN := by
    rw [← hMul]
    exact dvd_mul_of_dvd_right hpC FM
  have hpNotTwo : p ≠ 2 := by
    intro hpEq
    subst p
    have hThreePow : 3 ∣ N := (hTwoEntry N).mp hpFN
    have hThreeTwo : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hThreePow
    norm_num at hThreeTwo
  have hpNotPow (k : ℕ) : ¬ p ∣ 2 ^ k := by
    intro hpPow
    have hpTwo : p ∣ 2 := hpPrime.dvd_of_dvd_pow hpPow
    exact hpNotTwo ((Nat.prime_dvd_prime_iff_eq hpPrime Nat.prime_two).mp hpTwo)
  let r := rankWitness p hpPrime
  have hrDivN : r.val ∣ N :=
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      r.property.1 r.property.2.1 r.property.2.2).mp hpFN
  obtain ⟨j, hjLe, hjEq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hrDivN
  have hjTop : j = e := by
    by_contra hjNe
    have hjLow : j ≤ e - 1 := by omega
    have hrDivM : r.val ∣ M := by
      rw [hjEq]
      exact pow_dvd_pow 2 hjLow
    have hpFM : p ∣ FM :=
      (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
        r.property.1 r.property.2.1 r.property.2.2).mpr hrDivM
    have hValN := fibonacci_original_rank_valuation p N hpPrime hpFN (hpNotPow e)
    have hValM := fibonacci_original_rank_valuation p M hpPrime hpFM (hpNotPow (e - 1))
    have hValSame : padicValNat p FN = padicValNat p FM := hValN.trans hValM.symm
    have hCvalPos : 0 < padicValNat p C :=
      one_le_padicValNat_of_dvd hCpos.ne' hpC
    have hValMul : padicValNat p FN =
        padicValNat p FM + padicValNat p C := by
      rw [← hMul]
      exact padicValNat.mul hFMpos.ne' hCpos.ne'
    rw [hValSame] at hValMul
    omega
  have hrEqN : fibonacciRank p = N := by
    simpa only [fibonacciRank, hpPrime, dite_true, r] using (hjEq.trans (by rw [hjTop]))
  have hpNotFM : ¬ p ∣ FM := by
    intro hpFM
    have hrDivM : r.val ∣ M :=
      (D5.S3.Arith.FibonacciRank.fibonacci_entry_point
        r.property.1 r.property.2.1 r.property.2.2).mp hpFM
    have hrEqN' : r.val = N := by
      simpa only [fibonacciRank, hpPrime, dite_true, r] using hrEqN
    have hNM : N ∣ M := hrEqN' ▸ hrDivM
    have hVal : e ≤ e - 1 := by
      have hPow : 2 ^ e ∣ 2 ^ (e - 1) := hNM
      exact (Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mp hPow
    omega
  have hValFM : padicValNat p FM = 0 := padicValNat.eq_zero_of_not_dvd hpNotFM
  have hValFN : padicValNat p FN = padicValNat p C := by
    have hValMul : padicValNat p FN =
        padicValNat p FM + padicValNat p C := by
      rw [← hMul]
      exact padicValNat.mul hFMpos.ne' hCpos.ne'
    simpa only [hValFM, zero_add] using hValMul
  have hpNotH : p ∉ H := by
    intro hpH
    have hrR : fibonacciRank p ∣ R := Finset.dvd_lcm hpH
    have hNR : N ∣ R := hrEqN ▸ hrR
    have heLe : e ≤ padicValNat 2 R :=
      (padicValNat_dvd_iff_le (p := 2) hRpos.ne').mp hNR
    exact hBound (by simpa only [e, R] using heLe)
  have hpFibN : p ∣ Nat.fib n :=
    hpFN.trans (Nat.fib_dvd N n (by simpa only [N] using heIndex))
  have hpNotIndex : ¬ p ∣ n := by
    intro hpIndex
    exact hpNotH (hIndex p hpPrime hpIndex)
  have hValIndex := fibonacci_original_rank_valuation p n hpPrime hpFibN hpNotIndex
  have hValN := fibonacci_original_rank_valuation p N hpPrime hpFN (hpNotPow e)
  have hOddIndex : Odd (padicValNat p (Nat.fib n)) := by
    rw [hValIndex, ← hValN, hValFN]
    exact hpOddC
  exact hpNotH (hOdd p hpPrime hpFibN hOddIndex)

#print axioms fibonacci_dyadic_rank_budget

end D5.S3.Arith.Primes.FibonacciDyadicRankBudget
