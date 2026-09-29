/- GID: D5/S3/Arith/Primes/FibonacciTernaryRankBudget
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciTernaryRankBudget
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Odd Fibonacci support bounds ternary index depth by ranks in finite prime support. -/

import D5.S3.Arith.Primes.GoldenCubicBlockRanks

namespace D5.S3.Arith.Primes.FibonacciTernaryRankBudget

open D5.S1.Scale
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation
open D5.S3.Arith.Primes.GoldenCubicBlockRanks

/-- Odd Fibonacci support bounds the exponent of three in a positive index
by the rank lcm of its prescribed prime support. -/
theorem fibonacci_ternary_rank_budget (H : Finset ℕ) (n : ℕ)
    (hH : ∀ p ∈ H, p.Prime) (hTwo : 2 ∈ H) (hn : 0 < n)
    (hIndex : ∀ p : ℕ, p.Prime → p ∣ n → p ∈ H)
    (hOdd : ∀ p : ℕ, p.Prime → p ∣ Nat.fib n →
      Odd (padicValNat p (Nat.fib n)) → p ∈ H) :
    padicValNat 3 n ≤ padicValNat 3 (H.lcm fibonacciRank) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let R := H.lcm fibonacciRank
  let e := padicValNat 3 n
  have hTwoEntry (m : ℕ) : 2 ∣ Nat.fib m ↔ 3 ∣ m := by
    apply D5.S3.Arith.FibonacciRank.fibonacci_entry_point
      (by decide : 0 < 3) (by decide : 2 ∣ Nat.fib 3)
    intro k hk hFib
    by_contra hle
    have hkSmall : k = 1 ∨ k = 2 := by omega
    rcases hkSmall with rfl | rfl <;> norm_num at hFib
  have hRankTwo : fibonacciRank 2 = 3 := by
    let r := rankWitness 2 Nat.prime_two
    have hrDiv : 3 ∣ r.val := (hTwoEntry r.val).mp r.property.2.1
    have hrLe : r.val ≤ 3 := r.property.2.2 3 (by decide) (by decide)
    have hrEq : r.val = 3 :=
      Nat.le_antisymm hrLe (Nat.le_of_dvd r.property.1 hrDiv)
    simpa only [fibonacciRank, Nat.prime_two, dite_true, r] using hrEq
  have hThreeR : 3 ∣ R := by
    simpa only [R, ← hRankTwo] using
      (Finset.dvd_lcm (f := fibonacciRank) hTwo)
  have hRpos : 0 < R := by
    apply Nat.pos_of_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro p hp
    simp only [fibonacciRank, hH p hp, dite_true]
    exact (rankWitness p (hH p hp)).property.1.ne'
  have hRthree : 1 ≤ padicValNat 3 R := by
    have hPow : 3 ^ 1 ∣ R := by simpa using hThreeR
    exact (padicValNat_dvd_iff_le (p := 3) hRpos.ne').mp hPow
  by_contra hBound
  change ¬ e ≤ padicValNat 3 R at hBound
  have heLarge : 2 ≤ e := by omega
  have heIndex : 3 ^ e ∣ n := pow_padicValNat_dvd
  let j := e - 1
  have hj : 1 ≤ j := by omega
  have hje : j + 1 = e := by omega
  let x := goldenLucas (3 ^ j)
  let C : ℕ := (x ^ 2 + 1).toNat
  have hCposInt : 0 < x ^ 2 + 1 := by nlinarith [sq_nonneg x]
  have hCast : (C : ℤ) = x ^ 2 + 1 :=
    Int.toNat_of_nonneg (le_of_lt hCposInt)
  have hCpos : 0 < C := by
    rw [← hCast] at hCposInt
    exact_mod_cast hCposInt
  have hCmod : (C : ZMod 5) = 2 := by
    have hLucas : ((x ^ 2 : ℤ) : ZMod 5) = 1 := by
      simpa only [x] using (golden_cubic_lucas_block j hj).2.2.2.1
    push_cast at hLucas
    have hInt : (((C : ℕ) : ℤ) : ZMod 5) = 2 := by
      rw [hCast]
      push_cast
      rw [hLucas]
      decide
    simpa only [Int.cast_natCast] using hInt
  have hCnotSquare : ¬ IsSquare C := by
    intro hSquare
    have hSquareMod : IsSquare (C : ZMod 5) :=
      hSquare.map (Nat.castRingHom (ZMod 5))
    rw [hCmod] at hSquareMod
    exact (by decide : ¬ IsSquare (2 : ZMod 5)) hSquareMod
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
      obtain ⟨k, hk⟩ := hEven p hp
      omega
    apply hCnotSquare
    exact ⟨s, by simpa [pow_two] using hSquare⟩
  obtain ⟨p, hpPrime, hpC, hpOddC⟩ := hOddPrime
  have hpCInt : (p : ℤ) ∣ x ^ 2 + 1 := by
    rw [← hCast]
    exact_mod_cast hpC
  have hRankVal := cubic_block_c_prime_rank j p hj hpPrime (by simpa only [x] using hpCInt)
  have hRank : fibonacciRank p = 3 ^ e := by simpa only [hje] using hRankVal.1
  have hOriginal : padicValNat p C =
      padicValNat p (Nat.fib (fibonacciRank p)) := by
    have hValInt : padicValInt p (C : ℤ) =
        padicValNat p (Nat.fib (fibonacciRank p)) := by
      simpa only [hCast, x] using hRankVal.2
    simpa only [padicValInt.of_nat] using hValInt
  have hProductInt : (Nat.fib (3 ^ (j + 1)) : ℤ) =
      (Nat.fib (3 ^ j) : ℤ) * (x ^ 2 + 1) := by
    simpa only [x] using (golden_cubic_fibonacci_block j hj).2.2
  have hProduct : Nat.fib (3 ^ (j + 1)) = Nat.fib (3 ^ j) * C := by
    rw [← hCast] at hProductInt
    exact_mod_cast hProductInt
  have hpNotH : p ∉ H := by
    intro hpH
    have hrR : fibonacciRank p ∣ R := Finset.dvd_lcm hpH
    rw [hRank] at hrR
    have heLe : e ≤ padicValNat 3 R :=
      (padicValNat_dvd_iff_le (p := 3) hRpos.ne').mp hrR
    exact hBound heLe
  have hpFibPow : p ∣ Nat.fib (3 ^ e) := by
    have hFibEq : Nat.fib (3 ^ e) = Nat.fib (3 ^ j) * C := by
      simpa only [hje] using hProduct
    rw [hFibEq]
    exact dvd_mul_of_dvd_right hpC _
  have hpFibN : p ∣ Nat.fib n :=
    hpFibPow.trans (Nat.fib_dvd (3 ^ e) n heIndex)
  have hpNotIndex : ¬ p ∣ n := by
    intro hpIndex
    exact hpNotH (hIndex p hpPrime hpIndex)
  have hValN := fibonacci_original_rank_valuation p n hpPrime hpFibN hpNotIndex
  have hOddN : Odd (padicValNat p (Nat.fib n)) := by
    rw [hValN, ← hOriginal]
    exact hpOddC
  exact hpNotH (hOdd p hpPrime hpFibN hOddN)

#print axioms fibonacci_ternary_rank_budget

end D5.S3.Arith.Primes.FibonacciTernaryRankBudget
