/- GID: D5/S3/Arith/Primes/GoldenCubicBlockRanks
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/GoldenCubicBlockRanks
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Prime factors of the golden cubic blocks have exact Fibonacci entry ranks. -/

import D5.S1.Scale.GoldenCubicBlockCongruences
import D5.S1.Scale.FibLucasDouble
import D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

namespace D5.S3.Arith.Primes.GoldenCubicBlockRanks

open D5.S1.Scale
open D5.S3.Arith.Primes.FiniteFibonacciRankClosure
open D5.S3.Arith.Primes.FibonacciPrimeToIndexValuation

/-- A prime factor of the actual cubic Fibonacci block first divides the
Fibonacci sequence at the next power of three. -/
theorem cubic_block_c_prime_rank (j p : ℕ) (hj : 1 ≤ j) (hp : p.Prime)
    (hpC : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 1) :
    fibonacciRank p = 3 ^ (j + 1) ∧
      padicValInt p (goldenLucas (3 ^ j) ^ 2 + 1) =
        padicValNat p (Nat.fib (fibonacciRank p)) := by
  let n := 3 ^ j
  let x := goldenLucas n
  have hnodd : Odd n := (by decide : Odd (3 : ℕ)).pow
  have hx72 : ((x : ℤ) : ZMod 72) = 4 :=
    (golden_cubic_lucas_block j hj).1
  have hp3 : p ≠ 3 := by
    intro heq
    subst p
    have hx3 : (x : ZMod 3) = 1 := by
      have h := congrArg (ZMod.castHom (by decide : 3 ∣ 72) (ZMod 3)) hx72
      simpa only [map_intCast, map_ofNat, show (4 : ZMod 3) = 1 by decide] using h
    have hC0 : ((x ^ 2 + 1 : ℤ) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpC
    push_cast at hC0
    rw [hx3] at hC0
    exact (by decide : (2 : ZMod 3) ≠ 0) hC0
  have hpNotFib : ¬p ∣ Nat.fib n := by
    intro hpFib
    have hF0 : (Nat.fib n : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hpFib
    have hC0 : ((x ^ 2 + 1 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpC
    have hdisc : (x : ZMod p) ^ 2 - 5 * (Nat.fib n : ZMod p) ^ 2 = -4 := by
      have h := congrArg (fun z : ℤ => (z : ZMod p)) (golden_lucas_discriminant n)
      simpa [x, hnodd.neg_one_pow] using h
    have hxSq : (x : ZMod p) ^ 2 = -4 := by simpa [hF0] using hdisc
    have hcxSq : (x : ZMod p) ^ 2 = -1 := by
      push_cast at hC0
      exact eq_neg_iff_add_eq_zero.mpr hC0
    have h3zero : (3 : ZMod p) = 0 := by
      calc
        (3 : ZMod p) = (-1) - (-4) := by ring
        _ = (x : ZMod p) ^ 2 - (x : ZMod p) ^ 2 := by rw [← hcxSq, ← hxSq]
        _ = 0 := sub_self _
    have hpDvdThree : p ∣ 3 := (ZMod.natCast_eq_zero_iff _ _).mp h3zero
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hpDvdThree)
  have hpFibNext : p ∣ Nat.fib (3 ^ (j + 1)) := by
    have htriple := (golden_cubic_fibonacci_block j hj).2.2
    have hInt : (p : ℤ) ∣ (Nat.fib (3 ^ (j + 1)) : ℤ) := by
      rw [htriple]
      exact dvd_mul_of_dvd_right hpC _
    exact_mod_cast hInt
  let r := rankWitness p hp
  have hrpos : 0 < r.val := r.property.1
  have hrzero : p ∣ Nat.fib r.val := r.property.2.1
  have hrmin : ∀ t, 0 < t → p ∣ Nat.fib t → r.val ≤ t := r.property.2.2
  have hrdiv : r.val ∣ 3 ^ (j + 1) :=
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point hrpos hrzero hrmin).mp hpFibNext
  obtain ⟨e, he, hre⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hrdiv
  have heq : e = j + 1 := by
    by_contra hne
    have hele : e ≤ j := by omega
    have hrdivN : r.val ∣ n := by
      rw [hre]
      exact pow_dvd_pow 3 hele
    exact hpNotFib
      ((D5.S3.Arith.FibonacciRank.fibonacci_entry_point hrpos hrzero hrmin).mpr hrdivN)
  have hrNext : r.val = 3 ^ (j + 1) := by rw [hre, heq]
  have hRank : fibonacciRank p = 3 ^ (j + 1) := by
    simpa only [fibonacciRank, hp, dite_true] using hrNext
  refine ⟨hRank, ?_⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hpNotIndex : ¬p ∣ 3 ^ (j + 1) := by
    intro h
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp
      (hp.dvd_of_dvd_pow h))
  have hOriginal := fibonacci_original_rank_valuation p (3 ^ (j + 1))
    hp hpFibNext hpNotIndex
  have hFibNonzero : (Nat.fib n : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.fib_pos.mpr (pow_pos (by decide : 0 < 3) j)).ne'
  have hCNonzero : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hValFib : padicValInt p (Nat.fib (3 ^ (j + 1)) : ℤ) =
      padicValInt p (x ^ 2 + 1) := by
    rw [(golden_cubic_fibonacci_block j hj).2.2,
      padicValInt.mul hFibNonzero hCNonzero,
      padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hpNotFib), zero_add]
  simpa only [padicValInt.of_nat, x, n] using hValFib.symm.trans hOriginal

#print axioms cubic_block_c_prime_rank

/-- A prime factor of the actual Lucas cubic block first divides the
Fibonacci sequence at twice the next power of three. -/
theorem cubic_block_b_prime_rank (j p : ℕ) (hj : 1 ≤ j) (hp : p.Prime)
    (hpB : (p : ℤ) ∣ goldenLucas (3 ^ j) ^ 2 + 3) :
    fibonacciRank p = 2 * 3 ^ (j + 1) ∧
      @legendreSym p ⟨hp⟩ 5 = 1 ∧
      padicValInt p (goldenLucas (3 ^ j) ^ 2 + 3) =
        padicValNat p (Nat.fib (fibonacciRank p)) := by
  let n := 3 ^ j
  let rNext := 3 ^ (j + 1)
  let x := goldenLucas n
  let B := x ^ 2 + 3
  have hnodd : Odd n := (by decide : Odd (3 : ℕ)).pow
  have hrOdd : Odd rNext := (by decide : Odd (3 : ℕ)).pow
  have hx72 : (x : ZMod 72) = 4 := (golden_cubic_lucas_block j hj).1
  have hp2 : p ≠ 2 := by
    intro heq
    subst p
    have hx2 : (x : ZMod 2) = 0 := by
      have h := congrArg (ZMod.castHom (by decide : 2 ∣ 72) (ZMod 2)) hx72
      simpa only [map_intCast, map_ofNat, show (4 : ZMod 2) = 0 by decide] using h
    have hB0 : (B : ZMod 2) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpB
    dsimp [B] at hB0
    push_cast at hB0
    rw [hx2] at hB0
    have hOne : (1 : ZMod 2) = 0 := by
      simpa [show (3 : ZMod 2) = 1 by decide] using hB0
    exact (by decide : (1 : ZMod 2) ≠ 0) hOne
  have hp3 : p ≠ 3 := by
    intro heq
    subst p
    have hx3 : (x : ZMod 3) = 1 := by
      have h := congrArg (ZMod.castHom (by decide : 3 ∣ 72) (ZMod 3)) hx72
      simpa only [map_intCast, map_ofNat, show (4 : ZMod 3) = 1 by decide] using h
    have hB0 : (B : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpB
    dsimp [B] at hB0
    push_cast at hB0
    rw [hx3] at hB0
    have hOne : (1 : ZMod 3) = 0 := by
      simpa [show (3 : ZMod 3) = 0 by decide] using hB0
    exact (by decide : (1 : ZMod 3) ≠ 0) hOne
  have hpNotX : ¬(p : ℤ) ∣ x := by
    intro hpX
    have hx0 : (x : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpX
    have hB0 : (B : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpB
    dsimp [B] at hB0
    push_cast at hB0
    rw [hx0] at hB0
    have hpThree : p ∣ 3 := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hB0)
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hpThree)
  have hpNotFibN : ¬p ∣ Nat.fib n := by
    intro hpFib
    have hf0 : (Nat.fib n : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hpFib
    have hB0 : (B : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpB
    have hdisc : (x : ZMod p) ^ 2 - 5 * (Nat.fib n : ZMod p) ^ 2 = -4 := by
      have h := congrArg (fun z : ℤ => (z : ZMod p)) (golden_lucas_discriminant n)
      simpa [x, hnodd.neg_one_pow] using h
    have hxSq : (x : ZMod p) ^ 2 = -4 := by simpa [hf0] using hdisc
    have hbxSq : (x : ZMod p) ^ 2 = -3 := by
      dsimp [B] at hB0
      push_cast at hB0
      exact eq_neg_iff_add_eq_zero.mpr hB0
    have hone : (1 : ZMod p) = 0 := by
      calc
        (1 : ZMod p) = (-3) - (-4) := by ring
        _ = (x : ZMod p) ^ 2 - (x : ZMod p) ^ 2 := by rw [← hbxSq, ← hxSq]
        _ = 0 := sub_self _
    have hpOne : p ∣ 1 := (ZMod.natCast_eq_zero_iff _ _).mp (by simpa using hone)
    exact hp.ne_one (Nat.dvd_one.mp hpOne)
  have hpNotFibDoubleN : ¬p ∣ Nat.fib (2 * n) := by
    intro hpFib
    letI : Fact p.Prime := ⟨hp⟩
    have hf2 : (Nat.fib (2 * n) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hpFib
    have hfn : (Nat.fib n : ZMod p) ≠ 0 := by
      intro hz
      exact hpNotFibN ((ZMod.natCast_eq_zero_iff _ _).mp hz)
    have hx : (x : ZMod p) ≠ 0 := by
      intro hz
      exact hpNotX ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hz)
    have hDouble := congrArg (fun z : ℤ => (z : ZMod p))
      (golden_fib_two_mul_eq_fib_mul_lucas n)
    have hMul : (Nat.fib (2 * n) : ZMod p) = (Nat.fib n : ZMod p) * (x : ZMod p) := by
      simpa [x] using hDouble
    exact (mul_ne_zero hfn hx) (hMul ▸ hf2)
  have hLucasNext : goldenLucas rNext = x * B :=
    (golden_cubic_lucas_block j hj).2.2.2.2.2
  have hpLucasNext : (p : ℤ) ∣ goldenLucas rNext := by
    rw [hLucasNext]
    exact dvd_mul_of_dvd_right hpB _
  have hpNotFibNext : ¬p ∣ Nat.fib rNext := by
    intro hpFib
    have hL0 : (goldenLucas rNext : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpLucasNext
    have hF0 : (Nat.fib rNext : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hpFib
    have hdisc : (goldenLucas rNext : ZMod p) ^ 2 -
        5 * (Nat.fib rNext : ZMod p) ^ 2 = -4 := by
      have h := congrArg (fun z : ℤ => (z : ZMod p)) (golden_lucas_discriminant rNext)
      simpa [hrOdd.neg_one_pow] using h
    rw [hL0, hF0] at hdisc
    have hFour : (4 : ZMod p) = 0 := by linear_combination hdisc
    have hpFour : p ∣ 4 := (ZMod.natCast_eq_zero_iff _ _).mp hFour
    have hpPow : p ∣ 2 ^ (2 : ℕ) := by
      simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using hpFour
    have hpDvdTwo : p ∣ 2 := hp.dvd_of_dvd_pow hpPow
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hpDvdTwo)
  have hpFibDoubleNext : p ∣ Nat.fib (2 * rNext) := by
    have hInt : (p : ℤ) ∣ (Nat.fib (2 * rNext) : ℤ) := by
      rw [golden_fib_two_mul_eq_fib_mul_lucas]
      exact dvd_mul_of_dvd_right hpLucasNext _
    exact_mod_cast hInt
  let rank := rankWitness p hp
  have hrpos : 0 < rank.val := rank.property.1
  have hrzero : p ∣ Nat.fib rank.val := rank.property.2.1
  have hrmin : ∀ t, 0 < t → p ∣ Nat.fib t → rank.val ≤ t := rank.property.2.2
  have hrdiv : rank.val ∣ 2 * rNext :=
    (D5.S3.Arith.FibonacciRank.fibonacci_entry_point hrpos hrzero hrmin).mp hpFibDoubleNext
  have hrNotOdd : ¬Odd rank.val := by
    intro hOdd
    have hcop : Nat.Coprime rank.val 2 := hOdd.coprime_two_right
    have hrdivNext : rank.val ∣ rNext := hcop.dvd_of_dvd_mul_left hrdiv
    exact hpNotFibNext
      ((D5.S3.Arith.FibonacciRank.fibonacci_entry_point hrpos hrzero hrmin).mpr hrdivNext)
  obtain ⟨s, hs⟩ := (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hrNotOdd))
  have hsdiv : s ∣ rNext := by
    apply (mul_dvd_mul_iff_left (by decide : (2 : ℕ) ≠ 0)).mp
    simpa only [hs] using hrdiv
  obtain ⟨e, he, hse⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 3)).mp hsdiv
  have heq : e = j + 1 := by
    by_contra hne
    have hele : e ≤ j := by omega
    have hrdivDoubleN : rank.val ∣ 2 * n := by
      rw [hs, hse]
      exact mul_dvd_mul_left 2 (pow_dvd_pow 3 hele)
    exact hpNotFibDoubleN
      ((D5.S3.Arith.FibonacciRank.fibonacci_entry_point hrpos hrzero hrmin).mpr
        hrdivDoubleN)
  have hrNext : rank.val = 2 * 3 ^ (j + 1) := by rw [hs, hse, heq]
  have hRank : fibonacciRank p = 2 * 3 ^ (j + 1) := by
    simpa only [fibonacciRank, hp, dite_true] using hrNext
  have hp5 : p ≠ 5 := by
    intro heq
    subst p
    have hxSq : (x : ZMod 5) ^ 2 = 1 := by
      simpa only [Int.cast_pow] using (golden_cubic_lucas_block j hj).2.2.2.1
    have hB0 : (B : ZMod 5) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpB
    dsimp [B] at hB0
    push_cast at hB0
    rw [hxSq] at hB0
    have hFour : (4 : ZMod 5) = 0 := by
      simpa [show (1 + 3 : ZMod 5) = 4 by decide] using hB0
    exact (by decide : (4 : ZMod 5) ≠ 0) hFour
  refine ⟨hRank, ?_, ?_⟩
  · letI : Fact p.Prime := ⟨hp⟩
    have hFive : (5 : ZMod p) ≠ 0 := by
      intro hz
      have hpDvdFive : p ∣ 5 := (ZMod.natCast_eq_zero_iff _ _).mp hz
      exact hp5 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5)).mp hpDvdFive)
    have hTwo : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hpDvdTwo : p ∣ 2 := (ZMod.natCast_eq_zero_iff _ _).mp hz
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hpDvdTwo)
    have hL0 : (goldenLucas rNext : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpLucasNext
    have hdisc : (goldenLucas rNext : ZMod p) ^ 2 -
        5 * (Nat.fib rNext : ZMod p) ^ 2 = -4 := by
      have h := congrArg (fun z : ℤ => (z : ZMod p)) (golden_lucas_discriminant rNext)
      simpa [hrOdd.neg_one_pow] using h
    rw [hL0] at hdisc
    have hSquare : (2 : ZMod p) ^ 2 - 5 * (Nat.fib rNext : ZMod p) ^ 2 = 0 := by
      linear_combination hdisc
    exact legendreSym.eq_one_of_sq_sub_mul_sq_eq_zero'
      (p := p) (a := 5) (x := (2 : ZMod p)) (y := (Nat.fib rNext : ZMod p))
      (by simpa using hFive) hTwo (by simpa using hSquare)
  · letI : Fact p.Prime := ⟨hp⟩
    have hpNotIndex : ¬p ∣ 2 * rNext := by
      intro h
      rcases hp.dvd_mul.mp h with hpDvdTwo | hpDvdR
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hpDvdTwo)
      · have hpDvdThree : p ∣ 3 := hp.dvd_of_dvd_pow (by simpa [rNext] using hpDvdR)
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).mp hpDvdThree)
    have hOriginal := fibonacci_original_rank_valuation p (2 * rNext)
      hp hpFibDoubleNext hpNotIndex
    have hFibNonzero : (Nat.fib rNext : ℤ) ≠ 0 := by
      exact_mod_cast (Nat.fib_pos.mpr (pow_pos (by decide : 0 < 3) (j + 1))).ne'
    have hXNonzero : x ≠ 0 := by
      intro hz
      exact hpNotX (hz ▸ dvd_zero _)
    have hBNonzero : B ≠ 0 := by
      dsimp [B]
      nlinarith [sq_nonneg x]
    have hLNonzero : goldenLucas rNext ≠ 0 := by
      rw [hLucasNext]
      exact mul_ne_zero hXNonzero hBNonzero
    have hValF : padicValInt p (Nat.fib rNext : ℤ) = 0 :=
      padicValInt.eq_zero_of_not_dvd (by exact_mod_cast hpNotFibNext)
    have hValX : padicValInt p x = 0 :=
      padicValInt.eq_zero_of_not_dvd hpNotX
    have hValL : padicValInt p (goldenLucas rNext) = padicValInt p B := by
      rw [hLucasNext, padicValInt.mul hXNonzero hBNonzero, hValX, zero_add]
    have hValFib : padicValInt p (Nat.fib (2 * rNext) : ℤ) = padicValInt p B := by
      rw [golden_fib_two_mul_eq_fib_mul_lucas,
        padicValInt.mul hFibNonzero hLNonzero, hValF, zero_add, hValL]
    simpa only [padicValInt.of_nat, B, x, n] using hValFib.symm.trans hOriginal

#print axioms cubic_block_b_prime_rank

end D5.S3.Arith.Primes.GoldenCubicBlockRanks
