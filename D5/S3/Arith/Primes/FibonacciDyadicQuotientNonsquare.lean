/- GID: D5/S3/Arith/Primes/FibonacciDyadicQuotientNonsquare
   generality: I
   mirror-B: D5/B/S3/Arith/Primes/FibonacciDyadicQuotientNonsquare
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Every nontrivial dyadic Fibonacci quotient has a nonsquare residue modulo five. -/

import D5.S1.Scale.FibLucasDouble
import D5.S1.Scale.LucasDoubling
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare

open D5.S1.Scale

/-- The Lucas doubling orbit at powers of two enters the fixed residue two
modulo five, while its first quotient has residue three. -/
theorem fibonacci_dyadic_quotient_nonsquare (k : ℕ) (hk : 1 ≤ k) :
    let q := Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k)
    (k = 1 → q % 5 = 3) ∧ (2 ≤ k → q % 5 = 2) ∧ ¬ IsSquare q := by
  dsimp only
  have hL2 : goldenLucas 2 = 3 := by decide
  have hL4 : goldenLucas 4 = 7 := by decide
  have hOrbit (m : ℕ) : (goldenLucas (2 ^ (m + 2)) : ZMod 5) = 2 := by
    induction m with
    | zero =>
        change (goldenLucas 4 : ZMod 5) = 2
        rw [hL4]
        decide
    | succ m ih =>
        have hEven : Even (2 ^ (m + 2)) :=
          (Nat.even_pow).2 ⟨by decide, by omega⟩
        have hsign : (-1 : ℤ) ^ (2 ^ (m + 2)) = 1 := hEven.neg_one_pow
        have hindex : 2 ^ (m + 1 + 2) = 2 * 2 ^ (m + 2) := by ring
        rw [hindex, golden_lucas_two_mul, hsign]
        push_cast
        rw [ih]
        decide
  have hLmod :
      (goldenLucas (2 ^ k) : ZMod 5) = if k = 1 then 3 else 2 := by
    by_cases hk1 : k = 1
    · subst k
      simp [hL2]
    · have hk2 : 2 ≤ k := by omega
      have hindex : k = (k - 2) + 2 := by omega
      rw [hindex]
      simp [hOrbit]
  have hFpos : 0 < Nat.fib (2 ^ k) :=
    Nat.fib_pos.mpr (pow_pos (by decide) k)
  have hFnext : 0 < Nat.fib (2 ^ (k + 1)) :=
    Nat.fib_pos.mpr (pow_pos (by decide) (k + 1))
  have hDouble : (Nat.fib (2 ^ (k + 1)) : ℤ) =
      (Nat.fib (2 ^ k) : ℤ) * goldenLucas (2 ^ k) := by
    simpa [pow_succ, mul_comm] using golden_fib_two_mul_eq_fib_mul_lucas (2 ^ k)
  have hLpos : 0 < goldenLucas (2 ^ k) := by
    have hFposInt : (0 : ℤ) < Nat.fib (2 ^ k) := by exact_mod_cast hFpos
    have hFnextInt : (0 : ℤ) < Nat.fib (2 ^ (k + 1)) := by exact_mod_cast hFnext
    nlinarith [hDouble]
  have hDoubleNat : Nat.fib (2 ^ (k + 1)) =
      Nat.fib (2 ^ k) * (goldenLucas (2 ^ k)).toNat := by
    have hcast : (((goldenLucas (2 ^ k)).toNat : ℕ) : ℤ) = goldenLucas (2 ^ k) :=
      Int.toNat_of_nonneg (le_of_lt hLpos)
    rw [← hcast] at hDouble
    exact_mod_cast hDouble
  have hQuotient : Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k) =
      (goldenLucas (2 ^ k)).toNat := by
    rw [hDoubleNat]
    exact Nat.mul_div_cancel_left _ hFpos
  have hCast : (((goldenLucas (2 ^ k)).toNat : ℕ) : ZMod 5) =
      (goldenLucas (2 ^ k) : ZMod 5) :=
    ZMod.natCast_toNat 5 (le_of_lt hLpos)
  have hQmod : ((Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k) : ℕ) : ZMod 5) =
      if k = 1 then 3 else 2 := by
    rw [hQuotient, hCast]
    exact hLmod
  have hQone (hk1 : k = 1) :
      (Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k)) % 5 = 3 := by
    exact (ZMod.natCast_eq_natCast_iff' _ 3 5).mp (by simpa [hk1] using hQmod)
  have hQlater (hk2 : 2 ≤ k) :
      (Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k)) % 5 = 2 := by
    have hk1 : k ≠ 1 := by omega
    exact (ZMod.natCast_eq_natCast_iff' _ 2 5).mp (by simpa [hk1] using hQmod)
  refine ⟨hQone, hQlater, ?_⟩
  intro hSquare
  have hSquareMod :
      IsSquare ((Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k) : ℕ) : ZMod 5) :=
    hSquare.map (Nat.castRingHom (ZMod 5))
  by_cases hk1 : k = 1
  · have hBad : ¬ IsSquare (3 : ZMod 5) := by decide
    have hmod3 : ((Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k) : ℕ) : ZMod 5) = 3 :=
      by simpa [hk1] using hQmod
    rw [hmod3] at hSquareMod
    exact hBad hSquareMod
  · have hBad : ¬ IsSquare (2 : ZMod 5) := by decide
    have hmod2 : ((Nat.fib (2 ^ (k + 1)) / Nat.fib (2 ^ k) : ℕ) : ZMod 5) = 2 :=
      by simpa [hk1] using hQmod
    rw [hmod2] at hSquareMod
    exact hBad hSquareMod

#print axioms fibonacci_dyadic_quotient_nonsquare

end D5.S3.Arith.Primes.FibonacciDyadicQuotientNonsquare
