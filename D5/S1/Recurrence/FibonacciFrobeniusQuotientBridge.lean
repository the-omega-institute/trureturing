/- GID: D5/S1/Recurrence/FibonacciFrobeniusQuotientBridge
   generality: I
   mirror-B: none(waiver:conditional-index-identification)
   mirror-E: none(waiver:conditional-index-identification)
   anchors: []
   digest: Conditional exact bridge from the return-period Fibonacci quotient to the standard Frobenius-index quotient, with explicit p=2 and p=5 exclusions and unit factor. -/

import D5.S1.Recurrence.FibonacciReturnSpectrum
import D5.S3.Arith.GoldenApparition
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S1.Recurrence.FibonacciFrobeniusQuotientBridge

open D5.S1.Recurrence.FibonacciReturnSpectrum
open D5.S3.Arith.GoldenApparition

/-- The normalized Fibonacci quotient, viewed in the residue field. -/
def quotientMod (p n : ℕ) : ZMod p :=
  (Nat.fib n / p : ZMod p)

/-- The Frobenius index is positive for primes other than 2 and 5. -/
theorem frobenius_index_pos {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5) :
    0 < p - Int.natAbs (legendreSym 5 p) := by
  have hpge : 7 ≤ p := by
    omega
  have hleg : Int.natAbs (legendreSym 5 p) ≤ 1 := by
    have hcases := legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ))
    have hfive : (p : ZMod 5) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro h
      have : p = 5 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp h).symm
      exact hp5 this
    rcases hcases hfive with h | h <;> simp [h]
  omega

/-- Exact quotient bridge once the actual least return period is the Frobenius index.
The proportionality factor is 1, hence a unit. The hypotheses explicitly exclude
the dyadic and ramified cases where the golden Frobenius normalization changes. -/
theorem quotient_period_eq_frobenius
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (hperiod : period p = p - Int.natAbs (legendreSym 5 p)) :
    quotientMod p (period p) =
      (1 : ZMod p) * quotientMod p (p - Int.natAbs (legendreSym 5 p)) := by
  rw [hperiod]
  simp

/-- The proportionality coefficient in the preceding bridge is invertible,
for every prime, including the exceptional characteristics. -/
theorem quotient_period_eq_frobenius_factor_isUnit
    {p : ℕ} (hp : p.Prime) :
    IsUnit (1 : ZMod p) := by
  exact isUnit_one

/-- The standard Frobenius index is a genuine p-divisible Fibonacci index away
from p=5, by the repository's existing golden Frobenius theorem. -/
theorem frobenius_index_fib_dvd
    {p : ℕ} (hp : p.Prime) (hp5 : p ≠ 5) :
    p ∣ Nat.fib (p - Int.natAbs (legendreSym 5 p)) := by
  have hpNotDvdFive : ¬ p ∣ 5 := by
    intro h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h)
  have h := (fibonacci_apparition_entry_point hp hpNotDvdFive).1
  have hleg : Int.natAbs (legendreSym 5 p) = 1 := by
    have hpmod : (p : ZMod 5) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro hz
      exact hp5 ((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hz).symm
    rcases legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ)) hpmod with he | he <;>
      simp [he]
  have hindex : (p : ℤ) - legendreSym 5 p =
      ((p - Int.natAbs (legendreSym 5 p) : ℕ) : ℤ) := by
    have hs := legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ)) hpmod
    rcases hs with he | he <;> simp [he]
  rw [hindex, Int.fib_natCast, Int.cast_natCast] at h
  exact (ZMod.natCast_eq_zero_iff _ _).mp h

end D5.S1.Recurrence.FibonacciFrobeniusQuotientBridge
