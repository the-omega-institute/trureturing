/- GID: D5/S3/Arith/FibonacciRank
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Minimal Fibonacci zero indices characterize zero indices and meet prime bounds. -/

import Mathlib
import D5.S1.Recurrence.GoldenFibDivisibility
import D5.S3.Arith.GoldenApparition

/- Provenance: re-proved native from automath witness
`Omega.fib_prime_entry_point`, no automath import. -/

namespace D5.S3.Arith.FibonacciRank

open D5.S3.Arith.GoldenApparition

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- If `k` is the least positive index whose Fibonacci number is divisible by
`p`, then the indices of all Fibonacci numbers divisible by `p` are exactly
the multiples of `k`. No primality assumption on `p` is needed: this is the
minimal-zero consequence of the strong divisibility identity `Nat.fib_gcd`.
The hypotheses explicitly supply existence and minimality of the positive
entry point; the theorem does not define a rank for moduli without one. -/
theorem fibonacci_entry_point {p k n : ℕ} (hkpos : 0 < k)
    (hkzero : p ∣ Nat.fib k)
    (hkmin : ∀ j, 0 < j → p ∣ Nat.fib j → k ≤ j) :
    p ∣ Nat.fib n ↔ k ∣ n := by
  constructor
  · intro hn
    have hcommon : p ∣ Nat.fib (Nat.gcd k n) := by
      rw [Nat.fib_gcd]
      exact Nat.dvd_gcd hkzero hn
    have hgcdpos : 0 < Nat.gcd k n := Nat.gcd_pos_of_pos_left n hkpos
    have hkle : k ≤ Nat.gcd k n := hkmin _ hgcdpos hcommon
    have hgcdle : Nat.gcd k n ≤ k := Nat.gcd_le_left n (by omega)
    exact Nat.gcd_eq_left_iff_dvd.mp (Nat.le_antisymm hgcdle hkle)
  · intro hkn
    exact dvd_trans hkzero (Nat.fib_dvd k n hkn)

/-- For a prime `p ≠ 5`, any explicitly supplied least positive Fibonacci
zero index `r` divides `p - 1` when `(5 / p) = 1`, and divides `p + 1`
otherwise. This includes `p = 2`; only the ramified prime `5` is excluded.
The zero at the relevant index comes from the golden Frobenius apparition
theorem, while `fibonacci_entry_point` turns that zero into index divisibility. -/
theorem fibonacci_rank_dvd_prime_bound {p r : ℕ} (hp : p.Prime) (hp5 : p ≠ 5)
    (hrpos : 0 < r) (hrzero : p ∣ Nat.fib r)
    (hrmin : ∀ n, 0 < n → p ∣ Nat.fib n → r ≤ n) :
    r ∣ if legendreSym 5 p = 1 then p - 1 else p + 1 := by
  have hpNotDvdFive : ¬ p ∣ 5 := by
    intro hpDvdFive
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp hpDvdFive)
  have happ :=
    (fibonacci_apparition_entry_point hp hpNotDvdFive).1
  have hpOne : 1 ≤ p := hp.one_le
  by_cases heps : legendreSym 5 p = 1
  · rw [if_pos heps]
    apply (fibonacci_entry_point hrpos hrzero hrmin).mp
    rw [← ZMod.natCast_eq_zero_iff]
    have hindex : (p : ℤ) - legendreSym 5 p = ((p - 1 : ℕ) : ℤ) := by
      rw [heps]
      omega
    rw [hindex, Int.fib_natCast, Int.cast_natCast] at happ
    exact happ
  · rw [if_neg heps]
    have hpModFive : (p : ZMod 5) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      intro hFiveDvd
      exact hp5 (((Nat.prime_dvd_prime_iff_eq Nat.prime_five hp).mp hFiveDvd).symm)
    have hepsNeg : legendreSym 5 p = -1 :=
      (legendreSym.eq_one_or_neg_one (p := 5) (a := (p : ℤ)) hpModFive).resolve_left heps
    apply (fibonacci_entry_point hrpos hrzero hrmin).mp
    rw [← ZMod.natCast_eq_zero_iff]
    have hindex : (p : ℤ) - legendreSym 5 p = ((p + 1 : ℕ) : ℤ) := by
      rw [hepsNeg]
      omega
    rw [hindex, Int.fib_natCast, Int.cast_natCast] at happ
    exact happ

end D5.S3.Arith.FibonacciRank
