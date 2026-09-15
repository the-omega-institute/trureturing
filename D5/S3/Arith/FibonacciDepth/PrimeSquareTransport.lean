/- GID: D5/S3/Arith/FibonacciDepth/PrimeSquareTransport
   generality: G
   mirror-B: none(waiver:all-primes-all-multipliers)
   mirror-E: none(waiver:unbounded-recurrence-proof)
   anchors: []
   digest: Prime-square divisibility of actual Fibonacci multiples has exactly two causes. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.FibonacciDepth.PrimeSquareTransport

/-- The actual recurrence in a coefficient ring where F_n has square zero. -/
private lemma square_zero_pair {R : Type*} [CommRing R] (n k : ℕ)
    (hn : 0 < n) (hz : (Nat.fib n : R) ^ 2 = 0) :
    (Nat.fib (n * (k + 1)) : R) =
        ((k + 1 : ℕ) : R) * (Nat.fib n : R) * (Nat.fib (n + 1) : R) ^ k ∧
      (Nat.fib (n * (k + 1) + 1) : R) = (Nat.fib (n + 1) : R) ^ (k + 1) := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  have hrec : (Nat.fib (n + 1) : R) =
      (Nat.fib (n - 1) : R) + (Nat.fib n : R) := by
    simpa only [Nat.cast_add] using congrArg (fun a : ℕ => (a : R))
      (Nat.fib_add_one (show n ≠ 0 by omega))
  induction k with
  | zero => simp
  | succ k ih =>
    have hfirst : (Nat.fib (n * (k + 1) + n) : R) =
        (Nat.fib (n * (k + 1)) : R) * (Nat.fib (n - 1) : R) +
          (Nat.fib (n * (k + 1) + 1) : R) * (Nat.fib n : R) := by
      simpa only [Nat.add_assoc, hsub, Nat.cast_add, Nat.cast_mul] using
        congrArg (fun a : ℕ => (a : R)) (Nat.fib_add (n * (k + 1)) (n - 1))
    have hsecond : (Nat.fib (n * (k + 1) + n + 1) : R) =
        (Nat.fib (n * (k + 1)) : R) * (Nat.fib n : R) +
          (Nat.fib (n * (k + 1) + 1) : R) * (Nat.fib (n + 1) : R) := by
      simpa only [Nat.cast_add, Nat.cast_mul] using
        congrArg (fun a : ℕ => (a : R)) (Nat.fib_add (n * (k + 1)) n)
    constructor
    · change (Nat.fib (n * ((k + 1) + 1)) : R) = _
      rw [Nat.mul_add, Nat.mul_one, hfirst, ih.1, ih.2]
      calc
        _ = ((k + 1 + 1 : ℕ) : R) * (Nat.fib n : R) *
              (Nat.fib (n + 1) : R) ^ (k + 1) -
            ((k + 1 : ℕ) : R) * (Nat.fib (n + 1) : R) ^ k *
              (Nat.fib n : R) ^ 2 := by
          simp only [hrec, Nat.cast_add, Nat.cast_one, pow_succ]
          ring
        _ = _ := by rw [hz]; ring
    · change (Nat.fib (n * ((k + 1) + 1) + 1) : R) = _
      rw [Nat.mul_add, Nat.mul_one, hsecond, ih.1, ih.2]
      calc
        _ = ((k + 1 : ℕ) : R) * (Nat.fib (n + 1) : R) ^ k *
              (Nat.fib n : R) ^ 2 + (Nat.fib (n + 1) : R) ^ ((k + 1) + 1) := by
          simp only [pow_succ]
          ring
        _ = _ := by rw [hz]; ring

/-- A square factor at a multiple index is inherited from the original value
or is supplied by the multiplier. This includes the prime two and k=0. -/
theorem prime_square_fib_mul_iff (p n k : ℕ) (hp : p.Prime) (hn : 0 < n)
    (hpn : p ∣ Nat.fib n) :
    p ^ 2 ∣ Nat.fib (n * k) ↔ p ^ 2 ∣ Nat.fib n ∨ p ∣ k := by
  cases k with
  | zero => simp
  | succ k =>
    have hz : (Nat.fib n : ZMod (p ^ 2)) ^ 2 = 0 := by
      obtain ⟨u, hu⟩ := hpn
      have hd : p ^ 2 ∣ (Nat.fib n) ^ 2 := ⟨u ^ 2, by rw [hu]; ring⟩
      simpa only [Nat.cast_pow] using
        (ZMod.natCast_eq_zero_iff ((Nat.fib n) ^ 2) (p ^ 2)).mpr hd
    have hpair := (square_zero_pair n k hn hz).1
    have hmod : (Nat.fib (n * (k + 1)) : ZMod (p ^ 2)) =
        (((k + 1) * Nat.fib n * Nat.fib (n + 1) ^ k : ℕ) : ZMod (p ^ 2)) := by
      simpa only [Nat.cast_mul, Nat.cast_pow] using hpair
    have hdiv : p ^ 2 ∣ Nat.fib (n * (k + 1)) ↔
        p ^ 2 ∣ (k + 1) * Nat.fib n * Nat.fib (n + 1) ^ k := by
      rw [← ZMod.natCast_eq_zero_iff (Nat.fib (n * (k + 1))) (p ^ 2),
        ← ZMod.natCast_eq_zero_iff ((k + 1) * Nat.fib n * Nat.fib (n + 1) ^ k) (p ^ 2),
        hmod]
    have hcop : (p ^ 2).Coprime (Nat.fib (n + 1) ^ k) :=
      (((Nat.fib_coprime_fib_succ n).coprime_dvd_left hpn).pow_left 2).pow_right k
    have hcancel : p ^ 2 ∣ (k + 1) * Nat.fib n * Nat.fib (n + 1) ^ k ↔
        p ^ 2 ∣ (k + 1) * Nat.fib n :=
      ⟨hcop.dvd_of_dvd_mul_right, fun h => h.mul_right _⟩
    rw [hdiv, hcancel]
    obtain ⟨u, hu⟩ := hpn
    have hm : (k + 1) * (p * u) = p * ((k + 1) * u) := by ring
    simp only [hu, pow_two, hm, Nat.mul_dvd_mul_iff_left hp.pos, hp.dvd_mul, or_comm]

end D5.S3.Arith.FibonacciDepth.PrimeSquareTransport
