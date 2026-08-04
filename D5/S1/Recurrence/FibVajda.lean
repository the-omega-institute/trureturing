/- GID: D5/S1/Recurrence/FibVajda
   generality: I
   mirror-B: D5/B/S1/Recurrence/FibVajda
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Vajda's identity relates shifted Fibonacci products over the integers. -/

import Mathlib

namespace D5.S1.Recurrence.FibVajda

/- Provenance: Native proof over pinned mathlib. -/

/-- Vajda's identity for natural-number indices under the convention `F_0 = 0`, `F_1 = 1`.
All Fibonacci values are coerced to `ℤ` so that subtraction and `(-1)^n` are literal integer
operations. This statement does not extend the three index parameters to negative integers. -/
theorem fib_vajda (n i j : ℕ) :
    (Nat.fib (n + i) : ℤ) * (Nat.fib (n + j) : ℤ) -
        (Nat.fib n : ℤ) * (Nat.fib (n + i + j) : ℤ) =
      (-1 : ℤ) ^ n * (Nat.fib i : ℤ) * (Nat.fib j : ℤ) := by
  cases n with
  | zero => simp
  | succ n =>
    have hgZ : (Nat.fib (i + j) : ℤ) =
        Nat.fib i * Nat.fib (j + 1) + Nat.fib (i + 1) * Nat.fib j -
          Nat.fib i * Nat.fib j := by
      have h1 : Nat.fib (i + j + 2) = Nat.fib (i + j) + Nat.fib (i + j + 1) :=
        Nat.fib_add_two
      have h2 : Nat.fib (i + j + 1) =
          Nat.fib i * Nat.fib j + Nat.fib (i + 1) * Nat.fib (j + 1) :=
        Nat.fib_add i j
      have h3 := Nat.fib_add i (j + 1)
      rw [show i + (j + 1) + 1 = i + j + 2 by omega,
          show j + 1 + 1 = j + 2 by omega] at h3
      have h4 : Nat.fib (j + 2) = Nat.fib j + Nat.fib (j + 1) := Nat.fib_add_two
      nlinarith [h1, h2, h3, h4]
    have hcassini : (Nat.fib (n + 1) : ℤ) ^ 2 -
        Nat.fib n * Nat.fib (n + 1) - (Nat.fib n : ℤ) ^ 2 = (-1 : ℤ) ^ n := by
      have hcat := Int.fib_add_sq_sub_fib_mul_fib_add_two_mul (n : ℤ) 1
      have hfn2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      have hfn2Z : (Nat.fib (n + 2) : ℤ) = Nat.fib n + Nat.fib (n + 1) := by
        exact_mod_cast hfn2
      norm_num at hcat
      rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega,
          show (n : ℤ) + 2 = ((n + 2 : ℕ) : ℤ) by omega] at hcat
      simp only [Int.fib_natCast] at hcat
      nlinarith [hcat, hfn2Z]
    rw [show n + 1 + i = n + i + 1 by omega,
        show n + 1 + j = n + j + 1 by omega,
        show n + i + 1 + j = n + (i + j) + 1 by omega]
    have ha := Nat.fib_add n i
    have hb := Nat.fib_add n j
    have hc := Nat.fib_add n (i + j)
    have hsign : (-1 : ℤ) ^ (n + 1) = -((-1 : ℤ) ^ n) := by ring
    have haZ : (Nat.fib (n + i + 1) : ℤ) = Nat.fib n * Nat.fib i +
        Nat.fib (n + 1) * Nat.fib (i + 1) := by
      exact_mod_cast ha
    have hbZ : (Nat.fib (n + j + 1) : ℤ) = Nat.fib n * Nat.fib j +
        Nat.fib (n + 1) * Nat.fib (j + 1) := by
      exact_mod_cast hb
    have hcZ : (Nat.fib (n + (i + j) + 1) : ℤ) = Nat.fib n * Nat.fib (i + j) +
        Nat.fib (n + 1) * Nat.fib (i + j + 1) := by
      exact_mod_cast hc
    have hijZ : (Nat.fib (i + j + 1) : ℤ) = Nat.fib i * Nat.fib j +
        Nat.fib (i + 1) * Nat.fib (j + 1) := by
      exact_mod_cast Nat.fib_add i j
    have halg : (Nat.fib (n + i + 1) : ℤ) * Nat.fib (n + j + 1) -
        Nat.fib (n + 1) * Nat.fib (n + (i + j) + 1) =
        -((Nat.fib (n + 1) : ℤ) ^ 2 - Nat.fib n * Nat.fib (n + 1) -
          (Nat.fib n : ℤ) ^ 2) * Nat.fib i * Nat.fib j := by
      rw [haZ, hbZ, hcZ, hgZ, hijZ]
      ring
    rw [hsign, halg, hcassini]

end D5.S1.Recurrence.FibVajda
