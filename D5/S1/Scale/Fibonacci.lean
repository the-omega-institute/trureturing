/- GID: D5/S1/Scale/Fibonacci
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Golden powers have Fibonacci coordinates and imply Cassini's identity. -/

import D5.S0.Carrier.Units
import Mathlib.Data.Nat.Fib.Basic

namespace D5.S1.Scale

open D5.S0.Carrier

/-- The coordinates of each positive power of `phi` are consecutive Fibonacci numbers. -/
theorem golden_phi_pow_eq_fib_pair (n : ℕ) :
    phi ^ (n + 1) =
      ⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ := by
  induction n with
  | zero =>
      ext <;> simp [phi]
  | succ n ih =>
      rw [pow_succ, ih]
      ext <;> simp [Nat.fib_add_two]

/-- The integral coordinate of `phi^(n+1)` is `F_n`. -/
theorem golden_phi_pow_a_eq_fib (n : ℕ) :
    (phi ^ (n + 1)).a = (Nat.fib n : ℤ) := by
  rw [golden_phi_pow_eq_fib_pair]

/-- The golden coordinate of `phi^(n+1)` is `F_(n+1)`. -/
theorem golden_phi_pow_b_eq_fib (n : ℕ) :
    (phi ^ (n + 1)).b = (Nat.fib (n + 1) : ℤ) := by
  rw [golden_phi_pow_eq_fib_pair]

/-- Cassini's identity over the integers, obtained by taking norms of the bridge identity. -/
theorem fib_cassini_from_golden_norm (n : ℕ) :
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) -
        (Nat.fib (n + 1) : ℤ) ^ 2 =
      (-1 : ℤ) ^ (n + 1) := by
  calc
    (Nat.fib n : ℤ) * (Nat.fib (n + 2) : ℤ) -
          (Nat.fib (n + 1) : ℤ) ^ 2 =
        norm (⟨(Nat.fib n : ℤ), (Nat.fib (n + 1) : ℤ)⟩ : GoldenInt) := by
          rw [Nat.fib_add_two]
          simp [norm]
          ring
    _ = norm (phi ^ (n + 1)) := by
      rw [golden_phi_pow_eq_fib_pair]
    _ = (-1 : ℤ) ^ (n + 1) := norm_phi_pow (n + 1)

end D5.S1.Scale
