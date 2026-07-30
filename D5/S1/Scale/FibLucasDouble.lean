/- GID: D5/S1/Scale/FibLucasDouble
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fibonacci doubling is multiplication by the corresponding Lucas number. -/

import D5.S1.Scale.Lucas

namespace D5.S1.Scale

open D5.S0.Carrier

/-- The Fibonacci-Lucas doubling identity over the integers. -/
theorem golden_fib_two_mul_eq_fib_mul_lucas (n : ℕ) :
    (Nat.fib (2 * n) : ℤ) = (Nat.fib n : ℤ) * goldenLucas n := by
  calc
    (Nat.fib (2 * n) : ℤ) = (phi ^ (2 * n)).b :=
      (golden_phi_pow_b_eq_fib_index (2 * n)).symm
    _ = ((phi ^ n) * (phi ^ n)).b := by
      rw [show 2 * n = n + n by omega, pow_add]
    _ = (phi ^ n).b * trace (phi ^ n) := by
      simp only [b_mul, trace]
      ring
    _ = (Nat.fib n : ℤ) * goldenLucas n := by
      rw [golden_phi_pow_b_eq_fib_index, golden_lucas_eq_trace_phi_pow]

end D5.S1.Scale
