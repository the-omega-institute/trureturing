/- GID: D5/S1/Scale/Lucas
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Lucas traces satisfy the Fibonacci bridge and Pell-type discriminant identity. -/

import D5.S1.Scale.Fibonacci

namespace D5.S1.Scale

open D5.S0.Carrier

/-- The integral Lucas sequence, defined as the trace of powers of `phi`. -/
def goldenLucas (n : ℕ) : ℤ := trace (phi ^ n)

/-- The Lucas definition is the algebraic trace of the corresponding golden power. -/
theorem golden_lucas_eq_trace_phi_pow (n : ℕ) :
    goldenLucas n = trace (phi ^ n) := rfl

/-- The golden coordinate of `phi^n` is the Fibonacci number `F_n`. -/
theorem golden_phi_pow_b_eq_fib_index (n : ℕ) :
    (phi ^ n).b = (Nat.fib n : ℤ) := by
  cases n with
  | zero => simp
  | succ n =>
      simpa [Nat.succ_eq_add_one] using golden_phi_pow_b_eq_fib n

/-- The trace bridge identifies `L_(n+1)` with `F_n + F_(n+2)`. -/
theorem golden_lucas_succ_eq_fib_add_fib (n : ℕ) :
    goldenLucas (n + 1) =
      (Nat.fib n : ℤ) + (Nat.fib (n + 2) : ℤ) := by
  rw [goldenLucas, trace, golden_phi_pow_eq_fib_pair, Nat.fib_add_two]
  push_cast
  ring

/-- In golden coordinates, trace squared minus five times the golden coordinate squared
is four times the norm. -/
theorem golden_trace_discriminant (x : GoldenInt) :
    trace x ^ 2 - 5 * x.b ^ 2 = 4 * norm x := by
  simp [trace, norm]
  ring

/-- The Fibonacci-Lucas discriminant identity over the integers. -/
theorem golden_lucas_discriminant (n : ℕ) :
    goldenLucas n ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 =
      4 * (-1 : ℤ) ^ n := by
  calc
    goldenLucas n ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 =
        trace (phi ^ n) ^ 2 - 5 * (phi ^ n).b ^ 2 := by
          rw [golden_lucas_eq_trace_phi_pow, golden_phi_pow_b_eq_fib_index]
    _ = 4 * norm (phi ^ n) := golden_trace_discriminant (phi ^ n)
    _ = 4 * (-1 : ℤ) ^ n := by rw [norm_phi_pow]

end D5.S1.Scale
