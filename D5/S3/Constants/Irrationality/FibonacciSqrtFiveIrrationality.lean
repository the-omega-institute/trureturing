/- GID: D5/S3/Constants/Irrationality/FibonacciSqrtFiveIrrationality
   generality: I
   mirror-B: D5/B/S3/Constants/Irrationality/FibonacciSqrtFiveIrrationality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Odd Fibonacci-square-root-five layer constants are irrational. -/

/- Library-search audit trail (2026-08-17):
   * No equivalent declaration was found in D5.
   * Pinned mathlib provides `Nat.Prime.irrational_sqrt`, `Irrational.natCast_mul`,
     `Irrational.inv`, and `Nat.fib_pos`; the proof below composes these directly.
   * No exact declaration for the full reciprocal Fibonacci-square-root-five expression
     was found by local source search.
-/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.Irrational

namespace D5.S3.Constants.Irrationality.FibonacciSqrtFiveIrrationality

/-- The odd-layer expression `1 / (F_m * sqrt 5)` is irrational. -/
theorem odd_layer_constant_irrational (m : ℕ) (hm : Odd m) :
    Irrational (1 / ((Nat.fib m : ℝ) * Real.sqrt 5)) := by
  have hm_pos : 0 < m := by
    obtain ⟨k, hk⟩ := hm
    omega
  have hfib_ne : Nat.fib m ≠ 0 := (Nat.fib_pos.mpr hm_pos).ne'
  have hsqrt : Irrational (Real.sqrt 5) :=
    (by decide : Nat.Prime 5).irrational_sqrt
  have hproduct : Irrational ((Nat.fib m : ℝ) * Real.sqrt 5) :=
    hsqrt.natCast_mul hfib_ne
  simpa only [one_div] using hproduct.inv

#print axioms odd_layer_constant_irrational

end D5.S3.Constants.Irrationality.FibonacciSqrtFiveIrrationality
