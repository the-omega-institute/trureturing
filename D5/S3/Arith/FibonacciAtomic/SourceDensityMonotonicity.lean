/- GID: D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Shared definitions for real Fibonacci source density ratios. -/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SourceDensityMonotonicity

open scoped BigOperators

/-- The two numerator lengths, denominator length, and total composition coefficient. -/
def E (k : ℕ) : ℕ := Nat.fib (3 * k - 2)
def A (k : ℕ) : ℕ := Nat.fib (3 * k - 1)
def D (k : ℕ) : ℕ := Nat.fib (3 * k)
def L (k : ℕ) : ℕ := Nat.fib (3 * k + 1)

/-- Target alpha, beta, and total coordinates for the fixed ancestor minority. -/
def a (k j : ℕ) (t : ℝ) : ℝ := A k * t + E k * j
def b (k j : ℕ) (t : ℝ) : ℝ := D k * t + A k * j
def n (k j : ℕ) (t : ℝ) : ℝ := L k * t + D k * j

/-- Rising finite product; nonintegral arguments are auxiliary real parameters. -/
noncomputable def rising (x : ℝ) (m : ℕ) : ℝ :=
  ∏ i ∈ Finset.range m, (x + i)

/-- The real finite-product factor, with no interpretation as a nonintegral tree count. -/
noncomputable def H (k j : ℕ) (t : ℝ) : ℝ :=
  rising (a k j t + 1) (E k) * rising (b k j t + 1) (A k) /
    ((4 : ℝ) ^ D k * rising (n k j t - 1 / 2) (D k))

/-- Real finite-product ratio with auxiliary nonintegral arguments. -/
noncomputable def q (k j : ℕ) (t : ℝ) : ℝ :=
  (t - j) * H k j t / (j + 1)

/-- Leading finite-product coefficient. -/
noncomputable def c (k : ℕ) : ℝ :=
  (A k : ℝ) ^ E k * (D k : ℝ) ^ A k /
    ((4 : ℝ) ^ D k * (L k : ℝ) ^ D k)

/-- Explicit logarithmic derivative of the finite-product extension. -/
noncomputable def g (k j : ℕ) (t : ℝ) : ℝ :=
  1 / (t - j) +
    A k * (∑ i ∈ Finset.range (E k), 1 / (a k j t + 1 + i)) +
    D k * (∑ i ∈ Finset.range (A k), 1 / (b k j t + 1 + i)) -
    L k * (∑ i ∈ Finset.range (D k), 1 / (n k j t - 1 / 2 + i))

/-- Lower envelope combining both numerator errors and the shifted denominator error. -/
noncomputable def lowerEnvelope (k j : ℕ) (t : ℝ) : ℝ :=
  1 / (t - j) - (j + 1 / 2) / ((L k : ℝ) * A k * D k * t ^ 2) -
    (A k : ℝ) * E k / (2 * a k j t * (a k j t + E k)) -
    (D k : ℝ) * A k / (2 * b k j t * (b k j t + A k)) -
    (L k : ℝ) * D k / ((n k j t - 1 / 2) * (n k j t + D k - 1 / 2))

end D5.S3.Arith.FibonacciAtomic.SourceDensityMonotonicity
