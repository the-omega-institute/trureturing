/- GID: D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceDensityCrossing
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Real finite-product extension of adjacent Fibonacci source densities. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import D5.S1.Scale.Fibonacci
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing

open scoped BigOperators
open Filter Set

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

/-- Adjacent density ratio on the integer grid, extended by real finite products. -/
noncomputable def q (k j : ℕ) (t : ℝ) : ℝ :=
  (t - j) * H k j t / (j + 1)

/-- Leading finite-product coefficient. -/
noncomputable def c (k : ℕ) : ℝ :=
  (A k : ℝ) ^ E k * (D k : ℝ) ^ A k /
    ((4 : ℝ) ^ D k * (L k : ℝ) ^ D k)

/-- Density of the iterated substitution image in its actual composition fiber. -/
noncomputable def sourceDensity (k t i : ℕ) : ℝ :=
  (GenealogicalFiberTransport.fiberCount (t - i, i) : ℝ) /
    (GenealogicalFiberTransport.fiberCount
      (GraftAffineClosure.step^[3 * k] (t - i, i)) : ℝ)

/-- The six clauses of the real crossing and integer source-density bridge. -/
def Conclusion (k j : ℕ) : Prop :=
  0 < c k ∧
  StrictMonoOn (q k j) (Ici ((j : ℝ) + 1)) ∧
  Tendsto (fun t : ℝ => q k j t / t) atTop (nhds (c k / (j + 1))) ∧
  (∃! τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1) ∧
  (∃ τ : ℝ, τ ∈ Ici ((j : ℝ) + 1) ∧ q k j τ = 1 ∧
    2 * j + 1 < τ ∧ τ < j + (j + 1) / c k ∧
    ∀ t : ℕ, j + 1 ≤ t →
      (q k j t < 1 ↔ (t : ℝ) < τ) ∧
      (q k j t = 1 ↔ (t : ℝ) = τ) ∧
      (1 < q k j t ↔ τ < (t : ℝ))) ∧
  (∀ t : ℕ, j + 1 ≤ t →
    q k j t = sourceDensity k t (j + 1) / sourceDensity k t j)

end D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing
