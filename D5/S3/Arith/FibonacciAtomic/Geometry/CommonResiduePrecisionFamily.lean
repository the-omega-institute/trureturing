/- GID: D5/S3/Arith/FibonacciAtomic/Geometry/CommonResiduePrecisionFamily
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Geometry/CommonResiduePrecisionFamily
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A common integer residue class preserves nonunit denominator precision. -/

import D5.S3.Arith.FibonacciAtomic.SourceDensityCrossing
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Padics.PadicVal.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily

open scoped BigOperators
open SourceDensityMonotonicity

/-- Integer numerator of the adjacent source-density ratio, with minority count `m = j+1`. -/
def numerator (k : ℕ) (t m : ℤ) : ℤ :=
  (t - m + 1) * (∏ r ∈ Finset.range (E k), ((A k : ℤ) * t + E k * m - r)) *
    ∏ s ∈ Finset.range (A k), ((D k : ℤ) * t + A k * m - s)

/-- The actual, possibly nonunit, integer denominator. -/
def denominator (k : ℕ) (t m : ℤ) : ℤ :=
  2 ^ D k * m * ∏ h ∈ Finset.range (D k),
    (2 * (L k : ℤ) * t + 2 * D k * m - 2 * D k + 2 * h - 1)

/-- Quadratic numerator coefficient at the origin. -/
def G (k : ℕ) : ℕ := A k * D k * (E k - 1).factorial * (A k - 1).factorial

/-- Linear denominator coefficient at the origin. -/
def K (k : ℕ) : ℕ := 2 ^ D k * ∏ h ∈ Finset.range (D k), (2 * h + 3)

private def reducedNumerator (k : ℕ) (z : ℤ) : ℤ :=
  (K k * z - G k * K k * z ^ 2 + 1) *
    ((A k : ℤ) * K k + E k * G k * K k * z) *
    ((D k : ℤ) * K k + A k * G k * K k * z) *
    (∏ r ∈ Finset.range (E k - 1),
      ((A k : ℤ) * K k * z + E k * G k * K k * z ^ 2 - (r + 1))) *
    ∏ s ∈ Finset.range (A k - 1),
      ((D k : ℤ) * K k * z + A k * G k * K k * z ^ 2 - (s + 1))

private def reducedDenominator (k : ℕ) (z : ℤ) : ℤ :=
  2 ^ D k * (G k : ℤ) * K k * ∏ h ∈ Finset.range (D k),
    (2 * (L k : ℤ) * K k * z + 2 * D k * G k * K k * z ^ 2 -
      2 * D k + 2 * h - 1)

private theorem lengths (k : ℕ) (hk : 1 ≤ k) :
    0 < E k ∧ 0 < A k ∧ 0 < D k ∧ 0 < L k ∧
    D k = E k + A k ∧ Even (D k) := by
  have he : 0 < E k := Nat.fib_pos.mpr (by omega)
  have ha : 0 < A k := Nat.fib_pos.mpr (by omega)
  have hd : 0 < D k := Nat.fib_pos.mpr (by omega)
  have hl : 0 < L k := Nat.fib_pos.mpr (by omega)
  have hsum : D k = E k + A k := by
    simpa [D, E, A, show 3 * k = (3 * k - 2) + 2 by omega,
      show 3 * k - 1 = (3 * k - 2) + 1 by omega] using
      Nat.fib_add_two (3 * k - 2)
  have hdiv : 2 ∣ D k := by
    simpa [D] using Nat.fib_dvd (show 3 ∣ 3 * k from dvd_mul_right 3 k)
  exact ⟨he, ha, hd, hl, hsum, even_iff_two_dvd.mpr hdiv⟩

private theorem seed_factorization (k : ℕ) (hk : 1 ≤ k) (z : ℤ) :
    numerator k (K k * z) (G k * K k * z ^ 2) = z ^ 2 * reducedNumerator k z ∧
    denominator k (K k * z) (G k * K k * z ^ 2) = z ^ 2 * reducedDenominator k z := by
  obtain ⟨he, ha, _, _, _, _⟩ := lengths k hk
  constructor
  · unfold numerator reducedNumerator
    rw [show E k = (E k - 1) + 1 by omega, Finset.prod_range_succ']
    rw [show A k = (A k - 1) + 1 by omega, Finset.prod_range_succ']
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, sub_zero]
    ring
  · unfold denominator reducedDenominator
    simp only [mul_assoc]
    ring

end D5.S3.Arith.FibonacciAtomic.Geometry.CommonResiduePrecisionFamily
