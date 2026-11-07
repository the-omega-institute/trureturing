/- GID: D5/S3/Combinatorics/Geometry/FoldedGridRectangleSeries
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Geometry/FoldedGridRectangleSeries
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Data.Finset.Prod, mathlib/module/Mathlib.Data.Nat.Choose.Cast, mathlib/module/Mathlib.RingTheory.PowerSeries.Inverse]
   utility: none
   digest: The endpoint rectangle count has Barker's joint generating function and recurrence. -/

/-
Source: OEIS A096222 revision 13, Colin Barker's complete conjecture block.
The cardinality below counts placements, rather than a recurrence-defined sequence.
The natural divisions in the side lengths implement floor and ceiling respectively.
All Prop-valued declarations have proof_shape: bind-only; escape_witness: none.
Module admission_basis: open-problem-resolution; settling declaration: result.
Direct frozen D5 dependencies: none. The decisive owners are Mathlib's
Finset.card_product_filter_lt, Nat.cast_choose_two, and
PowerSeries.eq_mul_inv_iff_mul_eq.
Consumers: count -> countQ; countQ -> recurrence, coefficientIdentity;
recurrenceQ -> recurrence; recurrence -> coefficientIdentity, result;
denominator -> coefficientIdentity; denominatorConstant -> gf;
coefficientIdentity -> gf; gf -> result; claim -> result.
-/

import Mathlib.Data.Finset.Prod
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries

open Finset PowerSeries

/-- The number of natural grid-line endpoint rectangles in the folded array. -/
def a (n : ℕ) : ℕ :=
  let r := 2 ^ (n / 2)
  let s := 2 ^ ((n + 1) / 2)
  ((((range (r + 1)) ×ˢ (range (r + 1))).filter (fun p => p.1 < p.2)) ×ˢ
    (((range (s + 1)) ×ˢ (range (s + 1))).filter (fun p => p.1 < p.2))).card

private theorem count (n : ℕ) :
    a n = (2 ^ (n / 2) + 1).choose 2 * (2 ^ ((n + 1) / 2) + 1).choose 2 := by
  simp only [a, card_product, card_product_filter_lt, card_range]

private def q (n : ℕ) : ℚ :=
  (2 : ℚ) ^ (n / 2) * ((2 : ℚ) ^ (n / 2) + 1) *
    (2 : ℚ) ^ ((n + 1) / 2) * ((2 : ℚ) ^ ((n + 1) / 2) + 1) / 4

private theorem countQ (n : ℕ) : (a n : ℚ) = q n := by
  rw [count, Nat.cast_mul, Nat.cast_choose_two, Nat.cast_choose_two]
  push_cast
  simp only [q]
  ring

private theorem recurrenceQ (n : ℕ) :
    q (n + 4) = 6 * q (n + 3) - 48 * q (n + 1) + 64 * q n := by
  have h2 : (n + 2) / 2 = n / 2 + 1 := by omega
  have h3 : (n + 3) / 2 = (n + 1) / 2 + 1 := by omega
  have h4 : (n + 4) / 2 = n / 2 + 2 := by omega
  have h5 : (n + 5) / 2 = (n + 1) / 2 + 2 := by omega
  have h : (n + 1) / 2 = n / 2 ∨ (n + 1) / 2 = n / 2 + 1 := by omega
  simp only [q, show n + 4 + 1 = n + 5 by omega,
    show n + 3 + 1 = n + 4 by omega, show n + 1 + 1 = n + 2 by omega,
    h2, h3, h4, h5]
  rcases h with h | h <;> rw [h] <;> simp only [pow_add] <;> norm_num <;> ring

private theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℤ) = 6 * (a (n - 1) : ℤ) - 48 * (a (n - 3) : ℤ) +
      64 * (a (n - 4) : ℤ) := by
  have h := recurrenceQ (n - 4)
  have h0 : n - 4 + 4 = n := by omega
  have h1 : n - 4 + 3 = n - 1 := by omega
  have h3 : n - 4 + 1 = n - 3 := by omega
  rw [h0, h1, h3, ← countQ, ← countQ, ← countQ, ← countQ] at h
  exact_mod_cast h

/-- The formal series of the literal placement counts, starting at zero. -/
noncomputable def A : PowerSeries ℚ := mk (fun n => (a n : ℚ))

private noncomputable def D : PowerSeries ℚ := (1 - 2 * X) * (1 - 4 * X) * (1 - 8 * X ^ 2)
private noncomputable def N : PowerSeries ℚ := 1 - 3 * X - 9 * X ^ 2 + 24 * X ^ 3

private theorem denominator : D = 1 - 6 * X + 48 * X ^ 3 - 64 * X ^ 4 := by
  unfold D
  ring

private theorem denominatorConstant : constantCoeff D = 1 := by simp [D]

private theorem coefficientIdentity : A * D = N := by
  rw [denominator]
  have hex (F : PowerSeries ℚ) : F * (1 - 6 * X + 48 * X ^ 3 - 64 * X ^ 4) =
      F - 6 * (F * X ^ 1) + 48 * (F * X ^ 3) - 64 * (F * X ^ 4) := by ring
  rw [hex]
  ext n
  simp only [map_sub, map_add, map_mul, coeff_ofNat_mul, coeff_mul_X_pow', A, coeff_mk]
  by_cases hn : 4 ≤ n
  · have h := recurrence n hn
    have hq : (a n : ℚ) = 6 * (a (n - 1) : ℚ) - 48 * (a (n - 3) : ℚ) +
        64 * (a (n - 4) : ℚ) := by exact_mod_cast h
    simp [N, coeff_X_pow, coeff_X, coeff_one, show 1 ≤ n by omega,
      show 3 ≤ n by omega, hn, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega]
    linarith
  · interval_cases n <;> norm_num [N, count, coeff_X, coeff_X_pow, coeff_one, Nat.choose]

private theorem gf : A = N * D⁻¹ := by
  apply (PowerSeries.eq_mul_inv_iff_mul_eq (by rw [denominatorConstant]; norm_num)).2
  exact coefficientIdentity

/-- Barker's two conjectures on the same placement count. -/
def claim : Prop :=
  (A = (1 - 3 * X - 9 * X ^ 2 + 24 * X ^ 3) *
    ((1 - 2 * X) * (1 - 4 * X) * (1 - 8 * X ^ 2))⁻¹) ∧
  (∀ n : ℕ, 4 ≤ n → (a n : ℤ) =
    6 * (a (n - 1) : ℤ) - 48 * (a (n - 3) : ℤ) + 64 * (a (n - 4) : ℤ))

/-- Both source conjectures hold for every indicated natural index. -/
theorem result : claim := ⟨gf, recurrence⟩

end D5.S3.Combinatorics.Geometry.FoldedGridRectangleSeries
