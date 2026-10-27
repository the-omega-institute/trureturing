/- GID: D5/S3/CharacterSums/CubicEulerWilson
   generality: G
   mirror-B: D5/B/S3/CharacterSums/CubicEulerWilson
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Cubic Euler coefficient extraction and the Wilson inverse-factorial cube. -/

import D5.S3.Arith.Wilson
import Mathlib.Data.ZMod.Factorial
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring

/-! Wilson's factorial cube and the double-exponent cubic Euler sum.

The finite-field sum has arbitrary prime-power cardinality. The factorial
identity is transported from the prime field to every field of characteristic p.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators

namespace D5.S3.CharacterSums.CubicEulerWilson

/-- The factorial used in the cube witness is nonzero in characteristic p. -/
private theorem factorial_cast_ne_zero_of_lt
    {F : Type*} [Field F] (p m : ℕ) [Fact p.Prime] [CharP F p]
    (hmp : m < p) : (m.factorial : F) ≠ 0 := by
  intro hzero
  have hdvd : p ∣ m.factorial := (CharP.cast_eq_zero_iff F p m.factorial).mp hzero
  exact (not_le_of_gt hmp) ((Fact.out : p.Prime).dvd_factorial.mp hdvd)


private theorem neg_binomial_eq_inverse_factorial_cube_zmod
    (p m : ℕ) [Fact p.Prime] (hpm : p = 3 * m + 1) (hm : Even m) :
    -((2 * m).choose m : ZMod p) = ((m.factorial : ZMod p)⁻¹) ^ 3 := by
  have hsub : p - 1 - m = 2 * m := by omega
  have hdesc : ((p - 1).descFactorial m : ZMod p) = (m.factorial : ZMod p) := by
    rw [ZMod.cast_descFactorial (by omega : m ≤ p), hm.neg_one_pow, one_mul]
  have hw : ((2 * m).factorial : ZMod p) * (m.factorial : ZMod p) = -1 := by
    have hwil := D5.S3.Arith.Wilson.wilson_theorem p (Fact.out : p.Prime)
    have H := congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.factorial_mul_descFactorial (by omega : m ≤ p - 1))
    simpa only [Nat.cast_mul, hsub, hdesc, hwil] using H
  have hn : (m.factorial : ZMod p) ≠ 0 :=
    factorial_cast_ne_zero_of_lt p m (by omega)
  have hc : ((2 * m).choose m : ZMod p) * (m.factorial : ZMod p) ^ 2 =
      ((2 * m).factorial : ZMod p) := by
    have H := congrArg (fun n : ℕ => (n : ZMod p))
      (Nat.choose_mul_factorial_mul_factorial (by omega : m ≤ 2 * m))
    simpa only [Nat.cast_mul, show 2 * m - m = m by omega, pow_two, mul_assoc] using H
  have H : -((2 * m).choose m : ZMod p) * (m.factorial : ZMod p) ^ 3 = 1 := by
    calc
      _ = -((((2 * m).choose m : ZMod p) * (m.factorial : ZMod p) ^ 2) *
          (m.factorial : ZMod p)) := by ring
      _ = 1 := by rw [hc, hw, neg_neg]
  apply mul_left_injective₀ (pow_ne_zero 3 hn)
  change -((2 * m).choose m : ZMod p) * (m.factorial : ZMod p) ^ 3 =
    ((m.factorial : ZMod p)⁻¹) ^ 3 * (m.factorial : ZMod p) ^ 3
  rw [H, ← mul_pow, inv_mul_cancel₀ hn, one_pow]

/-- Transport the retained Wilson identity through the canonical prime-field
map; the finite field need not be identified with ZMod p by an equivalence. -/
theorem neg_binomial_eq_inverse_factorial_cube
    {F : Type*} [Field F] (p m : ℕ) [Fact p.Prime] [CharP F p]
    (hpm : p = 3 * m + 1) (hm : Even m) :
    -((2 * m).choose m : F) = ((m.factorial : F)⁻¹) ^ 3 := by
  let f : ZMod p →+* F := ZMod.castHom (dvd_refl p) F
  have H := congrArg f (neg_binomial_eq_inverse_factorial_cube_zmod p m hpm hm)
  simpa only [map_neg, map_natCast, map_pow, map_inv₀] using H


open Finset

/-- The full positive-exponent power sum, obtained from Mathlib's unit-group
formula. The zero element contributes zero since i is positive.
The units-to-nonzero-elements calculation reuses the proof in
Mathlib.FieldTheory.Finite.Basic.sum_pow_lt_card_sub_one. -/
private theorem sum_pow_positive (F : Type*) [Field F] [Fintype F]
    (i : ℕ) (hi : i ≠ 0) :
    (∑ x : F, x ^ i) = if Fintype.card F - 1 ∣ i then -1 else 0 := by
  classical
  let φ : Fˣ ↪ F := ⟨fun x => x, Units.val_injective⟩
  have huniv : univ.map φ = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton, φ] using! isUnit_iff_ne_zero
  calc
    ∑ x : F, x ^ i = ∑ x ∈ univ \ {(0 : F)}, x ^ i := by
      rw [← sum_sdiff ({0} : Finset F).subset_univ, sum_singleton, zero_pow hi, add_zero]
    _ = ∑ x : Fˣ, (x ^ i : F) := by simp [φ, ← huniv, univ.sum_map φ]
    _ = _ := FiniteField.sum_pow_units F i

/-- In the binomial expansion only the exponent 3m survives. This statement
uses the field cardinality and the parity actually needed for its sign. -/
theorem sum_double_cubic_euler (F : Type*) [Field F] [Fintype F]
    (m : ℕ) (hcard : Fintype.card F = 3 * m + 1) (hm : Even m) :
    (∑ x : F, x ^ (2 * m) * (1 - x) ^ (2 * m)) =
      -((2 * m).choose m : F) := by
  classical
  have hq : 1 < Fintype.card F := Fintype.one_lt_card
  have hmpos : 0 < m := by omega
  have hmodulus : Fintype.card F - 1 = 3 * m := by omega
  have hdiv (i : ℕ) (hi : i ≤ 2 * m) :
      Fintype.card F - 1 ∣ 2 * m + i ↔ i = m := by
    rw [hmodulus]
    constructor
    · rintro ⟨k, hk⟩
      have hkpos : 0 < k := by
        by_contra h
        have hk0 : k = 0 := by omega
        subst k
        omega
      have hklt : k < 2 := by
        by_contra h
        have hmul : (3 * m) * 2 ≤ (3 * m) * k :=
          Nat.mul_le_mul_left (3 * m) (by omega : 2 ≤ k)
        omega
      have hk1 : k = 1 := by omega
      subst k
      omega
    · intro h
      subst i
      exact ⟨1, by omega⟩
  calc
    _ = ∑ x : F, ∑ i ∈ range (2 * m + 1),
        ((2 * m).choose i : F) * (-1 : F) ^ i * x ^ (2 * m + i) := by
      apply sum_congr rfl
      intro x hx
      rw [show (1 : F) - x = -x + 1 by ring, add_pow, mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [neg_pow, one_pow, mul_one, pow_add]
      ring
    _ = ∑ i ∈ range (2 * m + 1),
        ((2 * m).choose i : F) * (-1 : F) ^ i * (∑ x : F, x ^ (2 * m + i)) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro i hi
      rw [mul_sum]
    _ = ∑ i ∈ range (2 * m + 1),
        if i = m then -((2 * m).choose m : F) else 0 := by
      apply sum_congr rfl
      intro i hi
      have hi' : i ≤ 2 * m := by have := mem_range.mp hi; omega
      rw [sum_pow_positive F (2 * m + i) (by omega)]
      simp only [hdiv i hi']
      by_cases him : i = m
      · subst i
        simp [hm.neg_one_pow]
      · simp [him]
    _ = -((2 * m).choose m : F) := by
      simp [show m < 2 * m + 1 by omega]

end D5.S3.CharacterSums.CubicEulerWilson
