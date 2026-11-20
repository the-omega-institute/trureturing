/- GID: D5/S3/Combinatorics/SubsetSpectrum/IntegralDigitWeights
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SubsetSpectrum/IntegralDigitWeights
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integer coverage beyond the capacity of one fewer digit forces small integral multiples of every weight. -/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S3.Combinatorics.SubsetSpectrum.IntegralDigitWeights

open Finset

private theorem card_le_of_nonintegral_coordinate {J : Type*} [Fintype J] {b levels : ℕ}
    (v : J → Fin b → ℝ) (digits : Fin levels → J → Fin b)
    (calibrated : ∀ k, ∑ j, v j (digits k j) = (k.val : ℝ)) (a : J)
    (separation : ∀ x y, x ≠ y → ¬ ∃ z : ℤ, v a x - v a y = (z : ℝ)) :
    levels ≤ b ^ (Fintype.card J - 1) := by
  classical
  let restrict (k : Fin levels) (i : {j : J // j ≠ a}) := digits k i
  have inj : Function.Injective restrict := by
    intro k l equal
    have outside (j : J) (hj : j ∈ univ.erase a) : digits k j = digits l j :=
      congrFun equal ⟨j, ne_of_mem_erase hj⟩
    have sums_eq : (∑ j ∈ univ.erase a, v j (digits k j)) =
        ∑ j ∈ univ.erase a, v j (digits l j) :=
      sum_congr rfl fun j hj => congrArg (v j) (outside j hj)
    have hk := sum_erase_add _ (fun j => v j (digits k j)) (mem_univ a)
    have hl := sum_erase_add _ (fun j => v j (digits l j)) (mem_univ a)
    rw [calibrated k] at hk
    rw [calibrated l] at hl
    have ha : digits k a = digits l a := by
      by_contra h
      apply separation _ _ h
      use ((k.val : ℤ) - (l.val : ℤ))
      push_cast
      linarith
    rw [ha, sums_eq, hl] at hk
    exact Fin.ext (by exact_mod_cast hk.symm)
  have hc := Fintype.card_le_of_injective restrict inj
  have hdelete : Fintype.card {j : J // j ≠ a} = Fintype.card J - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  simpa [Fintype.card_fun, hdelete] using hc


/-- If the calibrated levels cannot fit after deleting one digit coordinate, then each weight
has an integral multiple whose multiplier is positive and smaller than the digit alphabet. -/
theorem exists_integral_multiple_of_capacity_gap {J : Type*} [Fintype J] {b levels : ℕ}
    (weight : J → ℝ) (digits : Fin levels → J → Fin b)
    (calibrated : ∀ k, ∑ j, ((digits k j).val : ℝ) * weight j = (k.val : ℝ))
    (gap : b ^ (Fintype.card J - 1) < levels) (j : J) :
    ∃ d : ℕ, 0 < d ∧ d < b ∧ ∃ z : ℤ, (d : ℝ) * weight j = (z : ℝ) := by
  by_contra outside
  have separation (x y : Fin b) (different : x ≠ y) :
      ¬ ∃ z : ℤ, (x.val : ℝ) * weight j - (y.val : ℝ) * weight j = (z : ℝ) := by
    rintro ⟨z, hz⟩
    have lt_or_gt : x.val < y.val ∨ y.val < x.val := lt_or_gt_of_ne
      (fun he => different (Fin.ext he))
    apply outside
    rcases lt_or_gt with h | h
    · refine ⟨y.val - x.val, Nat.sub_pos_of_lt h, (Nat.sub_le _ _).trans_lt y.isLt, -z, ?_⟩
      rw [Nat.cast_sub h.le, sub_mul, Int.cast_neg]
      linarith only [hz]
    · refine ⟨x.val - y.val, Nat.sub_pos_of_lt h, (Nat.sub_le _ _).trans_lt x.isLt, z, ?_⟩
      rwa [Nat.cast_sub h.le, sub_mul]
  exact (not_le_of_gt gap) (card_le_of_nonintegral_coordinate
    (fun j d => (d.val : ℝ) * weight j) digits calibrated j separation)

end D5.S3.Combinatorics.SubsetSpectrum.IntegralDigitWeights
