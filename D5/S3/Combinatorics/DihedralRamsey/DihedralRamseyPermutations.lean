/- GID: D5/S3/Combinatorics/DihedralRamsey/DihedralRamseyPermutations
   generality: G
   mirror-B: D5/B/S3/Combinatorics/DihedralRamsey/DihedralRamseyPermutations
   mirror-E: none(waiver:cyclic-order-permutations)
   anchors: [mathlib/module/Mathlib.Data.Nat.Dist, mathlib/module/Mathlib.Data.Nat.ModEq]
   utility: none
   digest: Dihedral permutations preserve circular adjacency and are injective. -/

import D5.S3.Combinatorics.DihedralRamsey.DihedralRamseyDefs
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Nat.ModEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.DihedralRamsey

open DihedralRamseyDefs

theorem dihedralPerm_injective (k s : ℕ) (refl : Bool) :
    Function.Injective (dihedralPerm (k := k) s refl) := by
  intro i j hij
  have heq := congrArg Fin.val hij
  dsimp [dihedralPerm] at heq
  have hc := Nat.ModEq.add_right_cancel' s heq
  cases refl <;> simp only [Bool.false_eq_true, if_false, if_true] at hc
  · exact Fin.ext (hc.eq_of_lt_of_lt i.isLt j.isLt)
  · have hi := i.isLt
    have hj := j.isLt
    have hp := hc.eq_of_lt_of_lt (by omega) (by omega)
    apply Fin.ext
    omega

theorem dihedralPerm_val {k : ℕ} (s : ℕ) (refl : Bool) (x : Fin k) : (dihedralPerm s refl x).val =
      if (if refl then k - 1 - x.val else x.val) + s % k < k then
        (if refl then k - 1 - x.val else x.val) + s % k else
        (if refl then k - 1 - x.val else x.val) + s % k - k := by
  have hrot : ∀ z : ℕ, z < k → (z + s) % k =
      if z + s % k < k then z + s % k else z + s % k - k := by
    intro z hz
    rw [Nat.add_mod, Nat.mod_eq_of_lt hz]
    have hs : s % k < k := Nat.mod_lt _ (by have := x.isLt; omega)
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [Nat.mod_eq_sub_mod (by have := x.isLt; omega)]
      exact Nat.mod_eq_of_lt (by have := x.isLt; omega)
  dsimp [dihedralPerm]
  apply hrot
  cases refl <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
    have hx := x.isLt <;> omega

theorem dihedralPerm_circular {k : ℕ} (hk : 2 ≤ k) (s : ℕ) (refl : Bool) :
    ∀ x y : Fin k,
        (Nat.dist x.val y.val = 1 ∨ Nat.dist x.val y.val = k - 1) ↔
        (Nat.dist (dihedralPerm s refl x).val (dihedralPerm s refl y).val = 1 ∨
          Nat.dist (dihedralPerm s refl x).val (dihedralPerm s refl y).val = k - 1) := by
  intro x y
  have h₁ := dihedralPerm_val s refl x
  have h₂ := dihedralPerm_val s refl y
  have hx := x.isLt
  have hy := y.isLt
  have hs : s % k < k := Nat.mod_lt _ (by omega)
  unfold Nat.dist
  cases refl <;> simp only [Bool.false_eq_true, ↓reduceIte] at h₁ h₂ <;>
    split_ifs at h₁ h₂ <;> omega

end D5.S3.Combinatorics.DihedralRamsey
