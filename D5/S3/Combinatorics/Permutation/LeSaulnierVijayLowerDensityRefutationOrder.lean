/- GID: D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: none
   digest: Binary reversal ranks avoid monotone three-term arithmetic progressions. -/

import Mathlib.Algebra.Order.Ring.Nat
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationOrder

/-- Reverse the lowest `bits` binary digits, discarding all higher digits. -/
def rank : ℕ → ℕ → ℕ
  | 0, _ => 0
  | bits + 1, x => x % 2 * 2 ^ bits + rank bits (x / 2)

/-- The reversed digits always fit into the same number of bits. -/
theorem rank_lt (bits x : ℕ) : rank bits x < 2 ^ bits := by
  induction bits generalizing x with
  | zero => simp [rank]
  | succ bits ih =>
      have hr := ih (x / 2)
      have hm := Nat.mod_lt x (by omega : 0 < 2)
      simp only [rank, pow_succ]
      rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hm | hm <;> rw [hm] <;> omega

/-- Binary reversal is injective on the integers representable with `bits` bits. -/
theorem rank_injective {bits x y : ℕ} (hx : x < 2 ^ bits) (hy : y < 2 ^ bits)
    (h : rank bits x = rank bits y) : x = y := by
  induction bits generalizing x y with
  | zero => simp only [pow_zero] at hx hy; omega
  | succ bits ih =>
      have hxp : x / 2 < 2 ^ bits := by rw [pow_succ] at hx; omega
      have hyp : y / 2 < 2 ^ bits := by rw [pow_succ] at hy; omega
      have hxr := rank_lt bits (x / 2)
      have hyr := rank_lt bits (y / 2)
      have hxm := Nat.mod_lt x (by omega : 0 < 2)
      have hym := Nat.mod_lt y (by omega : 0 < 2)
      simp only [rank] at h
      have hm : x % 2 = y % 2 := by
        rcases (by omega : x % 2 = 0 ∨ x % 2 = 1) with hxm | hxm <;>
          rcases (by omega : y % 2 = 0 ∨ y % 2 = 1) with hym | hym <;>
          rw [hxm, hym] at h <;> omega
      have hq : rank bits (x / 2) = rank bits (y / 2) := by rw [hm] at h; omega
      have he := ih hxp hyp hq
      omega

/-- An arithmetic progression cannot occur in strictly increasing binary-reversal order.
The endpoints need not be listed in numerical order. -/
theorem rank_no_ap {bits a b c : ℕ} (ha : a < 2 ^ bits) (hb : b < 2 ^ bits)
    (hc : c < 2 ^ bits) (hap : a + c = 2 * b) :
    ¬(rank bits a < rank bits b ∧ rank bits b < rank bits c) := by
  induction bits generalizing a b c with
  | zero => simp [rank]
  | succ bits ih =>
      intro hord
      have haq : a / 2 < 2 ^ bits := by rw [pow_succ] at ha; omega
      have hbq : b / 2 < 2 ^ bits := by rw [pow_succ] at hb; omega
      have hcq : c / 2 < 2 ^ bits := by rw [pow_succ] at hc; omega
      have har := rank_lt bits (a / 2)
      have hbr := rank_lt bits (b / 2)
      have hcr := rank_lt bits (c / 2)
      have ham := Nat.mod_lt a (by omega : 0 < 2)
      have hbm := Nat.mod_lt b (by omega : 0 < 2)
      have hcm := Nat.mod_lt c (by omega : 0 < 2)
      have hacm : a % 2 = c % 2 := by omega
      simp only [rank] at hord
      by_cases habm : a % 2 = b % 2
      · have hqm : a / 2 + c / 2 = 2 * (b / 2) := by omega
        apply ih haq hbq hcq hqm
        rw [← habm, ← hacm] at hord
        omega
      · rcases (by omega : a % 2 = 0 ∨ a % 2 = 1) with ham | ham <;>
          rcases (by omega : b % 2 = 0 ∨ b % 2 = 1) with hbm | hbm <;>
          rw [← hacm, ham, hbm] at hord <;> omega

end D5.S3.Combinatorics.Permutation.LeSaulnierVijayLowerDensityRefutationOrder
