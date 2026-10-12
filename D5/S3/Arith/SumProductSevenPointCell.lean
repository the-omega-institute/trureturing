/- GID: D5/S3/Arith/SumProductSevenPointCell
   generality: G
   mirror-B: D5/B/S3/Arith/SumProductSevenPointCell
   mirror-E: none(waiver:sum-product-exclusion)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Seven positive real numbers with thirteen products have at least twenty-four sums. -/

import D5.S3.Arith.GeometricProductSetMinimum
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Pointwise
namespace D5.S3.Arith.SumProductSevenPointCell


private def H (j : Fin 12) (x : ℝ) : ℝ :=
  match j.val with
  | 0 => x^2-x-1
  | 1 => x^3-x-1
  | 2 => x^3-x^2-x-1
  | 3 => x^4-x-1
  | 4 => x^4+x^3-x^2-x-1
  | 5 => x^3-x^2-1
  | 6 => x^4-x^3-x^2-x-1
  | 7 => x^5-x-1
  | 8 => x^5+x^4-x^2-x-1
  | 9 => x^4-x^2-1
  | 10 => x^5-x^3-x^2-x-1
  | _ => x^5-x^4-x^3-x^2-x-1

private theorem noCommonRoot_ordered (r : ℝ) (j k : Fin 12)
    (hjk : j < k) (hj : H j r = 0) (hk : H k r = 0) : False := by
  fin_cases j <;> fin_cases k <;> norm_num [Fin.lt_def] at hjk <;> norm_num [H] at hj hk
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^2)*hj + (r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r)*hj + (-1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-2*r^3 + r^2 - r + 2)*hj + (2*r - 3)*hk
    norm_num at hc
  · have hc : (5 : ℝ) = 0 := by
      linear_combination (-3*r^3 - 2*r^2 + 2*r - 1)*hj + (3*r - 4)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^2 - 1)*hj + (r)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 + 2*r^2 + 1)*hj + (r - 2)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (-2*r^4 + r^3 - r^2 + 1)*hj + (2*r - 3)*hk
    norm_num at hc
  · have hc : (3 : ℝ) = 0 := by
      linear_combination (-2*r^4 - r^3 + r)*hj + (2*r - 3)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (-r^3 - 1)*hj + (r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^4)*hj + (r - 1)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (-r^4 + 2*r^3 + r)*hj + (r - 2)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^2 + 2*r)*hj + (r^2 - r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^2 - 1)*hj + (r)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 - r^2 + r)*hj + (r^2 - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r)*hj + (-r - 1)*hk
    norm_num at hc
  · have hc : (7 : ℝ) = 0 := by
      linear_combination (r^3 - 3*r^2 + 5*r - 4)*hj + (-r^2 + 2*r - 3)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r^4 - r^3 - 2)*hj + (-r^2 + r + 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3)*hj + (r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 - r^2 - 1)*hj + (r^2 + r)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r^4 - r^3 - 1)*hj + (-r^2 + r)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (2*r^4 - 3*r^3 - r^2 - 3)*hj + (-2*r^2 + r + 2)*hk
    norm_num at hc
  · have hc : (7 : ℝ) = 0 := by
      linear_combination (r^3 - 4*r^2 + 2*r - 2)*hj + (-r^2 + 5*r - 5)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-2*r^3 - 2*r^2 + 3*r + 2)*hj + (2*r^2 - 2*r - 3)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^2 + r)*hj + (r^2 - r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r)*hj + (-1)*hk
    norm_num at hc
  · have hc : (19 : ℝ) = 0 := by
      linear_combination (8*r^4 - 10*r^3 + 3*r^2 + r - 14)*hj + (-8*r^2 + 18*r - 5)*hk
    norm_num at hc
  · have hc : (11 : ℝ) = 0 := by
      linear_combination (-r^4 - 8*r^3 - r^2 + 5*r + 3)*hj + (r^2 + 6*r - 14)*hk
    norm_num at hc
  · have hc : (11 : ℝ) = 0 := by
      linear_combination (-5*r^3 - r^2 + 7*r - 3)*hj + (5*r^2 - 4*r - 8)*hk
    norm_num at hc
  · have hc : (7 : ℝ) = 0 := by
      linear_combination (r^4 - 4*r^3 + r^2 + 2*r - 2)*hj + (-r^2 + 5*r - 5)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (r^4 - 2*r^3 + r^2 - 1)*hj + (-r^2 + 2*r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 - r^2 - 1)*hj + (r^3 + r)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r - 1)*hj + (-r^2)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-3*r^3 + 5*r^2 + 3)*hj + (3*r^3 - 2*r^2 + r - 4)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^4 - r^2)*hj + (r^3 + r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^4 - r^3 + r)*hj + (r^3 - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r^2 + r)*hj + (-r^2 - r - 1)*hk
    norm_num at hc
  · have hc : (7 : ℝ) = 0 := by
      linear_combination (-4*r^4 + 2*r^3 + 3*r^2 + 6*r + 1)*hj + (4*r^3 - 2*r^2 + r - 8)*hk
    norm_num at hc
  · have hc : (29 : ℝ) = 0 := by
      linear_combination (-9*r^4 + 14*r^3 - 2*r^2 + 23*r - 7)*hj + (9*r^3 - 5*r^2 + 6*r - 22)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^2 + r + 1)*hj + (r^3 + r^2 - 2*r - 2)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (-r^2 + 2*r)*hj + (r^2 - 2)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^4 - 2*r^3 - 2*r^2 - 2*r - 2)*hj + (r^3 + 3*r^2 + 3*r + 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 - r^2)*hj + (r^2 + r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r)*hj + (-r - 1)*hk
    norm_num at hc
  · have hc : (17 : ℝ) = 0 := by
      linear_combination (5*r^4 - 7*r^3 - 2*r^2 + 8*r - 6)*hj + (-5*r^3 + 2*r^2 + 9*r - 11)*hk
    norm_num at hc
  · have hc : (59 : ℝ) = 0 := by
      linear_combination (26*r^4 - 50*r^3 + 2*r^2 + 13*r - 38)*hj + (-26*r^3 - 2*r^2 + 46*r - 21)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 + r^2 + 2*r)*hj + (r^2 - r - 1)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (-r^3 - 1)*hj + (r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^4 - 2*r^3 + 2*r + 1)*hj + (r^2 - 2)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 + r - 1)*hj + (r^2 - r)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r^2 + r)*hj + (-1)*hk
    norm_num at hc
  · have hc : (3 : ℝ) = 0 := by
      linear_combination (-r^3 + 2*r^2 + r - 1)*hj + (r - 2)*hk
    norm_num at hc
  · have hc : (17 : ℝ) = 0 := by
      linear_combination (-5*r^4 + 4*r^3 - 10*r^2 + 8*r + 2)*hj + (5*r^3 - 9*r^2 + 9*r - 19)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (2*r^4 + 3*r^3 - r^2 - 4*r - 2)*hj + (-2*r^3 + r^2 + 5*r + 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-2*r^3 + 3*r)*hj + (2*r^3 - 2*r^2 - 3*r - 1)*hk
    norm_num at hc
  · have hc : (3 : ℝ) = 0 := by
      linear_combination (-r^4 - r^3 + 4*r + 2)*hj + (r^3 - r - 5)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r)*hj + (-1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^4 - r^3)*hj + (r^4 + r - 1)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (r^2 + r - 1)*hj + (-r^3 - r^2 - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^4 + 2*r^2 + 1)*hj + (r^4 - r^2 + r - 2)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (-3*r^4 + 5*r^3 + 3*r + 1)*hj + (3*r^4 - 2*r^3 + r^2 - r - 3)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 + 2*r)*hj + (r^4 + r^3 - r^2 - 2*r - 1)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (r^4 - r^3 - r^2 + r - 1)*hj + (-r^4 + r^2)*hk
    norm_num at hc
  · have hc : (23 : ℝ) = 0 := by
      linear_combination (10*r^4 - 15*r^3 - 14*r^2 + 20*r - 20)*hj +
        (-10*r^4 - 5*r^3 + 14*r^2 + 3*r - 3)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^3 + 2*r + 1)*hj + (r^2 - 2)*hk
    norm_num at hc
  · have hc : (2 : ℝ) = 0 := by
      linear_combination (-r^3 + r^2 + 2*r)*hj + (r^2 - 2)*hk
    norm_num at hc
  · have hc : (1 : ℝ) = 0 := by
      linear_combination (-r^2 + 2*r)*hj + (r^2 - r - 1)*hk
    norm_num at hc

private theorem roots_separated (r : ℝ) (_hr : 1 < r) (j k : Fin 12)
    (hj : H j r = 0) (hk : H k r = 0) : j = k := by
  rcases lt_trichotomy j k with h | h | h
  · exact (noCommonRoot_ordered r j k h hj hk).elim
  · exact h
  · exact (noCommonRoot_ordered r k j h hk hj).elim



private abbrev Pair := Fin 7 × Fin 7

private def pairs : Finset Pair := Finset.univ.filter (fun p => p.1 ≤ p.2)

private def forbidden (j : Fin 12) : Finset Pair :=
  match j.val with
  | 0 => {(0, 3), (1, 4), (2, 5), (3, 6)}
  | 1 => {(0, 4), (1, 5), (2, 6), (0, 6)}
  | 2 => {(0, 4), (1, 5), (2, 6)}
  | 3 => {(0, 5), (1, 6)}
  | 4 => {(0, 5), (1, 6)}
  | 5 => {(0, 5), (1, 6)}
  | 6 => {(0, 5), (1, 6)}
  | _ => {(0, 6)}

private theorem mem_forbidden_of_gap (j : Fin 12) (p : Pair)
    (h : (j.val = 0 ∧ p.2.val = p.1.val + 3) ∨
      (j.val = 1 ∧ (p.2.val = p.1.val + 4 ∨ p.2.val = p.1.val + 6)) ∨
      (j.val = 2 ∧ p.2.val = p.1.val + 4) ∨
      (3 ≤ j.val ∧ j.val ≤ 6 ∧ p.2.val = p.1.val + 5) ∨
      (7 ≤ j.val ∧ p.2.val = p.1.val + 6)) : p ∈ forbidden j := by
  rcases p with ⟨a, b⟩
  have ha := a.isLt
  have hb := b.isLt
  fin_cases j <;> simp only [forbidden, Finset.mem_insert, Finset.mem_singleton,
    Prod.mk.injEq, Fin.ext_iff] at * <;> omega

private theorem surviving_pairs_card (j : Fin 12) : 24 ≤ (pairs \ forbidden j).card := by
  fin_cases j <;> decide

private theorem image_card_ge_twentyfour {α : Type*} [DecidableEq α]
    (f : Pair → α) (R : Fin 12 → Prop)
    (unique : ∀ j k, R j → R k → j = k)
    (collision : ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q → f p = f q →
      ∃ j, R j ∧ (p ∈ forbidden j ∨ q ∈ forbidden j)) :
    24 ≤ (pairs.image f).card := by
  classical
  have hj : ∃ j : Fin 12, ∀ k, R k → k = j := by
    by_cases h : ∃ k, R k
    · obtain ⟨j, hj⟩ := h
      exact ⟨j, fun k hk => unique k j hk hj⟩
    · exact ⟨0, fun k hk => False.elim (h ⟨k, hk⟩)⟩
  obtain ⟨j, hj⟩ := hj
  have hinj : Set.InjOn f ↑(pairs \ forbidden j) := by
    intro p hp q hq hpq
    by_contra hne
    obtain ⟨k, hk, hbad⟩ := collision p (Finset.mem_sdiff.mp hp).1
      q (Finset.mem_sdiff.mp hq).1 hne hpq
    rw [hj k hk] at hbad
    rcases hbad with hbad | hbad
    · exact (Finset.mem_sdiff.mp hp).2 hbad
    · exact (Finset.mem_sdiff.mp hq).2 hbad
  calc
    24 ≤ (pairs \ forbidden j).card := surviving_pairs_card j
    _ = ((pairs \ forbidden j).image f).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (pairs.image f).card := Finset.card_le_card
      (Finset.image_subset_image Finset.sdiff_subset)

private theorem geometric_pair_image_subset (b r : ℝ) :
    pairs.image (fun p => b * r ^ p.1.val + b * r ^ p.2.val) ⊆
      ((Finset.range 7).image (fun i => b * r ^ i)) +
        ((Finset.range 7).image (fun i => b * r ^ i)) := by
  intro x hx
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_add.mpr ⟨b * r ^ p.1.val,
    Finset.mem_image.mpr ⟨p.1.val, Finset.mem_range.mpr p.1.isLt, rfl⟩,
    b * r ^ p.2.val,
    Finset.mem_image.mpr ⟨p.2.val, Finset.mem_range.mpr p.2.isLt, rfl⟩, rfl⟩



private theorem nested_collision (r : ℝ) (hr : 1 < r) (i j k l : ℕ)
    (_hij : i ≤ j) (_hkl : k ≤ l) (hneq : (i, j) ≠ (k, l))
    (h : r ^ i + r ^ j = r ^ k + r ^ l) (hik : i ≤ k) : i < k ∧ l < j := by
  have hik' : i < k := by
    by_contra hn
    have he : i = k := by omega
    have hjl : j = l := by
      have : r ^ j = r ^ l := by rw [he] at h; linarith
      exact (pow_right_strictMono₀ hr).injective this
    exact hneq (by simp [he, hjl])
  refine ⟨hik', ?_⟩
  by_contra hn
  have hjl : j ≤ l := by omega
  have h1 := pow_lt_pow_right₀ hr hik'
  have h2 := pow_le_pow_right₀ hr.le hjl
  linarith

private theorem normalized_collision (r : ℝ) (hr : 1 < r) (i j k l : ℕ)
    (hik : i < k) (hkl : k ≤ l) (hlj : l < j)
    (h : r ^ i + r ^ j = r ^ k + r ^ l) :
    1 + r ^ (j-i) = r ^ (k-i) + r ^ (l-i) ∧ (j-i) < (k-i) + (l-i) := by
  have hi : i ≤ j := by omega
  have hk : i ≤ k := by omega
  have hl : i ≤ l := by omega
  have hp : r ^ i ≠ 0 := pow_ne_zero _ (by linarith)
  have he : 1 + r ^ (j-i) = r ^ (k-i) + r ^ (l-i) := by
    apply (mul_left_cancel₀ hp)
    calc
      r ^ i * (1 + r ^ (j-i)) = r ^ i + r ^ j := by
        rw [mul_add, mul_one, ← pow_add, Nat.add_sub_of_le hi]
      _ = r ^ k + r ^ l := h
      _ = r ^ i * (r ^ (k-i) + r ^ (l-i)) := by
        rw [mul_add, ← pow_add, ← pow_add, Nat.add_sub_of_le hk, Nat.add_sub_of_le hl]
  refine ⟨he, ?_⟩
  by_contra hn
  have hab : (k-i) + (l-i) ≤ j-i := by omega
  have hd := pow_le_pow_right₀ hr.le hab
  have ha : 1 < r ^ (k-i) := one_lt_pow₀ hr (by omega)
  have hb : 1 < r ^ (l-i) := one_lt_pow₀ hr (by omega)
  rw [pow_add] at hd
  have hp : 0 < (r ^ (k-i)-1) * (r ^ (l-i)-1) := mul_pos (by linarith) (by linarith)
  nlinarith

private theorem triple_cases (d a b : Fin 7) (ha : 1 ≤ a.val) (hab : a.val ≤ b.val)
    (hbd : b.val < d.val) (hs : d.val < a.val + b.val) :
    (d.val = 3 ∧ a.val = 2 ∧ b.val = 2) ∨
    (d.val = 4 ∧ a.val = 2 ∧ b.val = 3) ∨
    (d.val = 4 ∧ a.val = 3 ∧ b.val = 3) ∨
    (d.val = 5 ∧ a.val = 2 ∧ b.val = 4) ∨
    (d.val = 5 ∧ a.val = 3 ∧ b.val = 3) ∨
    (d.val = 5 ∧ a.val = 3 ∧ b.val = 4) ∨
    (d.val = 5 ∧ a.val = 4 ∧ b.val = 4) ∨
    (d.val = 6 ∧ a.val = 2 ∧ b.val = 5) ∨
    (d.val = 6 ∧ a.val = 3 ∧ b.val = 4) ∨
    (d.val = 6 ∧ a.val = 3 ∧ b.val = 5) ∨
    (d.val = 6 ∧ a.val = 4 ∧ b.val = 4) ∨
    (d.val = 6 ∧ a.val = 4 ∧ b.val = 5) ∨
    (d.val = 6 ∧ a.val = 5 ∧ b.val = 5) := by
  revert a b
  fin_cases d <;> decide

private theorem collision_table (r : ℝ) (hr : 1 < r) (d a b : ℕ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hbd : b < d) (hd : d ≤ 6)
    (hs : d < a + b) (he : 1 + r ^ d = r ^ a + r ^ b) :
    ∃ j : Fin 12, H j r = 0 ∧ ((j = 0 ∧ d = 3) ∨ (j = 1 ∧ (d = 4 ∨ d = 6)) ∨
      (j = 2 ∧ d = 4) ∨ (3≤j.val ∧ j.val≤6 ∧ d = 5) ∨ (7≤j.val ∧ d = 6)) := by
  have cases := triple_cases ⟨d, by omega⟩ ⟨a, by omega⟩ ⟨b, by omega⟩ ha hab hbd hs
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12
  · obtain ⟨rfl, rfl, rfl⟩ := h0
    refine ⟨0, ?_, by norm_num⟩
    have fac : 1 + r ^ 3-r ^ 2-r ^ 2 = (r-1) * (1) * H 0 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 0 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h1
    refine ⟨1, ?_, by norm_num⟩
    have fac : 1 + r ^ 4-r ^ 2-r ^ 3 = (r-1) * (1) * H 1 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 1 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h2
    refine ⟨2, ?_, by norm_num⟩
    have fac : 1 + r ^ 4-r ^ 3-r ^ 3 = (r-1) * (1) * H 2 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 2 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h3
    refine ⟨3, ?_, by norm_num⟩
    have fac : 1 + r ^ 5-r ^ 2-r ^ 4 = (r-1) * (1) * H 3 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 3 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h4
    refine ⟨4, ?_, by norm_num⟩
    have fac : 1 + r ^ 5-r ^ 3-r ^ 3 = (r-1) * (1) * H 4 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 4 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h5
    refine ⟨5, ?_, by norm_num⟩
    have fac : 1 + r ^ 5-r ^ 3-r ^ 4 = (r-1) * (r + 1) * H 5 r := by norm_num [H]; ring
    have hz : (r-1) * (r + 1) * H 5 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (r + 1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h6
    refine ⟨6, ?_, by norm_num⟩
    have fac : 1 + r ^ 5-r ^ 4-r ^ 4 = (r-1) * (1) * H 6 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 6 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h7
    refine ⟨7, ?_, by norm_num⟩
    have fac : 1 + r ^ 6-r ^ 2-r ^ 5 = (r-1) * (1) * H 7 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 7 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h8
    refine ⟨8, ?_, by norm_num⟩
    have fac : 1 + r ^ 6-r ^ 3-r ^ 4 = (r-1) * (1) * H 8 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 8 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h9
    refine ⟨1, ?_, by norm_num⟩
    have fac : 1 + r ^ 6-r ^ 3-r ^ 5 = (r-1) * (r ^ 2 + 1) * H 1 r := by norm_num [H]; ring
    have hz : (r-1) * (r ^ 2 + 1) * H 1 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (r ^ 2 + 1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h10
    refine ⟨9, ?_, by norm_num⟩
    have fac : 1 + r ^ 6-r ^ 4-r ^ 4 = (r-1) * (r + 1) * H 9 r := by norm_num [H]; ring
    have hz : (r-1) * (r + 1) * H 9 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (r + 1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h11
    refine ⟨10, ?_, by norm_num⟩
    have fac : 1 + r ^ 6-r ^ 4-r ^ 5 = (r-1) * (1) * H 10 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 10 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)
  · obtain ⟨rfl, rfl, rfl⟩ := h12
    refine ⟨11, ?_, by norm_num⟩
    have fac : 1 + r ^ 6-r ^ 5-r ^ 5 = (r-1) * (1) * H 11 r := by norm_num [H]; ring
    have hz : (r-1) * (1) * H 11 r = 0 := by rw [← fac]; linarith
    have hp : 0 < (r-1) * (1) := by positivity
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hp)


private theorem pair_collision_ordered (r : ℝ) (hr : 1 < r)
    (p q : Pair) (hp : p ∈ pairs) (hq : q ∈ pairs) (hne : p ≠ q)
    (he : r ^ p.1.val + r ^ p.2.val = r ^ q.1.val + r ^ q.2.val)
    (ho : p.1.val ≤ q.1.val) :
    ∃ j : Fin 12, H j r = 0 ∧ p ∈ forbidden j := by
  have hpn : (p.1.val, p.2.val) ≠ (q.1.val, q.2.val) := by
    intro h
    apply hne
    apply Prod.ext <;> apply Fin.ext
    · exact (Prod.mk.inj h).1
    · exact (Prod.mk.inj h).2
  have hpo : p.1.val ≤ p.2.val := (Finset.mem_filter.mp hp).2
  have hqo : q.1.val ≤ q.2.val := (Finset.mem_filter.mp hq).2
  obtain ⟨hik, hlj⟩ := nested_collision r hr _ _ _ _ hpo hqo hpn he ho
  obtain ⟨hn, hs⟩ := normalized_collision r hr _ _ _ _ hik hqo hlj he
  obtain ⟨j, hj, hd⟩ := collision_table r hr (p.2.val-p.1.val)
    (q.1.val-p.1.val) (q.2.val-p.1.val) (by omega) (by omega)
    (by omega) (by have := p.2.isLt; omega) hs hn
  refine ⟨j, hj, mem_forbidden_of_gap j p ?_⟩
  rcases hd with hd | hd | hd | hd | hd
  · left; exact ⟨congrArg Fin.val hd.1, by omega⟩
  · right; left
    exact ⟨congrArg Fin.val hd.1, by omega⟩
  · right; right; left
    exact ⟨congrArg Fin.val hd.1, by omega⟩
  · right; right; right; left
    exact ⟨hd.1, hd.2.1, by omega⟩
  · right; right; right; right
    exact ⟨hd.1, by omega⟩

/-- A geometric progression of seven positive terms has at least twenty-four sums. -/
theorem geometric_sum_card_lower_bound (b r : ℝ) (hb : 0 < b) (hr : 1 < r) :
    24 ≤ (((Finset.range 7).image (fun i => b * r ^ i)) +
      ((Finset.range 7).image (fun i => b * r ^ i))).card := by
  classical
  apply le_trans (image_card_ge_twentyfour
    (fun p => b * r ^ p.1.val + b * r ^ p.2.val) (fun j => H j r = 0)
    (roots_separated r hr) ?_)
    (Finset.card_le_card (geometric_pair_image_subset b r))
  intro p hp q hq hne he
  have he' : r ^ p.1.val + r ^ p.2.val = r ^ q.1.val + r ^ q.2.val := by
    apply mul_left_cancel₀ hb.ne'
    simpa only [mul_add] using he
  rcases le_total p.1.val q.1.val with ho | ho
  · obtain ⟨j, hj, hpj⟩ := pair_collision_ordered r hr p q hp hq hne he' ho
    exact ⟨j, hj, Or.inl hpj⟩
  · obtain ⟨j, hj, hqj⟩ := pair_collision_ordered r hr q p hq hp hne.symm he'.symm ho
    exact ⟨j, hj, Or.inr hqj⟩

/-- Minimum product cardinality imposes the sharp sum lower bound for seven positive reals. -/
theorem stronger_result (A : Finset ℝ) (hp : ∀ a ∈ A, 0 < a)
    (hc : A.card = 7) (hm : (A * A).card = 13) : 24 ≤ (A + A).card := by
  obtain ⟨b, r, hb, hr, hA⟩ := GeometricProductSetMinimum.eq_geometric_of_product_card
    A hp (by omega) (by omega)
  rw [hc] at hA
  rw [hA]
  exact geometric_sum_card_lower_bound b r hb hr

/-- The cell (23,13) is absent from the seven-point positive-real sum-product spectrum. -/
def claim : Prop := ∀ A : Finset ℝ, (∀ a ∈ A, 0<a) → A.card = 7 →
    ¬ ((A + A).card = 23 ∧ (A * A).card = 13)

/-- No seven-element positive-real set has twenty-three sums and thirteen products. -/
theorem result : claim := by
  intro A hp hc hcell
  have h := stronger_result A hp hc hcell.2
  omega

end D5.S3.Arith.SumProductSevenPointCell
