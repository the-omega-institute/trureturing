/- GID: D5/S3/Combinatorics/Sequenceability/PairedBinomialTail
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Sequenceability/PairedBinomialTail
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Data.Nat.Choose.Sum]
   utility: none
   digest: Finite symmetric binomial tail for the paired circular-block consumer. -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Exact rational estimates, uniform in the number of coordinate pairs. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Sequenceability.PairedBinomialTail

open Finset

/-- The paired-subset density among subsets of twice the size. -/
def density (r j : ℕ) : ℚ := (r.choose j : ℚ) / ((2*r).choose (2*j) : ℚ)

private theorem denominator_pos {r j : ℕ} (hj : j ≤ r) :
    (0 : ℚ) < (2*r).choose (2*j) := by
  exact_mod_cast Nat.choose_pos (by omega : 2*j ≤ 2*r)

theorem density_pos {r j : ℕ} (hj : j ≤ r) : 0 < density r j :=
  div_pos (by exact_mod_cast Nat.choose_pos hj) (denominator_pos hj)

theorem density_symm {r j : ℕ} (hj : j ≤ r) :
    density r (r-j) = density r j := by
  unfold density
  rw [Nat.choose_symm hj, show 2*(r-j) = 2*r-2*j by omega,
    Nat.choose_symm (by omega : 2*j ≤ 2*r)]

/-- The exact adjacent-index ratio; no asymptotic remainder is used. -/
theorem density_step {r j : ℕ} (hj : j < r) :
    density r (j+1) = density r j * (2*(j:ℚ)+1) / (2*(r:ℚ)-2*j-1) := by
  have ha : (r.choose (j+1) : ℚ) * (j+1) = (r.choose j : ℚ) * (r-j : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq r j
  have hb : ((2*r).choose (2*j+1) : ℚ) * (2*j+1) =
      ((2*r).choose (2*j) : ℚ) * (2*r-2*j : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq (2*r) (2*j)
  have hc : ((2*r).choose (2*j+2) : ℚ) * (2*j+2) =
      ((2*r).choose (2*j+1) : ℚ) * (2*r-(2*j+1) : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq (2*r) (2*j+1)
  rw [Nat.cast_sub (by omega : j ≤ r)] at ha
  rw [Nat.cast_sub (by omega : 2*j ≤ 2*r)] at hb
  rw [Nat.cast_sub (by omega : 2*j+1 ≤ 2*r)] at hc
  push_cast at hb hc
  have hm : ((2*r).choose (2*j+2) : ℚ) * ((j:ℚ)+1) * (2*j+1) =
      ((2*r).choose (2*j) : ℚ) * ((r:ℚ)-j) * (2*r-2*j-1) := by
    linear_combination (2*(j:ℚ)+1)/2 * hc + (2*(r:ℚ)-2*j-1)/2 * hb
  have hz : (j:ℚ)+1 ≠ 0 := by positivity
  have hd : 2*(r:ℚ)-2*j-1 ≠ 0 := by
    have : (j:ℚ)+1 ≤ r := by exact_mod_cast (by omega : j+1 ≤ r)
    linarith
  unfold density
  rw [show 2*(j+1) = 2*j+2 by omega]
  have hb0 : ((2*r).choose (2*j) : ℚ) ≠ 0 := ne_of_gt (denominator_pos hj.le)
  have hc0 : ((2*r).choose (2*j+2) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : 2*j+2 ≤ 2*r)
  rw [div_mul_eq_mul_div, div_div, div_eq_div_iff hc0 (mul_ne_zero hb0 hd)]
  apply mul_right_cancel₀ hz
  linear_combination ((2*r).choose (2*j) : ℚ) * (2*(r:ℚ)-2*j-1) * ha -
    (r.choose j : ℚ) * hm

private theorem density_step_le {r j : ℕ} (hj : j < r) (hm : 2*j+1 ≤ r) :
    density r (j+1) ≤ density r j := by
  rw [density_step hj]
  have hd : 0 < 2*(r:ℚ)-2*j-1 := by
    have : (j:ℚ)+1 ≤ r := by exact_mod_cast (by omega : j+1 ≤ r)
    linarith
  apply (div_le_iff₀ hd).mpr
  have : (2*(j:ℚ)+1) ≤ 2*(r:ℚ)-2*j-1 := by
    have : 2*(j:ℚ)+1 ≤ r := by exact_mod_cast hm
    linarith
  exact mul_le_mul_of_nonneg_left this (density_pos hj.le).le

/-- Every term between the two third terms is bounded by the third term. -/
theorem density_middle_le {r j : ℕ} (hr : 6 ≤ r) (hj : 3 ≤ j) (hjr : j ≤ r-3) :
    density r j ≤ density r 3 := by
  have half : ∀ k : ℕ, 3 ≤ k → 2*k ≤ r → density r k ≤ density r 3 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ k hk ih =>
      intro hkr
      have hm : 2*k+1 ≤ r := by omega
      exact (density_step_le (by omega) hm).trans (ih (by omega))
  by_cases hm : 2*j ≤ r
  · exact half j hj hm
  · rw [← density_symm (by omega : j ≤ r)]
    exact half (r-j) (by omega) (by omega)

private theorem density_zero (r : ℕ) : density r 0 = 1 := by simp [density]

/-- The two endpoint terms are evaluated exactly. -/
theorem density_two {r : ℕ} (hr : 2 ≤ r) :
    density r 2 = 3 / ((2*(r:ℚ)-1)*(2*r-3)) := by
  have h0 := density_step (r := r) (j := 0) (by omega)
  have h1 := density_step (r := r) (j := 1) (by omega)
  rw [density_zero] at h0
  norm_num at h0 h1
  rw [h1, h0]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem density_three {r : ℕ} (hr : 3 ≤ r) :
    density r 3 = 15 / ((2*(r:ℚ)-1)*(2*r-3)*(2*r-5)) := by
  have h2 := density_step (r := r) (j := 2) (by omega)
  norm_num at h2
  rw [h2, density_two (by omega)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The finite tail has two endpoint terms and exactly r-5 middle terms. -/
theorem density_tail_le {r : ℕ} (hr : 6 ≤ r) :
    ∑ j ∈ Icc 2 (r-2), density r j ≤
      2*density r 2 + (r-5:ℕ)*density r 3 := by
  have he : Icc 2 (r-2) = insert 2 (insert (r-2) (Icc 3 (r-3))) := by
    ext j
    simp only [mem_Icc,mem_insert]
    omega
  have h2 : 2 ∉ insert (r-2) (Icc 3 (r-3)) := by simp; omega
  have ht : r-2 ∉ Icc 3 (r-3) := by simp; omega
  rw [he,sum_insert h2,sum_insert ht,density_symm (by omega : 2 ≤ r)]
  have hmid : ∑ j ∈ Icc 3 (r-3), density r j ≤ (r-5:ℕ)*density r 3 := by
    calc
      _ ≤ ∑ _j ∈ Icc 3 (r-3), density r 3 := by
        apply sum_le_sum
        intro j hj
        exact density_middle_le hr (mem_Icc.mp hj).1 (mem_Icc.mp hj).2
      _ = _ := by
        have hc : (Icc 3 (r-3)).card = r-5 := by rw [Nat.card_Icc]; omega
        simp [hc]
  linarith

/-- Uniform finite residual mass bound used after excluding opposite-pair adjacencies. -/
theorem paired_tail_bound {r : ℕ} (hr : 6 ≤ r) :
    (r:ℚ) * ∑ j ∈ Icc 2 (r-2), density r j ≤
      (r:ℚ)*(27*r-105) / ((2*r-1)*(2*r-3)*(2*r-5)) := by
  have h1 : (2*(r:ℚ)-1) ≠ 0 := by
    have : (6:ℚ) ≤ r := by exact_mod_cast hr
    linarith
  have h3 : (2*(r:ℚ)-3) ≠ 0 := by
    have : (6:ℚ) ≤ r := by exact_mod_cast hr
    linarith
  have h5 : (2*(r:ℚ)-5) ≠ 0 := by
    have : (6:ℚ) ≤ r := by exact_mod_cast hr
    linarith
  calc
    _ ≤ (r:ℚ)*(2*density r 2+(r-5:ℕ)*density r 3) :=
      mul_le_mul_of_nonneg_left (density_tail_le hr) (by positivity)
    _ = _ := by
      rw [density_two (by omega),density_three (by omega),Nat.cast_sub (by omega : 5 ≤ r)]
      push_cast
      have hi : ((2*(r:ℚ)-1)*(2*r-3))⁻¹ =
          (2*(r:ℚ)-5) * ((2*(r:ℚ)-1)*(2*r-3)*(2*r-5))⁻¹ := by
        conv_rhs => rw [mul_inv_rev]
        rw [←mul_assoc,mul_inv_cancel₀ h5,one_mul]
      simp only [div_eq_mul_inv]
      rw [hi]
      ring

end D5.S3.Combinatorics.Sequenceability.PairedBinomialTail
