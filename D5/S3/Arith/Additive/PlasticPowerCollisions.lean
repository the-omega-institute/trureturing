/- GID: D5/S3/Arith/Additive/PlasticPowerCollisions
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticPowerCollisions
   mirror-E: none(waiver:algebraic-power-collisions)
   anchors: []
   utility: none
   digest: Integer powers of a plastic root have exactly four nontrivial normalized sum collisions. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Integer-exponent difference equations and normalized equal sums for a plastic root. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Additive.PlasticPowerCollisions

private theorem step_identities (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1) :
    r ^ (1 : ℤ) - 1 = r ^ (-4 : ℤ) ∧
    r ^ (2 : ℤ) - 1 = r ^ (-1 : ℤ) ∧ 2 < r ^ (3 : ℤ) := by
  have hr0 : r ≠ 0 := by linarith
  constructor
  · norm_num only [zpow_one, zpow_neg, zpow_ofNat]
    rw [inv_eq_one_div]
    apply (eq_div_iff (pow_ne_zero 4 hr0)).2
    linear_combination (r ^ 2 - r + 1) * hroot
  constructor
  · norm_num only [zpow_neg, zpow_ofNat, pow_one]
    rw [inv_eq_one_div]
    apply (eq_div_iff hr0).2
    linear_combination hroot
  · norm_num only [zpow_ofNat]
    linarith

/-- The complete integer-exponent difference equation, including negative exponents. -/
theorem difference_eq_one_iff (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (u v : ℤ) :
    r ^ u - r ^ v = 1 ↔
      (u = 1 ∧ v = -4) ∨ (u = 2 ∧ v = -1) ∨
      (u = 3 ∧ v = 1) ∨ (u = 5 ∧ v = 4) := by
  have hrpos : 0 < r := by linarith
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hm := zpow_right_strictMono₀ hr
  obtain ⟨hs1, hs2, hs3⟩ := step_identities r hr hroot
  constructor
  · intro h
    have hupos : 0 < u := (one_lt_zpow_iff_right₀ hr).1 (by
      have := zpow_pos hrpos v
      linarith)
    have huv : v < u := hm.lt_iff_lt.1 (by linarith)
    by_cases hv : v < 0
    · have hvone : r ^ v < 1 := zpow_lt_one_of_neg₀ hr hv
      have hu3 : u < 3 := hm.lt_iff_lt.1
        (lt_trans (show r ^ u < 2 by linarith) hs3)
      have hu : u = 1 ∨ u = 2 := by omega
      rcases hu with rfl | rfl
      · left
        refine ⟨rfl, hm.injective ?_⟩
        linarith
      · right; left
        refine ⟨rfl, hm.injective ?_⟩
        linarith
    · have hv0 : 0 ≤ v := by omega
      have hpv : 1 ≤ r ^ v := one_le_zpow₀ (le_of_lt hr) hv0
      have hgap : r ^ (u - v) - 1 = r ^ (-v) := by
        rw [zpow_sub₀ hr0, zpow_neg]
        field_simp
        nlinarith
      have hgap3 : u - v < 3 := hm.lt_iff_lt.1 (show r ^ (u - v) < r ^ (3 : ℤ) from by
        have hinv : r ^ (-v) ≤ 1 := zpow_le_one_of_nonpos₀ (le_of_lt hr) (by omega)
        exact lt_of_le_of_lt (show r ^ (u - v) ≤ 2 by linarith) hs3)
      have hgap12 : u - v = 1 ∨ u - v = 2 := by omega
      rcases hgap12 with hg | hg
      · rw [hg, hs1] at hgap
        have hv4 : v = 4 := by have := hm.injective hgap; omega
        right; right; right
        exact ⟨by omega, hv4⟩
      · rw [hg, hs2] at hgap
        have hv1 : v = 1 := by have := hm.injective hgap; omega
        right; right; left
        exact ⟨by omega, hv1⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · linarith
    · linarith
    · norm_num only [zpow_ofNat, zpow_one]
      linarith
    · norm_num only [zpow_ofNat]
      linear_combination (r ^ 2 - r + 1) * hroot

/-- All nontrivial normalized equal sums, with the diagonal inner pair retained. -/
theorem normalized_collision_iff (r : ℝ) (hr : 1 < r) (hroot : r ^ 3 = r + 1)
    (d a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hbd : b < d) :
    1 + r ^ d = r ^ a + r ^ b ↔
      (d = 4 ∧ a = 2 ∧ b = 3) ∨ (d = 6 ∧ a = 3 ∧ b = 5) ∨
      (d = 7 ∧ a = 5 ∧ b = 5) ∨ (d = 9 ∧ a = 5 ∧ b = 8) := by
  have hrpos : 0 < r := by linarith
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hm := zpow_right_strictMono₀ hr
  obtain ⟨hs1, hs2, hs3⟩ := step_identities r hr hroot
  constructor
  · intro h
    have hgap : r ^ (d - b) = 1 + r ^ (a - b) - r ^ (-b) := by
      rw [zpow_sub₀ hr0, zpow_sub₀ hr0, zpow_neg]
      field_simp
      nlinarith
    have hslt : d - b < 3 := hm.lt_iff_lt.1
      (show r ^ (d - b) < r ^ (3 : ℤ) from by
        have hab1 : r ^ (a - b) ≤ 1 :=
          zpow_le_one_of_nonpos₀ (le_of_lt hr) (by omega)
        have hbinv : 0 < r ^ (-b) := zpow_pos hrpos _
        exact lt_trans (show r ^ (d - b) < 2 by linarith) hs3)
    have hs : d - b = 1 ∨ d - b = 2 := by omega
    rcases hs with hs | hs
    · have hd : d = b + 1 := by omega
      have hshift : r ^ (b - 4) = r ^ b * (r ^ (1 : ℤ) - 1) := by
        rw [show b - 4 = b + (-4) by omega, zpow_add₀ hr0, ← hs1]
      have hdiff : r ^ a - r ^ (b - 4) = 1 := by
        rw [hd, zpow_add₀ hr0] at h
        rw [hshift]
        nlinarith
      have hc := (difference_eq_one_iff r hr hroot a (b - 4)).1 hdiff
      rcases hc with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · omega
      · left; exact ⟨by omega, ha', by omega⟩
      · right; left; exact ⟨by omega, ha', by omega⟩
      · right; right; right; exact ⟨by omega, ha', by omega⟩
    · have hd : d = b + 2 := by omega
      have hshift : r ^ (b - 1) = r ^ b * (r ^ (2 : ℤ) - 1) := by
        rw [show b - 1 = b + (-1) by omega, zpow_add₀ hr0, ← hs2]
      have hdiff : r ^ a - r ^ (b - 1) = 1 := by
        rw [hd, zpow_add₀ hr0] at h
        rw [hshift]
        nlinarith
      have hc := (difference_eq_one_iff r hr hroot a (b - 1)).1 hdiff
      rcases hc with ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩ | ⟨ha', hb'⟩
      · omega
      · omega
      · omega
      · right; right; left; exact ⟨by omega, ha', by omega⟩
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> norm_num only [zpow_ofNat]
    · linear_combination (r - 1) * hroot
    · linear_combination (r ^ 3 - r ^ 2 + r - 1) * hroot
    · linear_combination (r ^ 4 - r ^ 2 + r - 1) * hroot
    · linear_combination
        (r ^ 6 - r ^ 5 + r ^ 4 - r ^ 2 + r - 1) * hroot

end D5.S3.Arith.Additive.PlasticPowerCollisions
