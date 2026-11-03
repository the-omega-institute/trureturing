/- GID: D5/S3/Arith/Additive/PlasticPowerCollisions
   generality: G
   mirror-B: D5/B/S3/Arith/Additive/PlasticPowerCollisions
   mirror-E: none(waiver:algebraic-power-collisions)
   anchors: []
   utility: none
   digest: Integer powers of a plastic root have exactly four nontrivial normalized sum collisions. -/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

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
      have hu3 : u < 3 := hm.lt_iff_lt.1 (by linarith)
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
      have hgap3 : u - v < 3 := hm.lt_iff_lt.1 (by
        have hinv : r ^ (-v) ≤ 1 := zpow_le_one_of_nonpos₀ (le_of_lt hr) (by omega)
        linarith)
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

end D5.S3.Arith.Additive.PlasticPowerCollisions
