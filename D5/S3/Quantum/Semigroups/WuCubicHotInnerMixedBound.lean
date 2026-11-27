import D5.S3.Quantum.Semigroups.WuCubicHotInnerMixed
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import OmegaBuild.Commands

/-! The signed size of the exact Wu cubic mixed coefficient at every interior
temperature with physical Gibbs occupations. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicHotInnerMixedBound

open WuCubicHotInnerMixed (deficit hot_inner_mixed)
open WuRepeatedMiddleCubic (alpha)

private theorem log_ratio_bounds {r : ℝ} (hr : 1 < r) :
    2 * (r - 1) / (r + 1) ≤ Real.log r ∧
      Real.log r ≤ (r ^ 2 - 1) / (2 * r) := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hs : 0 < r + 1 := by positivity
  let w := (r - 1) / (r + 1)
  have hw : 0 ≤ w := div_nonneg (sub_nonneg.mpr hr.le) hs.le
  have hw1 : w < 1 := (div_lt_one hs).2 (by linarith)
  have hratio : (1 + w) / (1 - w) = r := by
    apply (div_eq_iff (sub_pos.mpr hw1).ne').2
    dsimp [w]
    field_simp [hs.ne']
    ring
  have hlow := Real.sum_range_le_log_div hw hw1 1
  have hhigh := Real.log_div_le_sum_range_add hw hw1 0
  rw [hratio] at hlow hhigh
  norm_num [Finset.sum_range_succ] at hlow hhigh
  have hwden : 0 < 1 - w ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hw1) (show 0 < 1 + w by positivity)]
  have hupper : 2 * (w / (1 - w ^ 2)) = (r ^ 2 - 1) / (2 * r) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hr0.ne')).2
    calc
      2 * (w / (1 - w ^ 2)) * (2 * r) = (4 * r * w) / (1 - w ^ 2) := by ring
      _ = _ := by
        apply (div_eq_iff hwden.ne').2
        dsimp [w]
        field_simp [hs.ne']
        ring
  constructor
  · unfold w at hlow
    rw [mul_div_assoc]
    linarith only [hlow]
  · rw [← hupper]
    linarith only [hhigh]

private theorem alpha_loss_bounds {r : ℝ} (hr : 1 < r) :
    let D := r ^ 2 + r + 1
    ((r - 1) ^ 2 / D) / 4 ≤ 1 - 2 * alpha r ∧
      1 - 2 * alpha r ≤ (r - 1) ^ 2 / D := by
  intro D
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hs : 0 < r + 1 := by positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have hl : 0 < Real.log r := Real.log_pos hr
  have hden : 0 < 2 * D * Real.log r := by positivity
  obtain ⟨hlogLow, hlogHigh⟩ := log_ratio_bounds hr
  have halpha : 2 * alpha r * (2 * D * Real.log r) = 3 * (r ^ 2 - 1) := by
    rw [alpha, ite_eq_right hr.ne']
    change 2 * (3 * (r ^ 2 - 1) / (4 * D * Real.log r)) * (2 * D * Real.log r) = _
    field_simp [hD.ne', hl.ne']
    ring
  have hlow : 3 * r / D ≤ 2 * alpha r := by
    apply (le_of_mul_le_mul_right ?_ hden)
    rw [halpha]
    calc
      3 * r / D * (2 * D * Real.log r) = 3 * (Real.log r * (2 * r)) := by
        field_simp [hD.ne']
      _ ≤ 3 * (r ^ 2 - 1) :=
        mul_le_mul_of_nonneg_left ((le_div_iff₀ (by positivity)).1 hlogHigh) (by norm_num)
  have hhigh : 2 * alpha r ≤ 3 * (r + 1) ^ 2 / (4 * D) := by
    apply (le_of_mul_le_mul_right ?_ hden)
    rw [halpha]
    calc
      3 * (r ^ 2 - 1) = (3 * (r + 1) ^ 2 / 2) * (2 * (r - 1) / (r + 1)) := by
        field_simp [hs.ne']
        ring
      _ ≤ (3 * (r + 1) ^ 2 / 2) * Real.log r :=
        mul_le_mul_of_nonneg_left hlogLow (by positivity)
      _ = 3 * (r + 1) ^ 2 / (4 * D) * (2 * D * Real.log r) := by
        field_simp [hD.ne']
        ring
  have hlow_eq : 1 - 3 * (r + 1) ^ 2 / (4 * D) = ((r - 1) ^ 2 / D) / 4 := by
    field_simp [hD.ne']
    dsimp [D]
    ring
  have hhigh_eq : 1 - 3 * r / D = (r - 1) ^ 2 / D := by
    field_simp [hD.ne']
    dsimp [D]
    ring
  exact ⟨hlow_eq ▸ sub_le_sub_left hhigh 1, hhigh_eq ▸ sub_le_sub_left hlow 1⟩

/-- The exact `k²y` coefficient is negative at every `r > 1` and its magnitude
is bounded by `3(r-1)/2`. The intermediate bounds retain the Gibbs factors. -/
theorem hot_inner_mixed_bound (r : ℝ) (hr : 1 < r) :
    let u := 1 / r
    let a := 1 / (1 + r ^ 3)
    let b := r ^ 3 / (1 + r ^ 3)
    let γ := 9 * a / 4
    let D := r ^ 2 + r + 1
    let C := -b * γ * (1 + u) / (1 - u) *
      (2 * (1 - 2 * alpha r) + 2 * (1 - u) ^ 2 / (1 + u + u ^ 2))
    HasDerivAt (fun y => deriv (fun z => deficit u a b (alpha r) z y) 0) C 0 ∧
      C < 0 ∧
      (5 / 2) * b * γ * (r + 1) * (r - 1) / D ≤ -C ∧
      -C ≤ 4 * b * γ * (r + 1) * (r - 1) / D ∧
      -C ≤ 3 * (r - 1) / 2 := by
  intro u a b γ D C
  have hr0 : 0 < r := zero_lt_one.trans hr
  have ht : 0 < r - 1 := sub_pos.mpr hr
  have hmass : 0 < 1 + r ^ 3 := by positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := (div_lt_one hr0).2 hr
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  have ha_eq : a = u ^ 3 * b := by
    dsimp [a, u, b]
    field_simp [hr0.ne', hmass.ne']
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hmass.ne']
  have hnorm : b * (1 + u ^ 3) = 1 := by
    rw [mul_add, mul_one, mul_comm b, ← ha_eq, add_comm]
    exact hab
  have hinv : 1 / u = r := by simp [u, one_div]
  have hderiv := hot_inner_mixed u a b hu hu1 hb ha_eq hnorm
  rw [hinv] at hderiv
  have hratio : (1 + u) / (1 - u) = (r + 1) / (r - 1) := by
    apply (div_eq_iff (sub_pos.mpr hu1).ne').2
    dsimp [u]
    field_simp [hr0.ne', ht.ne']
  have hq : (1 - u) ^ 2 / (1 + u + u ^ 2) = (r - 1) ^ 2 / D := by
    have hud : 0 < 1 + u + u ^ 2 := by positivity
    apply (div_eq_iff hud.ne').2
    dsimp [u, D]
    field_simp [hr0.ne', show r ^ 2 + r + 1 ≠ 0 by positivity]
  let q := (r - 1) ^ 2 / D
  let p := b * γ * (r + 1) / (r - 1)
  have hp : 0 < p := by dsimp [p]; positivity
  have hneg : -C = p * (2 * (1 - 2 * alpha r) + 2 * q) := by
    dsimp only [C]
    rw [mul_div_assoc (-b * γ), hratio, mul_div_assoc (2 : ℝ), hq]
    dsimp only [p, q]
    ring
  have hscale (c : ℝ) :
      p * (c * q) = c * b * γ * (r + 1) * (r - 1) / D := by
    dsimp only [p, q]
    field_simp [ht.ne', hD.ne']
  obtain ⟨hloss, hLoss⟩ := alpha_loss_bounds hr
  change q / 4 ≤ 1 - 2 * alpha r at hloss
  change 1 - 2 * alpha r ≤ q at hLoss
  have hboundLow : (5 / 2) * b * γ * (r + 1) * (r - 1) / D ≤ -C := by
    rw [← hscale, hneg]
    exact mul_le_mul_of_nonneg_left (by linarith only [hloss]) hp.le
  have hboundHigh : -C ≤ 4 * b * γ * (r + 1) * (r - 1) / D := by
    rw [← hscale, hneg]
    exact mul_le_mul_of_nonneg_left (by linarith only [hLoss]) hp.le
  have hsign : C < 0 := neg_pos.mp (lt_of_lt_of_le (by positivity) hboundLow)
  have hweight : b * γ ≤ 9 / 16 := by
    dsimp only [γ]
    nlinarith only [congrArg (fun x : ℝ => x ^ 2) hab, sq_nonneg (a - b)]
  have hfrac : (r + 1) / D ≤ 2 / 3 := by
    apply (div_le_iff₀ hD).2
    dsimp [D]
    nlinarith only [mul_nonneg ht.le (show 0 ≤ 2 * r + 1 by positivity)]
  refine ⟨hderiv, hsign, hboundLow, hboundHigh, hboundHigh.trans ?_⟩
  calc
    4 * b * γ * (r + 1) * (r - 1) / D = 4 * (b * γ * ((r + 1) / D) * (r - 1)) := by ring
    _ ≤ 4 * ((9 / 16) * (2 / 3) * (r - 1)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right
          (mul_le_mul hweight hfrac (by positivity) (by norm_num)) ht.le) (by norm_num)
    _ = 3 * (r - 1) / 2 := by ring

#print axioms hot_inner_mixed_bound

end D5.S3.Quantum.Semigroups.WuCubicHotInnerMixedBound
