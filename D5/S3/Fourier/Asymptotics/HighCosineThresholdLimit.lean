/- GID: D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/HighCosineThresholdLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First intermediate contact and sharp asymptotic limit for the cyclic two-cosine certificate. -/

import D5.S3.Fourier.Concentration.HighCosineThreshold
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset Filter
open scoped Topology
noncomputable section

namespace D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit

open D5.S3.Fourier.Concentration.HighCosineThreshold

private theorem inverse_gap_difference {l x v u A C : ℝ}
    (hlx : l < x) (hxv : x < v) (hvu : v < u) :
    (A / (u - v) + C / (v - l)) - (A / (u - x) + C / (x - l)) =
      (v - x) * (A / ((u - v) * (u - x)) - C / ((v - l) * (x - l))) := by
  field_simp [sub_ne_zero.mpr hvu.ne', sub_ne_zero.mpr (hxv.trans hvu).ne',
    sub_ne_zero.mpr (hlx.trans hxv).ne', sub_ne_zero.mpr hlx.ne']
  ring

private theorem strict_inverse_gap_dominance {l x v u A C : ℝ}
    (hlx : l < x) (hxv : x < v) (hvu : v < u)
    (h : C * ((u - v) * (u - x)) < A * ((v - l) * (x - l))) :
    A / (u - x) + C / (x - l) < A / (u - v) + C / (v - l) := by
  have hp := mul_pos (sub_pos.mpr hvu) (sub_pos.mpr (hxv.trans hvu))
  have hm := mul_pos (sub_pos.mpr (hlx.trans hxv)) (sub_pos.mpr hlx)
  apply sub_pos.mp
  rw [inverse_gap_difference hlx hxv hvu]
  exact mul_pos (sub_pos.mpr hxv) (sub_pos.mpr ((div_lt_div_iff₀ hm hp).mpr h))

private theorem inv_nat_limit : Tendsto (fun q : ℕ => (q : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private theorem cyclic_versine_limit :
    Tendsto (fun q : ℕ => (q : ℝ)^2 * (1 - Real.cos (2 * Real.pi / q)))
      atTop (𝓝 (2 * Real.pi ^ 2)) := by
  have ht : Tendsto (fun q : ℕ => Real.pi / (q : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using inv_nat_limit.const_mul Real.pi
  have hs := ((Real.continuous_sinc.continuousAt (x := 0)).tendsto.comp ht).pow 2
  simp only [Real.sinc_zero, one_pow] at hs
  have h := hs.const_mul (2 * Real.pi ^ 2)
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  have hqr : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have htq := div_ne_zero Real.pi_ne_zero hqr
  rw [Function.comp_apply, Real.sinc_of_ne_zero htq, div_pow, Real.sin_sq_eq_half_sub,
    ← mul_div_assoc]
  field_simp [hqr, Real.pi_ne_zero]

private theorem tail_moment_ratio_limit (u l : ℕ → ℝ)
    (hu : Tendsto u atTop (𝓝 1)) (hl : Tendsto l atTop (𝓝 (-1))) :
    Tendsto (fun q => 1 + (2 * u q + 1) * (u q - l q) /
      ((1 - u q) * (2 * u q + 1) - (1 - l q) * (2 * l q + 1)))
      atTop (𝓝 4) := by
  have huu := (hu.const_mul 2).add_const 1
  have hll := (hl.const_mul 2).add_const 1
  have hnum := huu.mul (hu.sub hl)
  have hdenom := ((hu.const_sub 1).mul huu).sub ((hl.const_sub 1).mul hll)
  convert (hnum.div hdenom (by norm_num)).const_add 1 using 2; norm_num

private theorem multiplier_slope_order {l u A C : ℝ}
    (hlu : l < u) (hu : u < 1) (hs : u + l < 0) (hAC : C ≤ A) :
    let top := 1 / ((1 - u) * (1 - l))
    let up := A / ((u - 1) * (u - l))
    let low := C / ((l - 1) * (l - u))
    let beta₀ := -(top * (u + l))
    let beta₁ := -(up * (1 + l) + low * (1 + u))
    let gamma₀ := top / 2
    let gamma₁ := (up + low) / 2
    1 - beta₁ / beta₀ ≤ 1 - gamma₁ / gamma₀ ∧
      1 - gamma₁ / gamma₀ = 1 + (A * (1 - l) - C * (1 - u)) / (u - l) := by
  let top : ℝ := 1 / ((1 - u) * (1 - l))
  let up := A / ((u - 1) * (u - l))
  let low := C / ((l - 1) * (l - u))
  have hl := hlu.trans hu
  have ht : 0 < top :=
    div_pos zero_lt_one (mul_pos (sub_pos.mpr hu) (sub_pos.mpr hl))
  change 1 - -(up * (1 + l) + low * (1 + u)) / -(top * (u + l)) ≤
      1 - ((up + low) / 2) / (top / 2) ∧ _
  constructor
  · apply sub_le_sub_left
    have hbeta : 0 < -(top * (u + l)) := neg_pos.mpr (mul_neg_of_pos_of_neg ht hs)
    apply (div_le_div_iff₀ (half_pos ht) hbeta).2
    have hnormal : -(up * (1 + l) + low * (1 + u)) =
        -(u + l) * (up + low) + (A - C) / (u - l) := by
      dsimp [up, low]
      field_simp [sub_ne_zero.mpr hu.ne, sub_ne_zero.mpr hl.ne,
        sub_ne_zero.mpr hlu.ne, sub_ne_zero.mpr hlu.ne']
      ring
    rw [hnormal]
    have hdiff := mul_nonneg (div_nonneg (sub_nonneg.mpr hAC) (sub_nonneg.mpr hlu.le)) (half_pos ht).le
    nlinarith only [hdiff]
  · change 1 - ((up + low) / 2) / (top / 2) = _
    dsimp only [top, up, low]
    field_simp [sub_ne_zero.mpr hu.ne, sub_ne_zero.mpr hu.ne',
      sub_ne_zero.mpr hl.ne, sub_ne_zero.mpr hl.ne',
      sub_ne_zero.mpr hlu.ne, sub_ne_zero.mpr hlu.ne']
    ring

private def grid (q n : ℕ) : ℝ := Real.cos (2 * Real.pi * (n : ℝ) / q)

private theorem grid_strict {q n m : ℕ} (hnm : n < m) (hm : m ≤ q / 2) :
    grid q m < grid q n := by
  have hq : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hm' : 2 * (m : ℝ) ≤ q := by exact_mod_cast (show 2 * m ≤ q by omega)
  have hnm' : (n : ℝ) < m := by exact_mod_cast hnm
  apply Real.cos_lt_cos_of_nonneg_of_le_pi
  · positivity
  · apply (div_le_iff₀ hq).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hm' Real.pi_pos.le]
  · apply (div_lt_div_iff_of_pos_right hq).mpr
    exact mul_lt_mul_of_pos_left hnm' (by positivity)

private theorem grid_one (q : ℕ) : grid q 1 = cyclicUpper q := by
  simp [grid, cyclicUpper]

private theorem grid_two (q : ℕ) : grid q 2 = 2 * (cyclicUpper q)^2 - 1 := by
  rw [grid, cyclicUpper, show 2 * Real.pi * ((2 : ℕ) : ℝ) / q =
    2 * (2 * Real.pi / q) by push_cast; ring, Real.cos_two_mul]

private theorem grid_two_argument (q : ℕ) : grid q 2 = Real.cos (4 * Real.pi / q) := by
  unfold grid
  push_cast
  congr 1
  ring

private theorem grid_lower (q : ℕ) : grid q (q / 2) = cyclicLower q := rfl

private theorem grid_le {q n m : ℕ} (hnm : n ≤ m) (hm : m ≤ q / 2) :
    grid q m ≤ grid q n := by
  rcases lt_or_eq_of_le hnm with h | rfl
  · exact (grid_strict h hm).le
  · exact le_rfl

private theorem grid_reflect {q n k : ℕ} (hq : 0 < q) (h : 2 * n + k = q) :
    grid q n = -Real.cos (Real.pi * k / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h' : 2 * (n : ℝ) + k = q := by exact_mod_cast h
  rw [grid, ← Real.cos_pi_sub]
  congr 1
  apply (div_eq_iff hq'.ne').mpr
  rw [sub_mul, div_mul_cancel₀ _ hq'.ne']
  linear_combination Real.pi * h'

private theorem cyclic_lower_parity {q : ℕ} (hq : 0 < q) :
    cyclicLower q = -Real.cos (Real.pi * ((q % 2 : ℕ) : ℝ) / q) :=
  grid_reflect hq (by omega)

private theorem cyclic_lower_even {q : ℕ} (hq : 0 < q) (he : q % 2 = 0) :
    cyclicLower q = -1 := by
  simp [cyclic_lower_parity hq, he]

private theorem cyclic_lower_odd {q : ℕ} (hq : 0 < q) (ho : q % 2 = 1) :
    cyclicLower q = -Real.cos (Real.pi / q) := by
  simp [cyclic_lower_parity hq, ho]

private theorem grid_bottom_even {q n : ℕ} (hq : 4 ≤ q) (he : q % 2 = 0) (hn : n < q / 2) :
    -cyclicUpper q ≤ grid q n := by
  have h := grid_reflect (n := q / 2 - 1) (k := 2) (by omega : 0 < q) (by omega)
  rw [show Real.pi * ((2 : ℕ) : ℝ) / q = 2 * Real.pi / q by push_cast; ring,
    ← cyclicUpper] at h
  rw [← h]
  exact grid_le (by omega) (by omega)

private theorem grid_bottom_odd {q n : ℕ} (hq : 4 ≤ q) (ho : q % 2 = 1) (hn : n < q / 2) :
    2 * Real.cos (Real.pi / q) * (1 - cyclicUpper q) ≤ grid q n - cyclicLower q := by
  let s : ℝ := Real.pi / q
  have h := grid_reflect (n := q / 2 - 1) (k := 3) (by omega : 0 < q) (by omega)
  rw [show Real.pi * ((3 : ℕ) : ℝ) / q = 3 * s by unfold s; push_cast; ring] at h
  have hcos := Real.cos_add_cos (x := 3 * s) (y := s)
  rw [show (3 * s + s) / 2 = 2 * s by ring, show (3 * s - s) / 2 = s by ring] at hcos
  have hstep : 2 * Real.cos s * (1 - cyclicUpper q) =
      grid q (q / 2 - 1) - cyclicLower q := by
    rw [h, cyclic_lower_odd (by omega : 0 < q) ho,
      show cyclicUpper q = Real.cos (2 * s) by unfold cyclicUpper s; ring_nf]
    linear_combination hcos
  rw [hstep]
  exact sub_le_sub_right (grid_le (by omega) (by omega)) _

private theorem cosine_div_gt {q m : ℕ} (hm : 0 < m) (hmq : m ≤ q) {k b : ℝ}
    (hk : k ≠ 0) (hb : k ^ 2 * 5 / (m : ℝ)^2 ≤ 1 - b) :
    b < Real.cos (k * Real.pi / q) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hq' : (0 : ℝ) < q := by exact_mod_cast (hm.trans_le hmq)
  have hmq' : (m : ℝ) ≤ q := by exact_mod_cast hmq
  have hpi : Real.pi ^ 2 < 10 :=
    (pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by decide : 2 ≠ 0)).trans (by norm_num)
  have hangle := div_ne_zero (mul_ne_zero hk Real.pi_ne_zero) hq'.ne'
  have hcos := Real.one_sub_sq_div_two_lt_cos hangle
  have hbound : (k * Real.pi / q)^2 / 2 < 1 - b := by
    calc
      _ = k ^ 2 * (Real.pi ^ 2 / 2) / (q : ℝ)^2 := by rw [div_pow, mul_pow]; ring
      _ < (k ^ 2 * 5) / (q : ℝ)^2 := div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left (by linarith only [hpi]) (sq_pos_of_ne_zero hk)) (sq_pos_of_pos hq')
      _ ≤ _ := (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hm')
        (pow_le_pow_left₀ hm'.le hmq' 2)).trans hb
  linarith only [hcos, hbound]

private theorem cyclic_upper_gt {q : ℕ} (hq : 13 ≤ q) : 22 / 25 < cyclicUpper q :=
  cosine_div_gt (by decide) hq (by norm_num) (by norm_num)

private theorem cyclic_upper_even_gt {q : ℕ} (hq : 13 ≤ q) (he : q % 2 = 0) :
    8 / 9 < cyclicUpper q :=
  cosine_div_gt (m := 14) (by decide) (by omega) (by norm_num) (by norm_num)

private theorem cyclic_half_cos_gt {q : ℕ} (hq : 13 ≤ q) : 97 / 100 < Real.cos (Real.pi / q) := by
  simpa only [one_mul] using cosine_div_gt (by decide) hq (k := 1) (b := 97 / 100)
    (by norm_num) (by norm_num)

private theorem cyclic_upper_lt_one {q : ℕ} (hq : 4 ≤ q) : cyclicUpper q < 1 := by
  have h := grid_strict (q := q) (n := 0) (m := 1) (by decide) (by omega)
  simpa [grid, cyclicUpper] using h

private theorem upper_add_lower_neg {q : ℕ} (hq : 4 ≤ q) :
    cyclicUpper q + cyclicLower q < 0 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq₂ : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hr : ((q % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast (show q % 2 < 2 by omega)
  rw [cyclicUpper, cyclic_lower_parity (by omega), ← sub_eq_add_neg]
  apply sub_neg.mpr
  apply Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity)
  · exact (div_le_iff₀ hq').mpr (by nlinarith only [mul_le_mul_of_nonneg_left hq₂ Real.pi_pos.le])
  · exact div_lt_div_of_pos_right (by nlinarith only [mul_lt_mul_of_pos_left hr Real.pi_pos]) hq'

private theorem cyclic_readout_eq_grid {q n : ℕ} (hn : 1 ≤ n) (hnh : n ≤ q / 2)
    (i : Fin q) : cyclicReadout q i = grid q n ↔ i.val = n ∨ i.val = q - n := by
  by_cases hi : i.val = 0
  · have hlt := grid_strict (show 0 < n by omega) hnh
    have hne : cyclicReadout q i ≠ grid q n := by
      have hzero : cyclicReadout q i = grid q 0 := by simp [cyclicReadout, grid, hi]
      rw [hzero]
      exact hlt.ne'
    constructor
    · exact fun h => (hne h).elim
    · intro h
      omega
  · obtain ⟨m, _, hmh, hr, hindex⟩ := cyclic_fold i hi
    change cyclicReadout q i = grid q m at hr
    rw [hr]
    have hgrid : grid q m = grid q n ↔ m = n := by
      constructor
      · intro h
        rcases lt_trichotomy m n with hmn | hmn | hnm
        · exact ((grid_strict hmn hnh).ne h.symm).elim
        · exact hmn
        · exact ((grid_strict hnm hmh).ne h).elim
      · rintro rfl
        rfl
    rw [hgrid]
    have hib := i.isLt
    omega

private theorem cyclic_upper_count {q : ℕ} (hq : 4 ≤ q) :
    count (cyclicReadout q) (cyclicUpper q) = 2 := by
  classical
  let a : Fin q := ⟨1, by omega⟩
  let b : Fin q := ⟨q - 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have h' := congrArg Fin.val h
    dsimp [a, b] at h'
    omega
  have hset : univ.filter (fun i : Fin q => cyclicReadout q i = cyclicUpper q) = {a, b} := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton, ← grid_one,
      cyclic_readout_eq_grid (by decide : 1 ≤ 1) (by omega : 1 ≤ q / 2), Fin.ext_iff, a, b]
  rw [count, hset, Finset.card_pair hab]
  norm_num

private theorem cyclic_lower_count_ge_one {q : ℕ} (hq : 4 ≤ q) :
    1 ≤ count (cyclicReadout q) (cyclicLower q) := by
  classical
  unfold count
  have h : (univ.filter (fun i : Fin q => cyclicReadout q i = cyclicLower q)).Nonempty :=
    ⟨⟨q / 2, by omega⟩, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  exact_mod_cast Finset.one_le_card.mpr h

private theorem cyclic_lower_count_even {q : ℕ} (hq : 4 ≤ q) (he : q % 2 = 0) :
    count (cyclicReadout q) (cyclicLower q) = 1 := by
  classical
  let b : Fin q := ⟨q / 2, by omega⟩
  have hset : univ.filter (fun i : Fin q => cyclicReadout q i = cyclicLower q) = {b} := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_singleton, ← grid_lower,
      cyclic_readout_eq_grid (by omega : 1 ≤ q / 2) le_rfl, Fin.ext_iff, b]
    omega
  rw [count, hset, card_singleton, Nat.cast_one]

private theorem upper_limit : Tendsto cyclicUpper atTop (𝓝 1) := by
  have h := inv_nat_limit.const_mul (2 * Real.pi)
  simp only [mul_zero] at h
  change Tendsto (fun q : ℕ => Real.cos (2 * Real.pi / q)) atTop (𝓝 1)
  simpa [div_eq_mul_inv, Real.cos_zero, Function.comp_def] using
    (Real.continuous_cos.continuousAt (x := 0)).tendsto.comp h

private theorem lower_limit : Tendsto cyclicLower atTop (𝓝 (-1)) := by
  have h := inv_nat_limit.const_mul Real.pi
  simp only [mul_zero] at h
  have hcos : Tendsto (fun q : ℕ => -Real.cos (Real.pi / q)) atTop (𝓝 (-1)) := by
    simpa [div_eq_mul_inv, Function.comp_def] using
      ((Real.continuous_cos.continuousAt (x := 0)).tendsto.comp h).neg
  rw [tendsto_def] at hcos ⊢
  intro s hs
  filter_upwards [hcos s hs, eventually_ge_atTop 1] with q hq hq₀
  change cyclicLower q ∈ s
  by_cases he : q % 2 = 0
  · rw [cyclic_lower_even (by omega) he]
    exact mem_of_mem_nhds hs
  · rwa [cyclic_lower_odd (by omega) (by omega)]

private theorem upper_fraction_limit :
    Tendsto (fun q => upperFraction (cyclicUpper q) (cyclicLower q)) atTop (𝓝 1) := by
  have hu := upper_limit.sub (((upper_limit.pow 2).const_mul 2).sub_const 1)
  have hl := lower_limit.sub (((lower_limit.pow 2).const_mul 2).sub_const 1)
  convert hl.neg.div (hu.sub hl) (by norm_num) using 2 <;> norm_num [upperFraction, difference, second]

private def upperWeight (q : ℕ) : ℝ :=
  upperFraction (cyclicUpper q) (cyclicLower q) / count (cyclicReadout q) (cyclicUpper q)

private def lowerWeight (q : ℕ) : ℝ :=
  (1 - upperFraction (cyclicUpper q) (cyclicLower q)) / count (cyclicReadout q) (cyclicLower q)

private theorem upper_weight_limit : Tendsto upperWeight atTop (𝓝 (1/2)) := by
  apply (upper_fraction_limit.div_const 2).congr'
  filter_upwards [eventually_ge_atTop 4] with q hq
  simp [upperWeight, cyclic_upper_count hq]

private theorem difference_factor (x : ℝ) :
    difference x = (1 - x) * (2 * x + 1) := by
  unfold difference second
  ring

private theorem fraction_bounds {u l : ℝ}
    (hdu : 0 < difference u) (hdl : difference l < 0) :
    0 < upperFraction u l ∧ upperFraction u l < 1 := by
  have hd : 0 < difference u - difference l := by linarith
  exact ⟨div_pos (neg_pos.mpr hdl) hd, (div_lt_one hd).mpr (by linarith)⟩

private theorem upperWeight_pos {q : ℕ} (hq : 4 ≤ q)
    (hp : 0 < upperFraction (cyclicUpper q) (cyclicLower q)) : 0 < upperWeight q := by
  rw [upperWeight, cyclic_upper_count hq]
  exact div_pos hp (by norm_num)

private theorem cyclic_difference_signs {q : ℕ} (hq : 13 ≤ q) :
    0 < difference (cyclicUpper q) ∧ difference (cyclicLower q) < 0 := by
  have hu := cyclic_upper_gt hq
  have ht := cyclic_upper_lt_one (by omega : 4 ≤ q)
  have hl : cyclicLower q < -(1 / 2 : ℝ) := by
    by_cases he : q % 2 = 0
    · rw [cyclic_lower_even (by omega) he]
      norm_num
    · rw [cyclic_lower_odd (by omega) (by omega)]
      linarith only [cyclic_half_cos_gt hq]
  rw [difference_factor, difference_factor]
  exact ⟨mul_pos (sub_pos.mpr ht) (by linarith only [hu]),
    mul_neg_of_pos_of_neg (by linarith only [hl]) (by linarith only [hl])⟩

private theorem cyclic_fraction_bounds {q : ℕ} (hq : 13 ≤ q) :
    0 < upperFraction (cyclicUpper q) (cyclicLower q) ∧
      upperFraction (cyclicUpper q) (cyclicLower q) < 1 :=
  fraction_bounds (cyclic_difference_signs hq).1 (cyclic_difference_signs hq).2

private theorem lowerWeight_eq {q : ℕ} (hq : 4 ≤ q)
    (hdu : 0 < difference (cyclicUpper q)) (hdl : difference (cyclicLower q) < 0) :
    lowerWeight q = upperWeight q *
      (2 * difference (cyclicUpper q) / (count (cyclicReadout q) (cyclicLower q) *
        (-difference (cyclicLower q)))) := by
  have hd : difference (cyclicUpper q) - difference (cyclicLower q) ≠ 0 := by
    linarith only [hdu, hdl]
  have hc : count (cyclicReadout q) (cyclicLower q) ≠ 0 :=
    ne_of_gt (zero_lt_one.trans_le (cyclic_lower_count_ge_one hq))
  unfold lowerWeight upperWeight upperFraction
  rw [cyclic_upper_count hq]
  field_simp [hd, hc, hdl.ne]
  ring

private theorem cyclic_weight_bound {q : ℕ} (hq : 13 ≤ q) :
    lowerWeight q < (if q % 2 = 0 then (8 / 25 : ℝ) else 2 / 5) * upperWeight q := by
  let u := cyclicUpper q
  let l := cyclicLower q
  let M := count (cyclicReadout q) l
  have hM : 1 ≤ M := cyclic_lower_count_ge_one (by omega)
  obtain ⟨hdu, hdl⟩ := cyclic_difference_signs hq
  have hA := upperWeight_pos (by omega) (fraction_bounds hdu hdl).1
  rw [lowerWeight_eq (by omega) hdu hdl, mul_comm (upperWeight q)]
  apply mul_lt_mul_of_pos_right _ hA
  apply (div_lt_iff₀ (mul_pos (zero_lt_one.trans_le hM) (neg_pos.mpr hdl))).mpr
  have hden : -difference l ≤ M * -difference l :=
    le_mul_of_one_le_left (neg_nonneg.mpr hdl.le) hM
  change 2 * difference u < _ * (M * -difference l)
  by_cases he : q % 2 = 0
  · rw [ite_eq_left he]
    have hu : (8 / 9 : ℝ) < u := cyclic_upper_even_gt hq he
    have hd : difference u < 25 / 81 := by
      rw [difference_factor]
      have h := mul_neg_of_pos_of_neg (sub_pos.mpr hu)
        (show 1 - 2 * (u + 8 / 9) < 0 by linarith only [hu])
      nlinarith only [h]
    have hl : -difference l = 2 := by
      dsimp only [l]
      rw [cyclic_lower_even (by omega) he]
      norm_num [difference, second]
    rw [hl] at hden ⊢
    linarith only [hden, hd]
  · rw [ite_eq_right he]
    have hu : (22 / 25 : ℝ) < u := cyclic_upper_gt hq
    have hut := cyclic_upper_lt_one (by omega : 4 ≤ q)
    have hd : difference u < 9 / 25 := by
      rw [difference_factor]
      have h := mul_lt_mul_of_pos_right
        (show 1 - u < 3 / 25 by linarith only [hu])
        (show 0 < 2 * u + 1 by linarith only [hu])
      linarith only [h, hut]
    have hl : l < -(97 / 100 : ℝ) := by
      dsimp only [l]
      rw [cyclic_lower_odd (by omega) (by omega)]
      linarith only [cyclic_half_cos_gt hq]
    have hd' : (9 / 5 : ℝ) < -difference l := by
      rw [difference_factor, ← mul_neg]
      have h := mul_lt_mul (show (197 / 100 : ℝ) < 1 - l by linarith only [hl])
        (show (94 / 100 : ℝ) ≤ -(2 * l + 1) by linarith only [hl])
        (by norm_num) (show 0 ≤ 1 - l by linarith only [hl])
      linarith only [h]
    linarith only [hden, hd, hd']

private theorem lower_weight_limit : Tendsto lowerWeight atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (show Tendsto (fun q => 1 - upperFraction (cyclicUpper q) (cyclicLower q)) atTop (𝓝 0) by
      simpa using upper_fraction_limit.const_sub 1)
  · filter_upwards [eventually_ge_atTop 13] with q hq
    have hp := cyclic_fraction_bounds hq
    exact div_nonneg (sub_nonneg.mpr hp.2.le) ((cyclic_lower_count_ge_one (by omega : 4 ≤ q)).trans' zero_le_one)
  · filter_upwards [eventually_ge_atTop 13] with q hq
    have hp := cyclic_fraction_bounds hq
    exact div_le_self (sub_nonneg.mpr hp.2.le) (cyclic_lower_count_ge_one (by omega : 4 ≤ q))

private theorem intermediate_level {q : ℕ} (i : Fin q)
    (hl : cyclicLower q < cyclicReadout q i) (hu : cyclicReadout q i < cyclicUpper q) :
    ∃ n : ℕ, 2 ≤ n ∧ n < q / 2 ∧ cyclicReadout q i = grid q n := by
  have hk : i.val ≠ 0 := by
    intro h
    have he : cyclicReadout q i = 1 := by simp [cyclicReadout, h]
    rw [he] at hu
    exact (not_lt_of_ge (Real.cos_le_one _)) hu
  obtain ⟨n, hn, hnh, he, _⟩ := cyclic_fold i hk
  change cyclicReadout q i = grid q n at he
  refine ⟨n, ?_, ?_, he⟩
  · by_contra! h
    have hn1 : n = 1 := by omega
    rw [he, hn1, grid_one] at hu
    exact lt_irrefl _ hu
  · by_contra! h
    have hnh' : n = q / 2 := by omega
    rw [he, hnh', grid_lower] at hl
    exact lt_irrefl _ hl

private theorem grid_two_between {q : ℕ} (hq : 6 ≤ q) :
    cyclicLower q < grid q 2 ∧ grid q 2 < cyclicUpper q := by
  rw [← grid_lower, ← grid_one]
  exact ⟨grid_strict (by omega) le_rfl, grid_strict (by decide) (by omega)⟩

private def middleSlope (q : ℕ) (x : ℝ) : ℝ :=
  let P := polynomial (cyclicUpper q) (cyclicLower q)
    (count (cyclicReadout q) (cyclicUpper q)) (count (cyclicReadout q) (cyclicLower q))
  Concentration.HighCosineThreshold.slope (P 0 x) (P 1 x)

private theorem middleSlope_eq {q : ℕ} {x : ℝ}
    (hl : cyclicLower q < x) (hu : x < cyclicUpper q) (hut : cyclicUpper q < 1) :
    let u := cyclicUpper q
    let l := cyclicLower q
    let A := upperWeight q
    let C := lowerWeight q
    middleSlope q x =
      (1 + (A * (1 - l) - C * (1 - u)) / (u - l)) +
      ((1 - u) * (1 - l) / (u - l)) * (A / (u - x) + C / (x - l)) := by
  dsimp [middleSlope, Concentration.HighCosineThreshold.slope, polynomial, topCoeff,
    upperCoeff, lowerCoeff, upperWeight, lowerWeight]
  simp only [sub_zero, zero_div, zero_mul, one_mul, add_zero]
  have hlu := hl.trans hu
  have hlt := hlu.trans hut
  field_simp [sub_ne_zero.mpr hut.ne, sub_ne_zero.mpr hut.ne', sub_ne_zero.mpr hlt.ne,
    sub_ne_zero.mpr hlt.ne', sub_ne_zero.mpr hlu.ne, sub_ne_zero.mpr hlu.ne',
    sub_ne_zero.mpr hl.ne', sub_ne_zero.mpr hu.ne, sub_ne_zero.mpr hu.ne']
  ring

private theorem grid_two_gap (q : ℕ) :
    cyclicUpper q - grid q 2 = (1 - cyclicUpper q) * (2 * cyclicUpper q + 1) := by
  rw [grid_two]
  ring

private theorem middleSlope_two_limit :
    Tendsto (fun q => middleSlope q (grid q 2)) atTop (𝓝 (5 / 3)) := by
  have hspread := upper_limit.sub lower_limit
  have hu := upper_limit.const_sub 1
  have hl := lower_limit.const_sub 1
  have hv : Tendsto (fun q => grid q 2) atTop (𝓝 1) := by
    have h := ((upper_limit.pow 2).const_mul 2).sub_const 1
    norm_num at h
    simpa only [grid_two] using h
  have hbase := (((upper_weight_limit.mul hl).sub (lower_weight_limit.mul hu)).div hspread
    (by norm_num)).const_add 1
  have htop := (upper_weight_limit.mul hl).div
    (hspread.mul ((upper_limit.const_mul 2).add_const 1)) (by norm_num)
  have hbottom := ((hu.mul hl).mul lower_weight_limit).div
    (hspread.mul (hv.sub lower_limit)) (by norm_num)
  have h := (hbase.add htop).add hbottom
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 6] with q hq
  obtain ⟨hlv, hvu⟩ := grid_two_between hq
  have hut := cyclic_upper_lt_one (by omega : 4 ≤ q)
  have hδ := sub_pos.mpr hut
  have hgap := grid_two_gap q
  have hu₁ := (mul_pos_iff_of_pos_left hδ).mp (hgap ▸ sub_pos.mpr hvu)
  rw [middleSlope_eq hlv hvu hut, hgap]
  field_simp [hδ.ne', hu₁.ne', (sub_pos.mpr (hlv.trans hvu)).ne', (sub_pos.mpr hlv).ne']
  ring

private theorem cyclic_inverse_gap_comparison {q n : ℕ} (hq : 13 ≤ q) (hn : n < q / 2)
    {x : ℝ} (hxv : x < grid q 2) (hx : x = grid q n) :
    let u := cyclicUpper q
    let l := cyclicLower q
    let v := grid q 2
    lowerWeight q * ((u - v) * (u - x)) < upperWeight q * ((v - l) * (x - l)) := by
  dsimp only
  let u := cyclicUpper q
  let l := cyclicLower q
  let v := grid q 2
  let A := upperWeight q
  let C := lowerWeight q
  change C * ((u - v) * (u - x)) < A * ((v - l) * (x - l))
  have hut : u < 1 := cyclic_upper_lt_one (by omega)
  have hδ := sub_pos.mpr hut
  obtain ⟨hlv, hvu⟩ := grid_two_between (by omega : 6 ≤ q)
  change l < v at hlv
  change v < u at hvu
  have huv := sub_pos.mpr hvu
  have hux := sub_pos.mpr (hxv.trans hvu)
  have hv : v = 2 * u^2 - 1 := grid_two q
  have huv_eq : u - v = (1 - u) * (2 * u + 1) := grid_two_gap q
  have hA : 0 < A := upperWeight_pos (by omega) (cyclic_fraction_bounds hq).1
  have hw := cyclic_weight_bound hq
  change C < _ at hw
  by_cases he : q % 2 = 0
  · rw [ite_eq_left he] at hw
    have hl : l = -1 := cyclic_lower_even (by omega) he
    have hu : (8 / 9 : ℝ) < u := cyclic_upper_even_gt hq he
    have h0u : 0 < u := by linarith only [hu]
    have hxL : -u ≤ x := hx ▸ grid_bottom_even (by omega) he hn
    have hratio : 8 / 25 * (2 * u + 1) < u := by linarith only [hu]
    calc
      _ < (8 / 25 * A) * ((u - v) * (u - x)) :=
        mul_lt_mul_of_pos_right hw (mul_pos huv hux)
      _ ≤ (8 / 25 * A) * ((u - v) * (2 * u)) := by
        gcongr
        linarith only [hxL]
      _ = (A * ((1 - u) * (2 * u))) * (8 / 25 * (2 * u + 1)) := by rw [huv_eq]; ring
      _ < (A * ((1 - u) * (2 * u))) * u :=
        mul_lt_mul_of_pos_left hratio (mul_pos hA (mul_pos hδ (by positivity)))
      _ = A * ((v - l) * (1 - u)) := by rw [hv, hl]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hA.le
        apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hlv.le)
        rw [hl]
        linarith only [hxL]
  · rw [ite_eq_right he] at hw
    have ho : q % 2 = 1 := by omega
    let w := Real.cos (Real.pi / q)
    have hl : l = -w := cyclic_lower_odd (by omega) ho
    have hw₀ : (97 / 100 : ℝ) < w := cyclic_half_cos_gt hq
    have hu : (22 / 25 : ℝ) < u := cyclic_upper_gt hq
    have hspread : (3 / 2 : ℝ) < v - l := by
      rw [hv, hl]
      nlinarith only [hw₀, hu, sq_nonneg (u - 22 / 25)]
    have hxL : 2 * w * (1 - u) ≤ x - l := hx ▸ grid_bottom_odd (by omega) ho hn
    have hgap : (19 / 10 : ℝ) * (1 - u) ≤ x - l := by
      refine (mul_le_mul_of_nonneg_right ?_ hδ.le).trans hxL
      linarith only [hw₀]
    have hupper : u - v ≤ 3 * (1 - u) := by
      rw [hv]
      nlinarith only [sq_nonneg (1 - u)]
    have hx₁ : -1 ≤ x := by rw [hx, grid]; exact Real.neg_one_le_cos _
    have hwidth : u - x ≤ 2 := by linarith only [hx₁, hut]
    calc
      _ < (2 / 5 * A) * ((u - v) * (u - x)) :=
        mul_lt_mul_of_pos_right hw (mul_pos huv hux)
      _ ≤ (2 / 5 * A) * ((3 * (1 - u)) * 2) := by gcongr
      _ = A * ((12 / 5) * (1 - u)) := by ring
      _ ≤ A * ((3 / 2) * ((19 / 10) * (1 - u))) := by
        rw [← mul_assoc (3 / 2 : ℝ)]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (by norm_num) hδ.le) hA.le
      _ ≤ _ := by gcongr

private theorem strict_slope_dominance {q : ℕ} (hq13 : 13 ≤ q) :
    let c := cyclicReadout q
    let u := cyclicUpper q
    let l := cyclicLower q
    let v := grid q 2
    let β := firstMultiplier u l (count c u) (count c l)
    let γ := secondMultiplier u l (count c u) (count c l)
    1 < middleSlope q v ∧
      Concentration.HighCosineThreshold.slope (β 0) (β 1) < middleSlope q v ∧
      Concentration.HighCosineThreshold.slope (γ 0) (γ 1) < middleSlope q v ∧
      (∀ i, l < c i → c i < u → c i ≠ v → middleSlope q (c i) < middleSlope q v) := by
  dsimp only
  have hut := cyclic_upper_lt_one (by omega : 4 ≤ q)
  have hp := cyclic_fraction_bounds hq13
  let c := cyclicReadout q
  let u := cyclicUpper q
  let l := cyclicLower q
  let v := grid q 2
  let A := upperWeight q
  let C := lowerWeight q
  have hA : 0 < A := upperWeight_pos (by omega) hp.1
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hp.2.le)
    ((cyclic_lower_count_ge_one (by omega : 4 ≤ q)).trans' zero_le_one)
  have hs := upper_add_lower_neg (by omega : 4 ≤ q)
  obtain ⟨hlv, hvu⟩ := grid_two_between (by omega : 6 ≤ q)
  have hlu := hlv.trans hvu
  have hlt := hlu.trans hut
  have hK : 0 < (1 - u) * (1 - l) / (u - l) :=
    div_pos (mul_pos (sub_pos.mpr hut) (sub_pos.mpr hlt)) (sub_pos.mpr hlu)
  have hC_A : C ≤ A := by
    have hw := cyclic_weight_bound hq13
    change C < _ at hw
    split at hw <;> linarith only [hA, hw]
  let β := firstMultiplier u l (count c u) (count c l)
  let γ := secondMultiplier u l (count c u) (count c l)
  obtain ⟨hβγ, hγ⟩ := multiplier_slope_order hlu hut hs hC_A
  have hβγ' : Concentration.HighCosineThreshold.slope (β 0) (β 1) ≤
      Concentration.HighCosineThreshold.slope (γ 0) (γ 1) := by
    simpa [Concentration.HighCosineThreshold.slope, firstMultiplier, secondMultiplier,
      topCoeff, upperCoeff, lowerCoeff, β, γ, A, C, upperWeight, lowerWeight, c, u, l] using hβγ
  have hγ' : Concentration.HighCosineThreshold.slope (γ 0) (γ 1) =
      1 + (A * (1 - l) - C * (1 - u)) / (u - l) := by
    simpa [Concentration.HighCosineThreshold.slope, secondMultiplier, topCoeff, upperCoeff,
      lowerCoeff, γ, A, C, upperWeight, lowerWeight, c, u, l] using hγ
  have hγS : Concentration.HighCosineThreshold.slope (γ 0) (γ 1) < middleSlope q v := by
    rw [hγ', middleSlope_eq hlv hvu hut]
    exact lt_add_of_pos_right _ (mul_pos hK
      (add_pos_of_pos_of_nonneg (div_pos hA (sub_pos.mpr hvu))
        (div_nonneg hC (sub_nonneg.mpr hlv.le))))
  have hγ₁ : 1 ≤ Concentration.HighCosineThreshold.slope (γ 0) (γ 1) := by
    rw [hγ']
    apply le_add_of_nonneg_right
    exact div_nonneg (sub_nonneg.mpr (mul_le_mul hC_A (by linarith only [hlu])
      (sub_nonneg.mpr hut.le) hA.le)) (sub_nonneg.mpr hlu.le)
  refine ⟨hγ₁.trans_lt hγS, hβγ'.trans_lt hγS, hγS, ?_⟩
  intro i hiL hiU hiV
  let x := c i
  obtain ⟨n, hn, hnh, he⟩ := intermediate_level i hiL hiU
  have hn2 : 2 < n := by
    by_contra! h
    have hn' : n = 2 := by omega
    exact hiV (by simpa [hn', v] using he)
  have hxv : x < v := by
    change x = grid q n at he
    rw [he]
    exact grid_strict hn2 hnh.le
  have hcross := cyclic_inverse_gap_comparison hq13 hnh hxv (x := x) he
  have hcompare := strict_inverse_gap_dominance hiL hxv hvu hcross
  rw [middleSlope_eq hiL hiU hut, middleSlope_eq hlv hvu hut]
  exact add_lt_add_right (mul_lt_mul_of_pos_left hcompare hK) _

private theorem middleSlope_mem {q : ℕ} (i : Fin q)
    (hl : cyclicLower q < cyclicReadout q i) (hu : cyclicReadout q i < cyclicUpper q) :
    middleSlope q (cyclicReadout q i) ∈
      certificateSlopes (cyclicReadout q) (cyclicUpper q) (cyclicLower q) := by
  classical
  unfold certificateSlopes
  exact mem_insert_of_mem (mem_insert_of_mem (mem_insert_of_mem
    (mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hl, hu⟩, rfl⟩)))

/-- The strict comparison identifies the actual finite supremum in the predecessor. -/
private theorem slope_maximum {q : ℕ} (hq : 13 ≤ q) :
    slopeBound (cyclicReadout q) (cyclicUpper q) (cyclicLower q) = middleSlope q (grid q 2) := by
  classical
  let c := cyclicReadout q
  let u := cyclicUpper q
  let l := cyclicLower q
  let v := grid q 2
  obtain ⟨hS, hβ, hγ, hm⟩ := strict_slope_dominance hq
  obtain ⟨hvl, hvu⟩ := grid_two_between (by omega : 6 ≤ q)
  let i : Fin q := ⟨2, by omega⟩
  have hmem : middleSlope q v ∈ certificateSlopes c u l := middleSlope_mem i hvl hvu
  unfold slopeBound
  apply le_antisymm
  · apply Finset.sup'_le
    intro s hs
    simp only [certificateSlopes, mem_insert, mem_image, mem_filter, mem_univ, true_and] at hs
    rcases hs with rfl | rfl | rfl | ⟨j, ⟨hjL, hjU⟩, rfl⟩
    · exact hS.le
    · exact hβ.le
    · exact hγ.le
    · change middleSlope q (c j) ≤ middleSlope q v
      by_cases h : c j = v
      · rw [h]
      · exact (hm j hjL hjU h).le
  · exact Finset.le_sup' id hmem

private theorem affine_slope_value {f : ℝ → ℝ} {r : ℝ} (h₀ : f 0 ≠ 0)
    (haff : f r = (1 - r) * f 0 + r * f 1) :
    f r = f 0 * (1 - r * Concentration.HighCosineThreshold.slope (f 0) (f 1)) := by
  rw [haff, Concentration.HighCosineThreshold.slope]
  field_simp
  ring

private theorem polynomial_zero_neg {l u nu nl x : ℝ}
    (hut : u < 1) (hxl : l < x) (hxu : x < u) : polynomial u l nu nl 0 x < 0 := by
  have ht : 0 < topCoeff u l 0 := by
    unfold topCoeff
    exact div_pos (by norm_num) (mul_pos (sub_pos.mpr hut) (sub_pos.mpr (hxl.trans (hxu.trans hut))))
  simp only [polynomial, upperCoeff, lowerCoeff, zero_mul, zero_div, add_zero]
  exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg ht (sub_neg.mpr hxu)) (sub_pos.mpr hxl)

private theorem polynomial_middle_affine {q : ℕ} {x t : ℝ}
    (hut : cyclicUpper q < 1) (hxl : cyclicLower q < x) (hxu : x < cyclicUpper q) :
    let c := cyclicReadout q
    let u := cyclicUpper q
    let l := cyclicLower q
    let P := polynomial u l (count c u) (count c l)
    P t x = P 0 x * (1 - t * middleSlope q x) := by
  dsimp only
  apply affine_slope_value
    (f := fun t => polynomial (cyclicUpper q) (cyclicLower q)
      (count (cyclicReadout q) (cyclicUpper q)) (count (cyclicReadout q) (cyclicLower q)) t x)
    (polynomial_zero_neg hut hxl hxu).ne
  unfold polynomial topCoeff upperCoeff lowerCoeff
  simp only [div_eq_mul_inv]
  ring

private theorem cutoff_tail_mass {ι : Type*} [Fintype ι] (c : ι → ℝ) {u l : ℝ}
    (hb : tailMoment u l < 1) :
    (1 - criticalThreshold c u l) / (1 - tailMoment u l) = 1 / slopeBound c u l := by
  rw [criticalThreshold, sub_sub_cancel, div_right_comm, div_self (sub_pos.mpr hb).ne']

/-- For every modulus at least thirteen the exact predecessor cutoff has a unique distinct
intermediate contact level, with both moment multipliers still strictly positive. -/
theorem cyclic_threshold_first_contact (q : ℕ) (hq13 : 13 ≤ q) :
  let contact := fun q : ℕ => Real.cos (4 * Real.pi / q)
  let c := cyclicReadout q
  let u := cyclicUpper q
  let l := cyclicLower q
  let v := contact q
  let a := criticalThreshold c u l
  let r := (1 - a) / (1 - tailMoment u l)
  let nu := count c u
  let nl := count c l
  let P := polynomial u l nu nl r
  let β := firstMultiplier u l nu nl r
  let γ := secondMultiplier u l nu nl r
  l < v ∧ v < u ∧ (∃ i, c i = v) ∧ 0 < r ∧ r < 1 ∧
    0 < β ∧ 0 < γ ∧ P v = 0 ∧
    (∀ i, l < c i → c i < u → c i ≠ v → P (c i) < 0) ∧
    P 1 = 1 - r ∧ P u = r * upperFraction u l / nu ∧
    P l = r * (1 - upperFraction u l) / nl ∧
    (∀ x, P x = (topCoeff u l r * u * l + upperCoeff u l nu r * l +
      lowerCoeff u l nl r * u + γ) + β * x + γ * (2 * x^2 - 1)) ∧
    (∀ i, weights c u l r i = max 0 (P (c i))) ∧ IsCertified c u l a ∧
    a < 1 ∧ polynomial u l nu nl 0 v < 0 ∧
    (∀ a' : ℝ, polynomial u l nu nl ((1 - a') / (1 - tailMoment u l)) v =
      polynomial u l nu nl 0 v * ((a' - a) / (1 - a))) := by
  dsimp only
  have hmax := slope_maximum hq13
  have hp := cyclic_fraction_bounds hq13
  have hut := cyclic_upper_lt_one (by omega : 4 ≤ q)
  have hs := upper_add_lower_neg (by omega : 4 ≤ q)
  obtain ⟨hlv, hvu⟩ := grid_two_between (by omega : 6 ≤ q)
  obtain ⟨hS, hβ, hγ, hm⟩ := strict_slope_dominance hq13
  let c := cyclicReadout q
  let u := cyclicUpper q
  let l := cyclicLower q
  let v := grid q 2
  let a := criticalThreshold c u l
  let r := (1 - a) / (1 - tailMoment u l)
  let nu := count c u
  let nl := count c l
  let P := polynomial u l nu nl
  let β := firstMultiplier u l nu nl
  let γ := secondMultiplier u l nu nl
  let S := middleSlope q v
  have hlu := hlv.trans hvu
  have hlt := hlu.trans hut
  have hv := grid_two_argument q
  have hi : ∃ i, c i = v := ⟨⟨2, by omega⟩, rfl⟩
  obtain ⟨hac, ha, hcert, _⟩ := cyclic_high_threshold_certificate (by omega : 4 ≤ q)
  have hb : tailMoment u l < 1 := hac.trans ha
  have hB : 1 < S := hS
  have hBr : r = 1 / S := by
    change (1 - a) / (1 - tailMoment u l) = _
    rw [cutoff_tail_mass c hb, hmax]
  have hr : 0 < r := by rw [hBr]; exact div_pos zero_lt_one (zero_lt_one.trans hB)
  have hr1 : r < 1 := by rw [hBr]; exact (div_lt_one (zero_lt_one.trans hB)).mpr hB
  have hrS : r * S = 1 := by rw [hBr, div_mul_cancel₀ _ (ne_of_gt (zero_lt_one.trans hB))]
  have hltS {s : ℝ} (hs : s < S) : 0 < 1 - r * s := by
    have h := mul_lt_mul_of_pos_left hs hr
    rw [hrS] at h
    exact sub_pos.mpr h
  have ht : 0 < topCoeff u l 0 := by
    unfold topCoeff
    exact div_pos (by norm_num) (mul_pos (sub_pos.mpr hut) (sub_pos.mpr hlt))
  have hb0 : 0 < β 0 := by
    have h : topCoeff u l 0 * (u + l) < 0 := mul_neg_of_pos_of_neg ht hs
    simp [β, firstMultiplier, upperCoeff, lowerCoeff, h]
  have hg0 : 0 < γ 0 := by
    simp [γ, secondMultiplier, upperCoeff, lowerCoeff, ht]
  have hbaff := affine_slope_value (f := β) hb0.ne' (r := r) (by
    unfold β firstMultiplier topCoeff upperCoeff lowerCoeff
    simp only [div_eq_mul_inv]
    ring)
  have hgaff := affine_slope_value (f := γ) hg0.ne' (r := r) (by
    unfold γ secondMultiplier topCoeff upperCoeff lowerCoeff
    simp only [div_eq_mul_inv]
    ring)
  have hβpos : 0 < β r := by rw [hbaff]; exact mul_pos hb0 (hltS hβ)
  have hγpos : 0 < γ r := by rw [hgaff]; exact mul_pos hg0 (hltS hγ)
  have hPaff (t x : ℝ) (hxL : l < x) (hxU : x < u) :
      P t x = P 0 x * (1 - t * middleSlope q x) :=
    polynomial_middle_affine hut hxL hxU
  have hz : P r v = 0 := by
    rw [hPaff r v hlv hvu]
    change P 0 v * (1 - r * S) = 0
    rw [hrS, sub_self, mul_zero]
  have hneg (i : Fin q) (hiL : l < c i) (hiU : c i < u) (hiV : c i ≠ v) :
      P r (c i) < 0 := by
    rw [hPaff r (c i) hiL hiU]
    exact mul_neg_of_neg_of_pos (polynomial_zero_neg hut hiL hiU) (hltS (hm i hiL hiU hiV))
  have hnonpos (i : Fin q) (hiL : l < c i) (hiU : c i < u) : P r (c i) ≤ 0 := by
    by_cases h : c i = v
    · rw [h, hz]
    · exact (hneg i hiL hiU h).le
  have hlevels (i : Fin q) : c i = 1 ∨ (l ≤ c i ∧ c i ≤ u) := by
    by_cases h : i.val = 0
    · exact Or.inl (by simp [c, cyclicReadout, h])
    · obtain ⟨n, hn, hnh, he, _⟩ := cyclic_fold i h
      change c i = grid q n at he
      right
      rw [he]
      change cyclicLower q ≤ grid q n ∧ grid q n ≤ cyclicUpper q
      rw [← grid_lower, ← grid_one]
      exact ⟨grid_le hnh le_rfl, grid_le hn hnh⟩
  have hvals := polynomial_values hut hlu nu nl r
  have hmaxval := weights_eq_max c hut hlu hlevels hr.le hr1.le hp.1.le hp.2.le hnonpos
  have hcert' : IsCertified c u l a := hcert a le_rfl ha.le
  have hcross (a' : ℝ) :
      P ((1 - a') / (1 - tailMoment u l)) v = P 0 v * ((a' - a) / (1 - a)) := by
    rw [hPaff _ v hlv hvu]
    congr 1
    change 1 - (1 - a') / (1 - tailMoment u l) * S = _
    have hgap : (1 - a) * S = 1 - tailMoment u l := by
      dsimp only [a, criticalThreshold]
      rw [hmax, sub_sub_cancel]
      exact div_mul_cancel₀ _ (ne_of_gt (zero_lt_one.trans hB))
    have hane : 1 - a ≠ 0 := sub_ne_zero.mpr ha.ne'
    have hSne : S ≠ 0 := ne_of_gt (zero_lt_one.trans hB)
    rw [← hgap, div_mul_eq_mul_div, mul_comm (1 - a) S, mul_comm (1 - a') S,
      mul_div_mul_left _ _ hSne]
    apply (eq_div_iff hane).mpr
    rw [sub_mul, div_mul_cancel₀ _ hane]
    ring
  rw [← hv]
  exact ⟨hlv, hvu, hi, hr, hr1, hβpos, hγpos, hz, hneg, hvals.1, hvals.2.1, hvals.2.2,
    polynomial_expand u l nu nl r, hmaxval, hcert', ha, polynomial_zero_neg hut hlv hvu, hcross⟩

/-- At modulus twelve the second grid level is strictly below contact at the actual cutoff. -/
theorem cyclic_threshold_twelve_no_contact :
    let q : ℕ := 12
    let c := cyclicReadout q
    let u := cyclicUpper q
    let l := cyclicLower q
    let a := criticalThreshold c u l
    let r := (1 - a) / (1 - tailMoment u l)
    polynomial u l (count c u) (count c l) r (Real.cos (4 * Real.pi / q)) < 0 := by
  classical
  dsimp only
  let u := cyclicUpper 12
  let l := cyclicLower 12
  let x := grid 12 5
  let v := grid 12 2
  let A := upperWeight 12
  let C := lowerWeight 12
  have hut : u < 1 := cyclic_upper_lt_one (by decide)
  have hlu : l < u := (grid_two_between (by decide : 6 ≤ 12)).1.trans
    (grid_two_between (by decide : 6 ≤ 12)).2
  have hxl : l < x := grid_strict (by decide : 5 < 12 / 2) le_rfl
  have hxv : x < v := grid_strict (by decide : 2 < 5) (by decide : 5 ≤ 12 / 2)
  have hvu : v < u := (grid_two_between (by decide : 6 ≤ 12)).2
  have hl : l = -1 := cyclic_lower_even (by decide) (by decide)
  have hx : x = -u := by
    change grid 12 5 = -cyclicUpper 12
    rw [grid_reflect (k := 2) (by decide) (by decide), cyclicUpper]
    norm_num
    ring_nf
  have hu : u = Real.sqrt 3 / 2 := by
    change Real.cos (2 * Real.pi / (12 : ℝ)) = _
    rw [show 2 * Real.pi / (12 : ℝ) = Real.pi / 6 by ring, Real.cos_pi_div_six]
  have hu₀ : 0 < u := by rw [hu]; positivity
  have hu₂ : u ^ 2 = 3 / 4 := by rw [hu, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hv : v = 2 * u^2 - 1 := grid_two 12
  have hdu : 0 < difference u := by
    rw [difference_factor]
    exact mul_pos (sub_pos.mpr hut) (by linarith only [hu₀])
  have hdl : difference l = -2 := by rw [hl]; norm_num [difference, second]
  have hdl₀ : difference l < 0 := by rw [hdl]; norm_num
  have hA : 0 < A := upperWeight_pos (by decide) (fraction_bounds hdu hdl₀).1
  have hC : C = A * difference u := by
    unfold C
    rw [lowerWeight_eq (by decide) hdu hdl₀, cyclic_lower_count_even (by decide) (by decide), hdl]
    change A * (2 * difference u / (1 * -(-2))) = A * difference u
    ring
  have hD : difference u * (2 * u + 1) = 1 := by
    rw [difference_factor]
    linear_combination -4 * u * hu₂
  have huv : u - v = (1 - u) * (2 * u + 1) := grid_two_gap 12
  have hcross : A * ((v - l) * (x - l)) < C * ((u - v) * (u - x)) := by
    calc
      _ = (A * ((1 - u) * (2 * u))) * u := by rw [hv, hx, hl]; ring
      _ < (A * ((1 - u) * (2 * u))) * 1 :=
        mul_lt_mul_of_pos_left hut (mul_pos hA (mul_pos (sub_pos.mpr hut) (by positivity)))
      _ = _ := by
        rw [hC, huv, hx]
        linear_combination -(A * ((1 - u) * (2 * u))) * hD
  have hp := mul_pos (sub_pos.mpr hvu) (sub_pos.mpr (hxv.trans hvu))
  have hm := mul_pos (sub_pos.mpr (hxl.trans hxv)) (sub_pos.mpr hxl)
  have hcompare : A / (u - v) + C / (v - l) < A / (u - x) + C / (x - l) := by
    apply sub_neg.mp
    rw [inverse_gap_difference hxl hxv hvu]
    exact mul_neg_of_pos_of_neg (sub_pos.mpr hxv) (sub_neg.mpr ((div_lt_div_iff₀ hp hm).mpr hcross))
  have hK : 0 < (1 - u) * (1 - l) / (u - l) :=
    div_pos (mul_pos (sub_pos.mpr hut) (sub_pos.mpr (hlu.trans hut))) (sub_pos.mpr hlu)
  have hreverse : middleSlope 12 v < middleSlope 12 x := by
    rw [middleSlope_eq (hxl.trans hxv) hvu hut, middleSlope_eq hxl (hxv.trans hvu) hut]
    exact add_lt_add_right (mul_lt_mul_of_pos_left hcompare hK) _
  let c := cyclicReadout 12
  let P := polynomial u l (count c u) (count c l)
  let B := slopeBound c u l
  let r := (1 - criticalThreshold c u l) / (1 - tailMoment u l)
  change P r (Real.cos (4 * Real.pi / (12 : ℝ))) < 0
  have hSx : middleSlope 12 x ≤ B :=
    Finset.le_sup' id (middleSlope_mem (⟨5, by decide⟩ : Fin 12) hxl (hxv.trans hvu))
  have hS : middleSlope 12 v < B := hreverse.trans_le hSx
  have h1 : 1 ≤ B := Finset.le_sup' id (by simp [certificateSlopes])
  have hB : 0 < B := zero_lt_one.trans_le h1
  obtain ⟨hac, ha, _, _⟩ := cyclic_high_threshold_certificate (by decide : 4 ≤ 12)
  have hr : r = 1 / B := cutoff_tail_mass c (hac.trans ha)
  have hfactor : 0 < 1 - r * middleSlope 12 v := by
    rw [hr, one_div, inv_mul_eq_div]
    exact sub_pos.mpr ((div_lt_one hB).mpr hS)
  have hPaff : P r v = P 0 v * (1 - r * middleSlope 12 v) :=
    polynomial_middle_affine hut (hxl.trans hxv) hvu
  rw [← (show v = Real.cos (4 * Real.pi / (12 : ℝ)) from grid_two_argument 12), hPaff]
  exact mul_neg_of_neg_of_pos (polynomial_zero_neg hut (hxl.trans hxv) hvu) hfactor

private theorem tailMoment_gap_factor {u l : ℝ} (hd : difference u - difference l ≠ 0) :
    1 - tailMoment u l =
      (1 - u) * (1 + (2 * u + 1) * (u - l) /
        ((1 - u) * (2 * u + 1) - (1 - l) * (2 * l + 1))) := by
  unfold tailMoment upperFraction
  rw [difference_factor u, difference_factor l] at hd ⊢
  generalize he : (1 - u) * (2 * u + 1) - (1 - l) * (2 * l + 1) = d at hd ⊢
  field_simp [hd]
  rw [← he]
  ring

/-- The deficit of the exact finite-grid threshold has sharp order q⁻²,
with coefficient 24π²/5. -/
theorem cyclic_criticalThreshold_limit :
    let scale := fun q : ℕ => (q : ℝ) ^ 2
    Tendsto (fun q : ℕ => scale q *
      (1 - criticalThreshold (cyclicReadout q) (cyclicUpper q) (cyclicLower q)))
      atTop (𝓝 (24 * Real.pi^2 / 5)) := by
  have hratio := tail_moment_ratio_limit cyclicUpper cyclicLower upper_limit lower_limit
  have hv : Tendsto (fun q : ℕ => (q : ℝ)^2 * (1 - cyclicUpper q))
      atTop (𝓝 (2 * Real.pi^2)) := cyclic_versine_limit
  have hlim := (hv.mul hratio).div middleSlope_two_limit (by norm_num)
  rw [show 2 * Real.pi ^ 2 * 4 / (5 / 3) = 24 * Real.pi ^ 2 / 5 by ring] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 13] with q hq
  obtain ⟨hu, hl⟩ := cyclic_difference_signs hq
  have hd : difference (cyclicUpper q) - difference (cyclicLower q) ≠ 0 := by linarith
  simp only [Pi.div_apply]
  rw [criticalThreshold, slope_maximum hq, sub_sub_cancel, tailMoment_gap_factor hd]
  ring
end D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit
