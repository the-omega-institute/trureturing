/- GID: D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/HighCosineThresholdLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First intermediate contact and sharp asymptotic limit for the cyclic two-cosine certificate. -/

import D5.S3.Fourier.Concentration.HighCosineThreshold
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
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

private theorem cyclic_versine_limit :
    Tendsto (fun q : ℕ => (q : ℝ)^2 * (1 - Real.cos (2 * Real.pi / q)))
      atTop (𝓝 (2 * Real.pi ^ 2)) := by
  let t (q : ℕ) : ℝ := Real.pi / q
  have hreal : Tendsto (fun q : ℕ => (q : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto t atTop (𝓝 0) := by
    simpa only [t, div_eq_mul_inv, mul_zero] using hreal.const_mul Real.pi
  have hne : ∀ᶠ q : ℕ in atTop, q ≠ 0 :=
    (eventually_ge_atTop 1).mono fun q hq => Nat.ne_of_gt hq
  have ht' : Tendsto t atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t ht
      (hne.mono fun q hq => by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
          (div_ne_zero Real.pi_ne_zero (Nat.cast_ne_zero.mpr hq) : t q ≠ 0))
  have hs := ((Real.tendsto_sin_div_nhdsNE_zero.comp ht').pow 2).const_mul (2 * Real.pi ^ 2)
  simp only [one_pow, mul_one] at hs
  apply hs.congr'
  filter_upwards [hne] with q hq
  have hqr : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have htr : t q ≠ 0 := div_ne_zero Real.pi_ne_zero hqr
  have hqt : (q : ℝ) * t q = Real.pi := by
    rw [mul_comm, div_mul_cancel₀ _ hqr]
  rw [show 2 * Real.pi / (q : ℝ) = 2 * t q by unfold t; ring]
  have hcos : Real.cos (2 * t q) = 1 - 2 * Real.sin (t q)^2 := by
    rw [Real.cos_two_mul']
    nlinarith [Real.sin_sq_add_cos_sq (t q)]
  rw [hcos, show (q : ℝ) ^ 2 * (1 - (1 - 2 * Real.sin (t q)^2)) =
    2 * ((q : ℝ) * t q) ^ 2 * (Real.sin (t q) / t q) ^ 2 by
      field_simp [htr]
      ring, hqt]
  rfl


private theorem threshold_slope_limit (u l topWeight bottomWeight : ℕ → ℝ)
    (hu : Tendsto u atTop (𝓝 1)) (hl : Tendsto l atTop (𝓝 (-1)))
    (htop : Tendsto topWeight atTop (𝓝 (1 / 2)))
    (hbottom : Tendsto bottomWeight atTop (𝓝 0)) :
    Tendsto (fun q => 1 +
      topWeight q * (1 - l q) * (2 * (1 + u q)) / ((u q - l q) * (2 * u q + 1)) +
      bottomWeight q * (1 - u q) * (1 - (2 * (u q)^2 - 1)) /
        ((u q - l q) * (2 * (u q)^2 - 1 - l q)))
      atTop (𝓝 (5 / 3)) := by
  have hspread := hu.sub hl
  have htopNumer := (htop.mul (hl.const_sub 1)).mul ((hu.const_add 1).const_mul 2)
  have htopDenom := hspread.mul ((hu.const_mul 2).add_const 1)
  have htopTerm := htopNumer.div htopDenom (by norm_num)
  have hdouble := ((hu.pow 2).const_mul 2).sub_const 1
  have hbotNumer := (hbottom.mul (hu.const_sub 1)).mul (hdouble.const_sub 1)
  have hbotDenom := hspread.mul (hdouble.sub hl)
  have hbottomTerm := hbotNumer.div hbotDenom (by norm_num)
  convert (htopTerm.const_add 1).add hbottomTerm using 2; norm_num

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

private theorem middle_slope_decomposition {l x u A C : ℝ}
    (hlx : l < x) (hxu : x < u) (hu : u < 1) :
    let P₀ := (1 / ((1 - u) * (1 - l))) * (x - u) * (x - l)
    let P₁ := (A / ((u - 1) * (u - l))) * (x - 1) * (x - l) +
      (C / ((l - 1) * (l - u))) * (x - 1) * (x - u)
    1 - P₁ / P₀ =
      (1 + (A * (1 - l) - C * (1 - u)) / (u - l)) +
      ((1 - u) * (1 - l) / (u - l)) * (A / (u - x) + C / (x - l)) := by
  dsimp only
  have hlu := hlx.trans hxu
  have hl := hlu.trans hu
  field_simp [sub_ne_zero.mpr hu.ne, sub_ne_zero.mpr hu.ne',
    sub_ne_zero.mpr hl.ne, sub_ne_zero.mpr hl.ne',
    sub_ne_zero.mpr hlu.ne, sub_ne_zero.mpr hlu.ne',
    sub_ne_zero.mpr hlx.ne', sub_ne_zero.mpr hxu.ne, sub_ne_zero.mpr hxu.ne']
  ring

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
  have hbu : up * (1 - u) = -(A / (u - l)) := by
    dsimp [up]
    field_simp [sub_ne_zero.mpr hu.ne, sub_ne_zero.mpr hlu.ne']
    ring
  have hbl : low * (1 - l) = C / (u - l) := by
    dsimp [low]
    field_simp [sub_ne_zero.mpr hl.ne, sub_ne_zero.mpr hlu.ne,
      sub_ne_zero.mpr hlu.ne']
    ring
  change 1 - -(up * (1 + l) + low * (1 + u)) / -(top * (u + l)) ≤
      1 - ((up + low) / 2) / (top / 2) ∧ _
  constructor
  · apply sub_le_sub_left
    have hbeta : 0 < -(top * (u + l)) := neg_pos.mpr (mul_neg_of_pos_of_neg ht hs)
    apply (div_le_div_iff₀ (half_pos ht) hbeta).2
    have hnormal : -(up * (1 + l) + low * (1 + u)) =
        -(u + l) * (up + low) + (A - C) / (u - l) := by
      rw [sub_div]
      linear_combination -hbu - hbl
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

private theorem grid_lower (q : ℕ) : grid q (q / 2) = cyclicLower q := rfl

private theorem grid_half_angle {q : ℕ} (hq : 0 < q) :
    Real.pi - Real.pi / q ≤ 2 * Real.pi * ((q / 2 : ℕ) : ℝ) / q ∧
      2 * Real.pi * ((q / 2 : ℕ) : ℝ) / q ≤ Real.pi := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hh : 2 * ((q / 2 : ℕ) : ℝ) ≤ q := by
    exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
  have hr : (q : ℝ) ≤ 2 * ((q / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show q ≤ 2 * (q / 2) + 1 by omega)
  constructor
  · apply (le_div_iff₀ hq').mpr
    rw [sub_mul, div_mul_cancel₀ _ hq'.ne']
    nlinarith only [mul_le_mul_of_nonneg_left hr Real.pi_pos.le]
  · apply (div_le_iff₀ hq').mpr
    nlinarith only [mul_le_mul_of_nonneg_left hh Real.pi_pos.le]

private theorem grid_reflect {q n k : ℕ} (hq : 0 < q) (h : 2 * n + k = q) :
    grid q n = -Real.cos (Real.pi * k / q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h' : 2 * (n : ℝ) + k = q := by exact_mod_cast h
  rw [grid, ← Real.cos_pi_sub]
  congr 1
  apply (div_eq_iff hq'.ne').mpr
  rw [sub_mul, div_mul_cancel₀ _ hq'.ne']
  linear_combination Real.pi * h'

private theorem cyclic_lower_even {q : ℕ} (hq : 0 < q) (he : q % 2 = 0) :
    cyclicLower q = -1 := by
  rw [← grid_lower, grid_reflect (k := 0) hq (by omega)]
  simp

private theorem cyclic_lower_odd {q : ℕ} (hq : 0 < q) (ho : q % 2 = 1) :
    cyclicLower q = -Real.cos (Real.pi / q) := by
  rw [← grid_lower, grid_reflect (k := 1) hq (by omega)]
  simp

private theorem grid_bottom_even {q n : ℕ} (hq : 4 ≤ q) (he : q % 2 = 0) (hn : n < q / 2) :
    -cyclicUpper q ≤ grid q n := by
  have h := grid_reflect (n := q / 2 - 1) (k := 2) (by omega : 0 < q) (by omega)
  rw [show Real.pi * ((2 : ℕ) : ℝ) / q = 2 * Real.pi / q by push_cast; ring,
    ← cyclicUpper] at h
  rw [← h]
  rcases lt_or_eq_of_le (show n ≤ q / 2 - 1 by omega) with hn' | rfl
  · exact (grid_strict hn' (by omega)).le
  · exact le_rfl

private theorem grid_bottom_odd {q n : ℕ} (hq : 4 ≤ q) (ho : q % 2 = 1) (hn : n < q / 2) :
    2 * Real.cos (Real.pi / q) * (1 - cyclicUpper q) ≤ grid q n - cyclicLower q := by
  let s : ℝ := Real.pi / q
  have h := grid_reflect (n := q / 2 - 1) (k := 3) (by omega : 0 < q) (by omega)
  rw [show Real.pi * ((3 : ℕ) : ℝ) / q = 3 * s by unfold s; push_cast; ring] at h
  have hcos : Real.cos (3 * s) + Real.cos s = 2 * Real.cos (2 * s) * Real.cos s := by
    rw [show 3 * s = 2 * s + s by ring, Real.cos_add]
    conv_lhs =>
      arg 2
      rw [show s = 2 * s - s by ring, Real.cos_sub]
    ring
  have hu : cyclicUpper q = Real.cos (2 * s) := by
    unfold cyclicUpper s
    ring_nf
  have hstep : 2 * Real.cos s * (1 - cyclicUpper q) =
      grid q (q / 2 - 1) - cyclicLower q := by
    rw [h, cyclic_lower_odd (by omega : 0 < q) ho, hu]
    change 2 * Real.cos s * (1 - Real.cos (2 * s)) = -Real.cos (3 * s) - -Real.cos s
    linear_combination hcos
  rw [hstep]
  apply sub_le_sub_right
  rcases lt_or_eq_of_le (show n ≤ q / 2 - 1 by omega) with hn' | rfl
  · exact (grid_strict hn' (by omega)).le
  · exact le_rfl

private theorem cyclic_versine_bound {q : ℕ} (hq : 0 < q) {k : ℝ} (hk : k ≠ 0) :
    1 - Real.cos (k * Real.pi / q) < (k ^ 2 * 5) / (q : ℝ)^2 := by
  have hpi : Real.pi ^ 2 < 10 := by
    have h := pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by decide : 2 ≠ 0)
    exact h.trans (by norm_num)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hangle : k * Real.pi / q ≠ 0 := div_ne_zero (mul_ne_zero hk Real.pi_ne_zero) hq'.ne'
  have hcos := Real.one_sub_sq_div_two_lt_cos hangle
  calc
    _ < (k * Real.pi / q)^2 / 2 := by linarith only [hcos]
    _ = k ^ 2 * (Real.pi ^ 2 / 2) / (q : ℝ)^2 := by rw [div_pow, mul_pow]; ring
    _ < _ := div_lt_div_of_pos_right
      (mul_lt_mul_of_pos_left (by linarith only [hpi]) (sq_pos_of_ne_zero hk)) (sq_pos_of_pos hq')

private theorem cyclic_upper_gt {q m : ℕ} (hm : 0 < m) (hq : m ≤ q) :
    1 - 20 / (m : ℝ)^2 < cyclicUpper q := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmq : (m : ℝ) ≤ q := by exact_mod_cast hq
  have hb : 20 / (q : ℝ)^2 ≤ 20 / (m : ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hm')
      (pow_le_pow_left₀ hm'.le hmq 2)
  have h := cyclic_versine_bound (hm.trans_le hq) (k := 2) (by norm_num)
  norm_num at h
  change 1 - cyclicUpper q < _ at h
  linarith only [h, hb]

private theorem cyclic_half_cos_gt {q : ℕ} (hq : 13 ≤ q) : 97 / 100 < Real.cos (Real.pi / q) := by
  have hq' : (13 : ℝ) ≤ q := by exact_mod_cast hq
  have hb : 5 / (q : ℝ)^2 ≤ 5 / (13 : ℝ)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num) hq' 2)
  have h := cyclic_versine_bound (by omega : 0 < q) (k := 1) (by norm_num)
  simp only [one_mul, one_pow] at h
  linarith only [h, hb]

private theorem cyclic_upper_lt_one {q : ℕ} (hq : 4 ≤ q) : cyclicUpper q < 1 := by
  have h := grid_strict (q := q) (n := 0) (m := 1) (by decide) (by omega)
  simpa [grid, cyclicUpper] using h

private theorem upper_add_lower_neg {q : ℕ} (hq : 4 ≤ q) :
    cyclicUpper q + cyclicLower q < 0 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq4 : (4 : ℝ) ≤ q := by exact_mod_cast hq
  have hstep : 0 < Real.pi / q := by positivity
  have hpos : 0 ≤ Real.pi - 2 * Real.pi / q := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hq').mpr
    nlinarith only [mul_le_mul_of_nonneg_left hq4 Real.pi_pos.le, Real.pi_pos]
  obtain ⟨hl, hu⟩ := grid_half_angle (show 0 < q by omega)
  have hg : Real.pi - 2 * Real.pi / q <
      2 * Real.pi * ((q / 2 : ℕ) : ℝ) / q := by
    calc
      _ < Real.pi - Real.pi / q := by rw [mul_div_assoc]; linarith
      _ ≤ _ := hl
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi hpos hu hg
  rw [Real.cos_pi_sub, ← cyclicLower, ← cyclicUpper] at h
  linarith

private theorem cyclic_upper_count {q : ℕ} (hq : 4 ≤ q) :
    count (cyclicReadout q) (cyclicUpper q) = 2 := by
  classical
  let a : Fin q := ⟨1, by omega⟩
  let b : Fin q := ⟨q - 1, by omega⟩
  have hab : a ≠ b := by
    intro h
    have he := congrArg Fin.val h
    dsimp [a, b] at he
    omega
  have htop : cyclicUpper q < 1 := by
    have h := grid_strict (q := q) (n := 0) (m := 1) (by decide) (by omega)
    simpa [grid, cyclicUpper] using h
  have hfold (k : Fin q) (hk : k.val ≠ 0) (he : cyclicReadout q k = cyclicUpper q) :
      k = a ∨ k = b := by
    obtain ⟨n, hn, hnh, hread, hindex⟩ := cyclic_fold k hk
    change cyclicReadout q k = grid q n at hread
    have hn1 : n = 1 := by
      by_contra hne
      have h := grid_strict (q := q) (n := 1) (m := n) (by omega) hnh
      rw [grid_one, ← hread, he] at h
      exact (lt_irrefl _) h
    rcases hindex with h | h
    · exact Or.inl (Fin.ext (by dsimp [a]; omega))
    · exact Or.inr (Fin.ext (by dsimp [b]; have := k.isLt; omega))
  have hreadA : cyclicReadout q a = cyclicUpper q := by simp [cyclicReadout, a, cyclicUpper]
  have hreadB : cyclicReadout q b = cyclicUpper q := by
    obtain ⟨n, hn, hnh, hre, hi⟩ := cyclic_fold b (by dsimp [b]; omega)
    have hn1 : n = 1 := by
      dsimp [b] at hi
      omega
    simpa [hn1, cyclicUpper] using hre
  have hset : univ.filter (fun k : Fin q => cyclicReadout q k = cyclicUpper q) = {a,b} := by
    ext k
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro he
      have hk : k.val ≠ 0 := by
        intro hz
        have h : cyclicReadout q k = 1 := by simp [cyclicReadout, hz]
        rw [he] at h
        exact htop.ne h
      exact hfold k hk he
    · rintro (rfl | rfl)
      · exact hreadA
      · exact hreadB
  unfold count
  rw [hset, Finset.card_pair hab]
  norm_num

private theorem cyclic_lower_count_ge_one {q : ℕ} (hq : 4 ≤ q) :
    1 ≤ count (cyclicReadout q) (cyclicLower q) := by
  classical
  unfold count
  have h : 0 < (univ.filter (fun k : Fin q => cyclicReadout q k = cyclicLower q)).card :=
    Finset.card_pos.mpr ⟨⟨q / 2, by omega⟩, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  exact_mod_cast (show 1 ≤ _ from h)

private theorem cyclic_lower_count_even {q : ℕ} (hq : 4 ≤ q) (he : q % 2 = 0) :
    count (cyclicReadout q) (cyclicLower q) = 1 := by
  classical
  let b : Fin q := ⟨q / 2, by omega⟩
  have hset : univ.filter (fun i : Fin q => cyclicReadout q i = cyclicLower q) = {b} := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hi
      have hi₀ : i.val ≠ 0 := by
        intro h
        rw [cyclicReadout, h, Nat.cast_zero, mul_zero, zero_div, Real.cos_zero,
          cyclic_lower_even (by omega : 0 < q) he] at hi
        norm_num at hi
      obtain ⟨n, _, hn, hr, hi'⟩ := cyclic_fold i hi₀
      change cyclicReadout q i = grid q n at hr
      have hn' : n = q / 2 := by
        by_contra hne
        have h := grid_strict (show n < q / 2 by omega) (Nat.le_refl (q / 2))
        rw [grid_lower, ← hr, hi] at h
        exact lt_irrefl _ h
      apply Fin.ext
      have hib := i.isLt
      dsimp [b]
      rcases hi' with h | h <;> omega
    · rintro rfl
      rfl
  rw [count, hset, card_singleton, Nat.cast_one]

private theorem inv_nat_limit : Tendsto (fun q : ℕ => (q : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private theorem upper_limit : Tendsto cyclicUpper atTop (𝓝 1) := by
  have h := inv_nat_limit.const_mul (2 * Real.pi)
  simp only [mul_zero] at h
  change Tendsto (fun q : ℕ => Real.cos (2 * Real.pi / q)) atTop (𝓝 1)
  simpa [div_eq_mul_inv, Real.cos_zero, Function.comp_def] using
    (Real.continuous_cos.continuousAt (x := 0)).tendsto.comp h

private theorem lower_limit : Tendsto cyclicLower atTop (𝓝 (-1)) := by
  have hlow : Tendsto (fun q : ℕ => Real.pi - Real.pi / q) atTop (𝓝 Real.pi) := by
    simpa [div_eq_mul_inv] using (inv_nat_limit.const_mul Real.pi).const_sub Real.pi
  have ha : Tendsto (fun q : ℕ => 2 * Real.pi * ((q/2 : ℕ) : ℝ) / q)
      atTop (𝓝 Real.pi) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 1] with q hq
      exact (grid_half_angle (by omega)).1
    · filter_upwards [eventually_ge_atTop 1] with q hq
      exact (grid_half_angle (by omega)).2
  change Tendsto (fun q : ℕ => Real.cos (2 * Real.pi * ((q/2 : ℕ) : ℝ) / q)) atTop (𝓝 (-1))
  simpa [Real.cos_pi, Function.comp_def] using
    (Real.continuous_cos.continuousAt (x := Real.pi)).tendsto.comp ha

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

private theorem cyclic_difference_signs {q : ℕ} (hq : 13 ≤ q) :
    0 < difference (cyclicUpper q) ∧ difference (cyclicLower q) < 0 := by
  have hu := cyclic_upper_gt (by decide : 0 < 13) hq
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
  have hA : 0 < upperWeight q := by
    rw [upperWeight, cyclic_upper_count (by omega : 4 ≤ q)]
    exact div_pos (fraction_bounds hdu hdl).1 (by norm_num)
  rw [lowerWeight_eq (by omega) hdu hdl, mul_comm (upperWeight q)]
  apply mul_lt_mul_of_pos_right _ hA
  apply (div_lt_iff₀ (mul_pos (zero_lt_one.trans_le hM) (neg_pos.mpr hdl))).mpr
  have hden : -difference l ≤ M * -difference l :=
    le_mul_of_one_le_left (neg_nonneg.mpr hdl.le) hM
  change 2 * difference u < _ * (M * -difference l)
  by_cases he : q % 2 = 0
  · rw [ite_eq_left he]
    have hu : (8 / 9 : ℝ) < u := by
      have h := cyclic_upper_gt (by decide : 0 < 14) (show 14 ≤ q by omega)
      norm_num at h
      linarith only [h]
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
    have hu : (22 / 25 : ℝ) < u := by
      have h := cyclic_upper_gt (by decide : 0 < 13) hq
      norm_num at h
      linarith only [h]
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
  simpa [middleSlope, Concentration.HighCosineThreshold.slope, polynomial, topCoeff, upperCoeff, lowerCoeff,
    upperWeight, lowerWeight] using middle_slope_decomposition hl hu hut
      (A := upperWeight q) (C := lowerWeight q)

private theorem middleSlope_two_eq {q : ℕ} (hq : 6 ≤ q)
    (hut : cyclicUpper q < 1) :
    let u := cyclicUpper q
    let l := cyclicLower q
    let A := upperWeight q
    let C := lowerWeight q
    middleSlope q (grid q 2) =
      1 + A * (1 - l) * (2 * (1 + u)) / ((u - l) * (2 * u + 1)) +
        C * (1 - u) * (1 - (2 * u^2 - 1)) / ((u - l) * (2 * u^2 - 1 - l)) := by
  obtain ⟨hl, hu⟩ := grid_two_between hq
  rw [middleSlope_eq hl hu hut]
  let u := cyclicUpper q
  let l := cyclicLower q
  let A := upperWeight q
  let C := lowerWeight q
  have hspread : l < u := hl.trans hu
  have hdouble : grid q 2 = 2 * u^2 - 1 := grid_two q
  have hh : u - grid q 2 = (1 - u) * (2 * u + 1) := by rw [hdouble]; ring
  have hpos : 0 < 2 * u + 1 :=
    (mul_pos_iff_of_pos_left (sub_pos.mpr hut)).mp (hh ▸ sub_pos.mpr hu)
  change (1 + (A * (1 - l) - C * (1 - u)) / (u - l)) +
    ((1 - u) * (1 - l) / (u - l)) * (A / (u - grid q 2) + C / (grid q 2 - l)) =
    1 + A * (1 - l) * (2 * (1 + u)) / ((u - l) * (2 * u + 1)) +
      C * (1 - u) * (1 - (2 * u^2 - 1)) / ((u - l) * (2 * u^2 - 1 - l))
  rw [hh, hdouble]
  have hb : 2 * u^2 - 1 - l ≠ 0 := by rw [← hdouble]; exact sub_ne_zero.mpr hl.ne'
  have hs : u - l ≠ 0 := sub_ne_zero.mpr hspread.ne'
  have ht : 1 - u ≠ 0 := sub_ne_zero.mpr hut.ne'
  have hpos' : 2 * u + 1 ≠ 0 := hpos.ne'
  clear_value u l A C
  have hpos'' : u * 2 + 1 ≠ 0 := by rwa [mul_comm u 2]
  have hb' : u^2 * 2 - 1 - l ≠ 0 := by rwa [mul_comm (u^2) 2]
  field_simp [hs, ht, hpos', hb, hpos'', hb']
  ring

private theorem middleSlope_two_limit :
    Tendsto (fun q => middleSlope q (grid q 2)) atTop (𝓝 (5 / 3)) := by
  apply (threshold_slope_limit cyclicUpper cyclicLower upperWeight lowerWeight
    upper_limit lower_limit upper_weight_limit lower_weight_limit).congr'
  filter_upwards [eventually_ge_atTop 6] with q hq
  exact (middleSlope_two_eq hq (cyclic_upper_lt_one (by omega))).symm

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
  have huv_eq : u - v = (1 - u) * (2 * u + 1) := by rw [hv]; ring
  have hA : 0 < A := by
    unfold A upperWeight
    rw [cyclic_upper_count (by omega : 4 ≤ q)]
    exact div_pos (cyclic_fraction_bounds hq).1 (by norm_num)
  have hw := cyclic_weight_bound hq
  change C < _ at hw
  by_cases he : q % 2 = 0
  · rw [ite_eq_left he] at hw
    have hl : l = -1 := cyclic_lower_even (by omega) he
    have hu : (8 / 9 : ℝ) < u := by
      have h := cyclic_upper_gt (by decide : 0 < 14) (show 14 ≤ q by omega)
      norm_num at h
      linarith only [h]
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
    have hu : (22 / 25 : ℝ) < u := by
      have h := cyclic_upper_gt (by decide : 0 < 13) hq
      norm_num at h
      linarith only [h]
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
    let nu := count c u
    let nl := count c l
    let β := firstMultiplier u l nu nl
    let γ := secondMultiplier u l nu nl
    6 ≤ q ∧ u < 1 ∧ u + l < 0 ∧ l < v ∧ v < u ∧
      1 < middleSlope q v ∧
      Concentration.HighCosineThreshold.slope (β 0) (β 1) < middleSlope q v ∧
      Concentration.HighCosineThreshold.slope (γ 0) (γ 1) < middleSlope q v ∧
      (∀ i, l < c i → c i < u → c i ≠ v → middleSlope q (c i) < middleSlope q v) := by
  dsimp only
  have hq : 6 ≤ q := by omega
  have hut := cyclic_upper_lt_one (by omega : 4 ≤ q)
  have hp := cyclic_fraction_bounds hq13
  let c := cyclicReadout q
  let u := cyclicUpper q
  let l := cyclicLower q
  let v := grid q 2
  let A := upperWeight q
  let C := lowerWeight q
  have hA : 0 < A := by
    unfold A upperWeight
    rw [cyclic_upper_count (by omega)]
    exact div_pos hp.1 (by norm_num)
  have hC : 0 ≤ C := div_nonneg (sub_nonneg.mpr hp.2.le)
    ((cyclic_lower_count_ge_one (by omega : 4 ≤ q)).trans' zero_le_one)
  have hs := upper_add_lower_neg (by omega : 4 ≤ q)
  obtain ⟨hlv, hvu⟩ := grid_two_between hq
  have hlu := hlv.trans hvu
  have hlt := hlu.trans hut
  have hK : 0 < (1 - u) * (1 - l) / (u - l) :=
    div_pos (mul_pos (sub_pos.mpr hut) (sub_pos.mpr hlt)) (sub_pos.mpr hlu)
  have hw := cyclic_weight_bound hq13
  have hC_A : C ≤ A := by
    change C < _ at hw
    split at hw <;> linarith only [hA, hw]
  have hS : 1 < middleSlope q v := by
    rw [middleSlope_two_eq hq hut, ← grid_two q]
    change 1 < 1 + A * (1 - l) * (2 * (1 + u)) / ((u - l) * (2 * u + 1)) +
      C * (1 - u) * (1 - v) / ((u - l) * (v - l))
    have hu := cyclic_upper_gt (by decide : 0 < 13) hq13
    have hu₁ : 0 < 1 + u := by dsimp [u]; linarith only [hu]
    have hu₂ : 0 < 2 * u + 1 := by dsimp [u]; linarith only [hu]
    have htop := div_pos (mul_pos (mul_pos hA (sub_pos.mpr hlt)) (mul_pos (by norm_num : (0 : ℝ) < 2) hu₁))
      (mul_pos (sub_pos.mpr hlu) hu₂)
    have hbottom := div_nonneg
      (mul_nonneg (mul_nonneg hC (sub_nonneg.mpr hut.le)) (sub_nonneg.mpr (hvu.trans hut).le))
      (mul_nonneg (sub_nonneg.mpr hlu.le) (sub_nonneg.mpr hlv.le))
    linarith only [htop, hbottom]
  obtain ⟨hβγ, hγ⟩ := multiplier_slope_order hlu hut hs hC_A
  have hβγ' :
      Concentration.HighCosineThreshold.slope (firstMultiplier u l (count c u) (count c l) 0)
        (firstMultiplier u l (count c u) (count c l) 1) ≤
      Concentration.HighCosineThreshold.slope (secondMultiplier u l (count c u) (count c l) 0)
        (secondMultiplier u l (count c u) (count c l) 1) := by
    simpa [Concentration.HighCosineThreshold.slope, firstMultiplier, secondMultiplier, topCoeff, upperCoeff, lowerCoeff,
      A, C, upperWeight, lowerWeight, c, u, l] using hβγ
  have hγ' :
      Concentration.HighCosineThreshold.slope (secondMultiplier u l (count c u) (count c l) 0)
        (secondMultiplier u l (count c u) (count c l) 1) =
      1 + (A * (1 - l) - C * (1 - u)) / (u - l) := by
    simpa [Concentration.HighCosineThreshold.slope, secondMultiplier, topCoeff, upperCoeff, lowerCoeff,
      A, C, upperWeight, lowerWeight, c, u, l] using hγ
  have hγS : Concentration.HighCosineThreshold.slope (secondMultiplier u l (count c u) (count c l) 0)
      (secondMultiplier u l (count c u) (count c l) 1) < middleSlope q v := by
    rw [hγ', middleSlope_eq hlv hvu hut]
    exact lt_add_of_pos_right _ (mul_pos hK
      (add_pos_of_pos_of_nonneg (div_pos hA (sub_pos.mpr hvu))
        (div_nonneg hC (sub_nonneg.mpr hlv.le))))
  refine ⟨hq, hut, hs, hlv, hvu, hS, hβγ'.trans_lt hγS, hγS, ?_⟩
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
private theorem exact_slope_maximum {q : ℕ} (hq : 6 ≤ q)
    (hvl : cyclicLower q < grid q 2) (hvu : grid q 2 < cyclicUpper q)
    (hS : 1 < middleSlope q (grid q 2))
    (hβ : Concentration.HighCosineThreshold.slope
        (firstMultiplier (cyclicUpper q) (cyclicLower q)
          (count (cyclicReadout q) (cyclicUpper q)) (count (cyclicReadout q) (cyclicLower q)) 0)
        (firstMultiplier (cyclicUpper q) (cyclicLower q)
          (count (cyclicReadout q) (cyclicUpper q)) (count (cyclicReadout q) (cyclicLower q)) 1)
      < middleSlope q (grid q 2))
    (hγ : Concentration.HighCosineThreshold.slope
        (secondMultiplier (cyclicUpper q) (cyclicLower q)
          (count (cyclicReadout q) (cyclicUpper q)) (count (cyclicReadout q) (cyclicLower q)) 0)
        (secondMultiplier (cyclicUpper q) (cyclicLower q)
          (count (cyclicReadout q) (cyclicUpper q)) (count (cyclicReadout q) (cyclicLower q)) 1)
      < middleSlope q (grid q 2))
    (hm : ∀ i, cyclicLower q < cyclicReadout q i → cyclicReadout q i < cyclicUpper q →
      cyclicReadout q i ≠ grid q 2 → middleSlope q (cyclicReadout q i) < middleSlope q (grid q 2)) :
    slopeBound (cyclicReadout q) (cyclicUpper q) (cyclicLower q) = middleSlope q (grid q 2) := by
  classical
  let c := cyclicReadout q
  let u := cyclicUpper q
  let l := cyclicLower q
  let v := grid q 2
  let i : Fin q := ⟨2, by omega⟩
  have hi : c i = v := rfl
  have hmem : middleSlope q v ∈ certificateSlopes c u l := by
    rw [← hi]
    apply middleSlope_mem i
    · change l < c i
      rw [hi]
      exact hvl
    · change c i < u
      rw [hi]
      exact hvu
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

private theorem slope_maximum {q : ℕ} (hq : 13 ≤ q) :
    slopeBound (cyclicReadout q) (cyclicUpper q) (cyclicLower q) =
      middleSlope q (grid q 2) := by
  obtain ⟨hq', _, _, hl, hu, hS, hβ, hγ, hm⟩ := strict_slope_dominance hq
  exact exact_slope_maximum hq' hl hu hS hβ hγ hm

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
  let c := cyclicReadout q
  let u := cyclicUpper q
  let l := cyclicLower q
  let v := Real.cos (4 * Real.pi / q)
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
  have hdom := strict_slope_dominance hq13
  have hmax := slope_maximum hq13
  have hp := cyclic_fraction_bounds hq13
  dsimp only at hdom ⊢
  obtain ⟨hq, hut, hs, hlv, hvu, hS, hβ, hγ, hm⟩ := hdom
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
  have hv : v = Real.cos (4 * Real.pi / q) := by
    unfold v grid
    push_cast
    congr 1
    ring
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
      constructor
      · rcases lt_or_eq_of_le hnh with h | h
        · exact (grid_strict h le_rfl).le
        · rw [h]
      · rcases lt_or_eq_of_le hn with h | h
        · exact (grid_strict h hnh).le
        · rw [← h]
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

private theorem slope_twelve_reverse :
    middleSlope 12 (grid 12 2) < middleSlope 12 (grid 12 5) := by
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
  have hu₀ : 0 < u := by
    have hangle : 2 * Real.pi / (12 : ℝ) = Real.pi / 6 := by ring
    simp [u, cyclicUpper, hangle, Real.cos_pi_div_six]
  have hu₂ : u ^ 2 = 3 / 4 := by
    change Real.cos (2 * Real.pi / (12 : ℝ)) ^ 2 = _
    rw [show 2 * Real.pi / (12 : ℝ) = Real.pi / 6 by ring, Real.sq_cos_pi_div_six]
  have hv : v = 2 * u^2 - 1 := grid_two 12
  have hdu : 0 < difference u := by
    rw [difference_factor]
    exact mul_pos (sub_pos.mpr hut) (by linarith only [hu₀])
  have hdl : difference l = -2 := by rw [hl]; norm_num [difference, second]
  have hdl₀ : difference l < 0 := by rw [hdl]; norm_num
  have hA : 0 < A := by
    unfold A upperWeight
    rw [cyclic_upper_count (by decide : 4 ≤ 12)]
    exact div_pos (fraction_bounds hdu hdl₀).1 (by norm_num)
  have hC : C = A * difference u := by
    unfold C
    rw [lowerWeight_eq (by decide) hdu hdl₀, cyclic_lower_count_even (by decide) (by decide), hdl]
    change A * (2 * difference u / (1 * -(-2))) = A * difference u
    ring
  have hD : difference u * (2 * u + 1) = 1 := by
    rw [difference_factor]
    linear_combination -4 * u * hu₂
  have huv : u - v = (1 - u) * (2 * u + 1) := by rw [hv]; ring
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
  rw [middleSlope_eq (hxl.trans hxv) hvu hut, middleSlope_eq hxl (hxv.trans hvu) hut]
  exact add_lt_add_right (mul_lt_mul_of_pos_left hcompare hK) _

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
  let c := cyclicReadout 12
  let u := cyclicUpper 12
  let l := cyclicLower 12
  let v := grid 12 2
  let P := polynomial u l (count c u) (count c l)
  let i : Fin 12 := ⟨5, by decide⟩
  let B := slopeBound c u l
  let r := (1 - criticalThreshold c u l) / (1 - tailMoment u l)
  have hl : l < c i := grid_strict (by decide : 5 < 12 / 2) le_rfl
  have hvx : c i < v := grid_strict (by decide : 2 < 5) (by decide : 5 ≤ 12 / 2)
  obtain ⟨hlv, hvu⟩ := grid_two_between (by decide : 6 ≤ 12)
  have hSx : middleSlope 12 (c i) ≤ B := Finset.le_sup' id (middleSlope_mem i hl (hvx.trans hvu))
  have hS : middleSlope 12 v < B := slope_twelve_reverse.trans_le hSx
  have h1 : 1 ≤ B := Finset.le_sup' id (by simp [certificateSlopes])
  have hB : 0 < B := zero_lt_one.trans_le h1
  obtain ⟨hac, ha, _, _⟩ := cyclic_high_threshold_certificate (by decide : 4 ≤ 12)
  have hr : r = 1 / B := cutoff_tail_mass c (hac.trans ha)
  have hfactor : 0 < 1 - r * middleSlope 12 v := by
    rw [hr, one_div, inv_mul_eq_div]
    exact sub_pos.mpr ((div_lt_one hB).mpr hS)
  have hv : v = Real.cos (4 * Real.pi / (12 : ℝ)) := by
    unfold v grid
    push_cast
    congr 1
    ring
  change P r (Real.cos (4 * Real.pi / (12 : ℝ))) < 0
  have hu := cyclic_upper_lt_one (by decide : 4 ≤ 12)
  have hPaff : P r v = P 0 v * (1 - r * middleSlope 12 v) :=
    polynomial_middle_affine hu hlv hvu
  rw [← hv, hPaff]
  exact mul_neg_of_neg_of_pos (polynomial_zero_neg hu hlv hvu) hfactor

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
  have hlim' : Tendsto (fun q : ℕ =>
      ((q : ℝ)^2 * (1 - cyclicUpper q)) *
        (1 + (2 * cyclicUpper q + 1) * (cyclicUpper q - cyclicLower q) /
          ((1 - cyclicUpper q) * (2 * cyclicUpper q + 1) -
            (1 - cyclicLower q) * (2 * cyclicLower q + 1))) /
        middleSlope q (grid q 2)) atTop (𝓝 (24 * Real.pi^2 / 5)) := by
    convert hlim using 1
    congr 1
    ring
  apply hlim'.congr'
  have hdiff := (upper_limit.sub (((upper_limit.pow 2).const_mul 2).sub_const 1)).sub
    (lower_limit.sub (((lower_limit.pow 2).const_mul 2).sub_const 1))
  have hpos : ∀ᶠ q in atTop, 0 < difference (cyclicUpper q) - difference (cyclicLower q) := by
    have h := tendsto_const_nhds.eventually_lt hdiff (show (0 : ℝ) < (1 - (2 * 1^2 - 1)) -
      (-1 - (2 * (-1)^2 - 1)) by norm_num)
    simpa [difference, second] using h
  filter_upwards [eventually_ge_atTop 13, hpos] with q hq hd
  rw [criticalThreshold, slope_maximum hq, sub_sub_cancel, tailMoment_gap_factor hd.ne']
  ring

end D5.S3.Fourier.Asymptotics.HighCosineThresholdLimit
