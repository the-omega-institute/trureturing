/- GID: D5/S3/Fourier/Asymptotics/HighCosineThresholdLimit
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/HighCosineThresholdLimit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First intermediate contact and sharp asymptotic limit for the cyclic two-cosine certificate. -/

import D5.S3.Fourier.Concentration.HighCosineThreshold
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

private theorem strict_inverse_gap_dominance {l x v u A C : ℝ}
    (hlx : l < x) (hxv : x < v) (hvu : v < u)
    (h : C * ((u - v) * (u - x)) < A * ((v - l) * (x - l))) :
    A / (u - x) + C / (x - l) < A / (u - v) + C / (v - l) := by
  have hp : 0 < (u - v) * (u - x) := mul_pos (sub_pos.mpr hvu) (sub_pos.mpr (hxv.trans hvu))
  have hm : 0 < (v - l) * (x - l) := mul_pos (sub_pos.mpr (hlx.trans hxv)) (sub_pos.mpr hlx)
  have hinv := (div_lt_div_iff₀ hm hp).mpr h
  have hmul := mul_lt_mul_of_pos_left hinv (sub_pos.mpr hxv)
  have hd :
      A / (u - v) + C / (v - l) - (A / (u - x) + C / (x - l)) =
      (v - x) * (A / ((u - v) * (u - x)) - C / ((v - l) * (x - l))) := by
    field_simp [hp.ne', hm.ne', sub_ne_zero.mpr hvu.ne',
      sub_ne_zero.mpr (hxv.trans hvu).ne', sub_ne_zero.mpr (hlx.trans hxv).ne',
      sub_ne_zero.mpr hlx.ne']
    ring
  linarith

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


private theorem cosine_edge_gap {t y : ℝ}
    (ht : 0 ≤ t) (hy : 0 ≤ y) (hmid : y + t / 2 ≤ Real.pi / 2) :
    1 - Real.cos t ≤ Real.cos y - Real.cos (y + t) := by
  have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ t / 2 by linarith [Real.pi_pos]) hmid (by linarith : t / 2 ≤ y + t / 2)
  have hsn : 0 ≤ Real.sin (t / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [Real.pi_pos])
  have hid : 1 - Real.cos t = 2 * Real.sin (t / 2) * Real.sin (t / 2) := by
    have h := Real.cos_sub_cos 0 t
    rw [Real.cos_zero, zero_add, zero_sub, neg_div, Real.sin_neg] at h
    linarith
  rw [hid, Real.cos_sub_cos]
  rw [show (y + (y + t)) / 2 = y + t / 2 by ring,
    show (y - (y + t)) / 2 = -(t / 2) by ring, Real.sin_neg]
  nlinarith only [mul_le_mul_of_nonneg_right hs hsn]

private theorem inverse_gap_criterion {l x v u A C : ℝ}
    (hlx : l < x) (hxv : x < v) (hvu : v < u) (hu : u < 1)
    (hA : 0 < A) (hC : 0 ≤ C) (hAC : 6 * C < A)
    (hgap : 1 - u ≤ x - l) (hspread : 1 ≤ v - l)
    (hupper : u - v ≤ 3 * (1 - u)) (hwidth : u - x ≤ 2) :
    A / (u - x) + C / (x - l) < A / (u - v) + C / (v - l) := by
  apply strict_inverse_gap_dominance hlx hxv hvu
  calc
    C * ((u - v) * (u - x)) ≤ C * (3 * (1 - u) * 2) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hupper hwidth (sub_nonneg.mpr (hxv.trans hvu).le) (by linarith)) hC
    _ = (6 * C) * (1 - u) := by ring
    _ < A * (1 - u) := mul_lt_mul_of_pos_right hAC (sub_pos.mpr hu)
    _ ≤ A * ((v - l) * (x - l)) := by
      apply mul_le_mul_of_nonneg_left _ hA.le
      calc
        1 - u ≤ x - l := hgap
        _ = 1 * (x - l) := (one_mul _).symm
        _ ≤ (v - l) * (x - l) := mul_le_mul_of_nonneg_right hspread (sub_nonneg.mpr hlx.le)

private theorem grid_bottom_gap {q n : ℕ} (hq : 6 ≤ q) (hn : n < q / 2) :
    1 - Real.cos (2 * Real.pi / (q : ℝ)) ≤
      Real.cos (2 * Real.pi * (n : ℝ) / q) -
      Real.cos (2 * Real.pi * ((q / 2 : ℕ) : ℝ) / q) := by
  let t : ℝ := 2 * Real.pi / q
  let y : ℝ := Real.pi - t * ((q / 2 : ℕ) : ℝ)
  have hq₀ : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have ht : 0 < t := div_pos (by positivity) hq₀
  have htq : t * (q : ℝ) = 2 * Real.pi := div_mul_cancel₀ _ hq₀.ne'
  have hhalf : (2 : ℝ) * ((q / 2 : ℕ) : ℝ) ≤ q := by
    exact_mod_cast (show 2 * (q / 2) ≤ q by omega)
  have hrem : (q : ℝ) ≤ 2 * ((q / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show q ≤ 2 * (q / 2) + 1 by omega)
  have hy₀ : 0 ≤ y := by
    dsimp only [y]
    nlinarith only [mul_le_mul_of_nonneg_left hhalf ht.le, htq]
  have hy₁ : y ≤ t / 2 := by
    dsimp only [y]
    nlinarith only [mul_le_mul_of_nonneg_left hrem ht.le, htq]
  have ht₁ : t ≤ Real.pi / 2 := by
    have h : (4 : ℝ) ≤ q := by exact_mod_cast (show 4 ≤ q by omega)
    nlinarith only [mul_le_mul_of_nonneg_left h ht.le, htq]
  have hfirst := cosine_edge_gap ht.le hy₀ (show y + t / 2 ≤ Real.pi / 2 by linarith)
  have hnR : (n : ℝ) + 1 ≤ ((q / 2 : ℕ) : ℝ) := by
    exact_mod_cast (show n + 1 ≤ q / 2 by omega)
  have ha₀ : 0 ≤ t * (n : ℝ) := mul_nonneg ht.le (Nat.cast_nonneg _)
  have ha₁ : t * (n : ℝ) ≤ Real.pi - (y + t) := by
    dsimp only [y]
    nlinarith only [mul_le_mul_of_nonneg_left hnR ht.le]
  have ha₂ : Real.pi - (y + t) ≤ Real.pi := by linarith
  have hsecond := Real.cos_le_cos_of_nonneg_of_le_pi ha₀ ha₂ ha₁
  rw [Real.cos_pi_sub] at hsecond
  have hycos : Real.cos (t * ((q / 2 : ℕ) : ℝ)) = -Real.cos y := by
    rw [← Real.cos_pi_sub]
    congr 1
    dsimp [y]
    ring
  rw [show 2 * Real.pi * (n : ℝ) / (q : ℝ) = t * n by unfold t; ring,
    show 2 * Real.pi * ((q / 2 : ℕ) : ℝ) / (q : ℝ) = t * ((q / 2 : ℕ) : ℝ) by
      unfold t
      ring]
  change 1 - Real.cos t ≤ Real.cos (t * (n : ℝ)) - Real.cos (t * ((q / 2 : ℕ) : ℝ))
  rw [hycos]
  linarith only [hfirst, hsecond]

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
  convert (htopTerm.const_add 1).add hbottomTerm using 2 <;> norm_num

private theorem tail_moment_ratio_limit (u l : ℕ → ℝ)
    (hu : Tendsto u atTop (𝓝 1)) (hl : Tendsto l atTop (𝓝 (-1))) :
    Tendsto (fun q => 1 + (2 * u q + 1) * (u q - l q) /
      ((1 - u q) * (2 * u q + 1) - (1 - l q) * (2 * l q + 1)))
      atTop (𝓝 4) := by
  have huu := (hu.const_mul 2).add_const 1
  have hll := (hl.const_mul 2).add_const 1
  have hnum := huu.mul (hu.sub hl)
  have hdenom := ((hu.const_sub 1).mul huu).sub ((hl.const_sub 1).mul hll)
  convert (hnum.div hdenom (by norm_num)).const_add 1 using 2 <;> norm_num

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
