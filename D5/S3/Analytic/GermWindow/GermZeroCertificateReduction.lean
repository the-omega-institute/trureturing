/- GID: D5/S3/Analytic/GermWindow/GermZeroCertificateReduction
   generality: I
   mirror-B: D5/B/S3/Analytic/GermWindow/GermZeroCertificateReduction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Reduce a prime-two golden local-factor zero to three finite center-jet bounds. -/

import D5.S3.Analytic.EulerGerm.LocalFactorZeroDivisor
import D5.S3.Weil.ZetaAnalytic.RoucheZeroCount

/- Library-search audit trail (2026-09-05):
   * Exact D5 searches found no target declaration, no explicit prime-two
     geometric tail estimate, and no center-jet-to-local-zero reduction.
   * The frozen rectangle theorem
     `rectangle_zero_count_eq_of_norm_sub_lt` supplies the zero-count
     preservation step; this module wraps it only to extract existence from a
     unique simple comparison zero.
   * Pinned Mathlib has no rectangle Rouche theorem or matching ball-zero
     criterion. It supplies `Summable.sum_add_tsum_nat_add`,
     `tsum_geometric_of_lt_one`,
     `AnalyticAt.analyticOrderAt_eq_one_of_zero_deriv_ne_zero`, and
     `Convex.norm_image_sub_le_of_norm_deriv_le`, all used below.
   * Exact-name and literal-body searches for every definition introduced
     below found no duplicate carrier on origin/dev. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Complex Metric Set
open D5.S3.Analytic.GoldenEulerBeta
open D5.S3.Analytic.EulerGerm.GoldenLocalFactor
open D5.S3.Analytic.EulerGerm.LocalFactorZeroDivisor
open D5.S3.Weil.ZetaAnalytic.RoucheZeroCount

noncomputable section

namespace D5.S3.Analytic.GermWindow.GermZeroCertificateReduction

def c : ℂ :=
  ⟨23815329946211908 / 10^17, 5256712292901926 / 10^15⟩

def h : ℝ := 1 / (2 * 10^8)

def Q : Set ℂ := Rectangle (c - h - h * I) (c + h + h * I)

def g (V : ℕ) (s : ℂ) : ℂ :=
  ∑ v ∈ Finset.range (V + 1),
    (2 : ℂ) ^ (-s * (o5Beta v : ℂ))

private theorem Q_apply :
    Q = Icc (c.re - h) (c.re + h) ×ℂ Icc (c.im - h) (c.im + h) := by
  rw [Q, Rectangle]
  norm_num [h]
  have hh : 0 < h := by norm_num [h]
  rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]

theorem Q_subset_ball : Q ⊆ Metric.ball c (1 / 10^8) := by
  intro s hs
  rw [Q_apply] at hs
  rcases hs with ⟨⟨hsrelo, hsrehi⟩, hsimlo, hsimhi⟩
  rw [mem_ball, dist_eq]
  have hrelo : -h ≤ (s - c).re := by simpa using sub_le_sub_right hsrelo c.re
  have hrehi : (s - c).re ≤ h := by simpa using sub_le_sub_right hsrehi c.re
  have himlo : -h ≤ (s - c).im := by simpa using sub_le_sub_right hsimlo c.im
  have himhi : (s - c).im ≤ h := by simpa using sub_le_sub_right hsimhi c.im
  have hre_sum : 0 ≤ h + (s - c).re := by linarith
  have him_sum : 0 ≤ h + (s - c).im := by linarith
  have hre_prod := mul_nonneg (sub_nonneg.mpr hrehi) hre_sum
  have him_prod := mul_nonneg (sub_nonneg.mpr himhi) him_sum
  have hre_sq : (s - c).re ^ 2 ≤ h ^ 2 := by nlinarith
  have him_sq : (s - c).im ^ 2 ≤ h ^ 2 := by nlinarith
  have hnormsq : ‖s - c‖ ^ 2 ≤ 2 * h ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith
  have hstrict : 2 * h ^ 2 < (1 / 10^8 : ℝ) ^ 2 := by norm_num [h]
  nlinarith [norm_nonneg (s - c)]

theorem Q_subset_re_pos : Q ⊆ {s : ℂ | 0 < s.re} := by
  intro s hs
  rw [Q_apply] at hs
  change 0 < s.re
  rcases hs with ⟨⟨hsrelo, _⟩, _⟩
  have hc : (1 / 5 : ℝ) < c.re := by norm_num [c]
  have hh : h < (1 / 5 : ℝ) := by norm_num [h]
  linarith

theorem c_in_golden_window :
    1 / (2 * Real.goldenRatio ^ 3) < c.re ∧
      c.re < 1 / Real.goldenRatio ^ 2 := by
  have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hphi_lo : (8 / 5 : ℝ) < Real.goldenRatio := by
    rw [Real.goldenRatio]
    nlinarith
  have hphi_hi : Real.goldenRatio < (5 / 3 : ℝ) := by
    rw [Real.goldenRatio]
    nlinarith
  have hphi_pos : 0 < Real.goldenRatio := Real.goldenRatio_pos
  constructor
  · rw [div_lt_iff₀ (by positivity : 0 < 2 * Real.goldenRatio ^ 3)]
    have hc : (1 / 5 : ℝ) < c.re := by norm_num [c]
    have hcube_eq : Real.goldenRatio ^ 3 = 2 * Real.goldenRatio + 1 := by
      nlinarith [Real.goldenRatio_sq]
    have hcube : (4 : ℝ) < Real.goldenRatio ^ 3 := by nlinarith
    nlinarith
  · rw [lt_div_iff₀ (by positivity : 0 < Real.goldenRatio ^ 2)]
    have hc : c.re < (1 / 4 : ℝ) := by norm_num [c]
    have hsq : Real.goldenRatio ^ 2 < (3 : ℝ) := by nlinarith
    nlinarith

theorem c_mem_Q : c ∈ Q := by
  rw [Q_apply]
  constructor <;> constructor <;> norm_num [h]

private theorem beta_nonneg (v : ℕ) : 0 ≤ o5Beta v := by
  cases v with
  | zero => simp [o5_beta_zero]
  | succ v =>
      have hg := o5_beta_growth (v + 1)
      have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
      have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
      have hinv_pos : 0 < 1 / Real.goldenRatio := by positivity
      push_cast at hg ⊢
      nlinarith

private theorem local_term_norm (s : ℂ) (v : ℕ) :
    ‖(2 : ℂ) ^ (-s * (o5Beta v : ℂ))‖ =
      (2 : ℝ) ^ (-s.re * o5Beta v) := by
  change ‖((2 : ℕ) : ℂ) ^ (-s * (o5Beta v : ℂ))‖ = _
  rw [Complex.norm_natCast_cpow_of_pos (by norm_num)]
  simp

private theorem local_terms_summable (s : ℂ) (hs : 0 < s.re) :
    Summable (fun v : ℕ => (2 : ℂ) ^ (-s * (o5Beta v : ℂ))) := by
  let q : ℝ := (2 : ℝ) ^ (-s.re)
  have hq_nonneg : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq_lt : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable (fun v : ℕ => q ^ v) :=
    summable_geometric_of_lt_one hq_nonneg hq_lt
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun v => norm_nonneg _)
      (fun v => ?_) hgeom
  rw [local_term_norm]
  have hexp : -s.re * o5Beta v ≤ -s.re * (v : ℝ) := by
    nlinarith [beta_nonneg v, show (v : ℝ) ≤ o5Beta v from by
      cases v with
      | zero => simp [o5_beta_zero]
      | succ v =>
          have hg := o5_beta_growth (v + 1)
          have hsqrt_sq : Real.sqrt 5 ^ 2 = (5 : ℝ) :=
            Real.sq_sqrt (by norm_num)
          have hsqrt_nonneg : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
          have hsqrt_two : 2 < Real.sqrt 5 := by nlinarith
          have hinv_pos : 0 < 1 / Real.goldenRatio := by positivity
          push_cast at hg ⊢
          nlinarith]
  calc
    (2 : ℝ) ^ (-s.re * o5Beta v) ≤ (2 : ℝ) ^ (-s.re * (v : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = q ^ v := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

theorem germLocalFactor_eq_trunc_add_tail (s : ℂ) (hs : 0 < s.re) (N : ℕ) :
    germLocalFactor s 2 =
      (∑ v ∈ Finset.range N, (2 : ℂ) ^ (-s * (o5Beta v : ℂ))) +
        ∑' k : ℕ, (2 : ℂ) ^ (-s * (o5Beta (k + N) : ℂ)) := by
  rw [germLocalFactor]
  change (∑' v : ℕ, (2 : ℂ) ^ (-s * (o5Beta v : ℂ))) = _
  exact ((local_terms_summable s hs).sum_add_tsum_nat_add N).symm

private theorem local_term_norm_le_growth {sigma : ℝ} (hsigma : 0 < sigma)
    {s : ℂ} (hs : sigma ≤ s.re) (v : ℕ) :
    ‖(2 : ℂ) ^ (-s * (o5Beta v : ℂ))‖ ≤
      (2 : ℝ) ^
        (-sigma * (Real.sqrt 5 * (v : ℝ) + 1 / Real.goldenRatio - 1)) := by
  rw [local_term_norm]
  have hbeta := beta_nonneg v
  have hgrowth := o5_beta_growth v
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith

theorem germLocalFactor_two_tail_le {σ : ℝ} (hσ : 0 < σ)
    {s : ℂ} (hs : σ ≤ s.re) (V : ℕ) :
    ‖germLocalFactor s 2 -
        ∑ v ∈ Finset.range (V + 1),
          (2 : ℂ) ^ (-s * (o5Beta v : ℂ))‖ ≤
      (2 : ℝ) ^
          (-σ *
            (Real.sqrt 5 * ((V + 1 : ℕ) : ℝ) +
              1 / Real.goldenRatio - 1)) /
        (1 - (2 : ℝ) ^ (-σ * Real.sqrt 5)) := by
  change ‖germLocalFactor s 2 - g V s‖ ≤ _
  let N : ℕ := V + 1
  let A : ℝ := (2 : ℝ) ^
    (-σ * (Real.sqrt 5 * (N : ℝ) + 1 / Real.goldenRatio - 1))
  let q : ℝ := (2 : ℝ) ^ (-σ * Real.sqrt 5)
  have hsqrt_pos : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hq_nonneg : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq_lt : q < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by
      nlinarith)
  have hgeom : Summable (fun k : ℕ => A * q ^ k) :=
    (summable_geometric_of_lt_one hq_nonneg hq_lt).mul_left A
  have hmajorant : ∀ k : ℕ,
      ‖(2 : ℂ) ^ (-s * (o5Beta (k + N) : ℂ))‖ ≤ A * q ^ k := by
    intro k
    calc
      ‖(2 : ℂ) ^ (-s * (o5Beta (k + N) : ℂ))‖ ≤
          (2 : ℝ) ^ (-σ *
            (Real.sqrt 5 * ((k + N : ℕ) : ℝ) +
              1 / Real.goldenRatio - 1)) :=
        local_term_norm_le_growth hσ hs (k + N)
      _ = A * q ^ k := by
        dsimp [A, q]
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
        congr 1
        push_cast
        ring
  have hnormtail : Summable (fun k : ℕ =>
      ‖(2 : ℂ) ^ (-s * (o5Beta (k + N) : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hmajorant hgeom
  have htail : Summable (fun k : ℕ =>
      (2 : ℂ) ^ (-s * (o5Beta (k + N) : ℂ))) := hnormtail.of_norm
  have hpos : 0 < s.re := lt_of_lt_of_le hσ hs
  have hidentity : germLocalFactor s 2 - g V s =
      ∑' k : ℕ, (2 : ℂ) ^ (-s * (o5Beta (k + N) : ℂ)) := by
    rw [g, germLocalFactor_eq_trunc_add_tail s hpos N]
    dsimp [N]
    ring
  rw [hidentity]
  calc
    ‖∑' k : ℕ, (2 : ℂ) ^ (-s * (o5Beta (k + N) : ℂ))‖ ≤
        ∑' k : ℕ, ‖(2 : ℂ) ^ (-s * (o5Beta (k + N) : ℂ))‖ :=
      norm_tsum_le_tsum_norm hnormtail
    _ ≤ ∑' k : ℕ, A * q ^ k :=
      hnormtail.tsum_le_tsum hmajorant hgeom
    _ = A / (1 - q) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hq_nonneg hq_lt,
        div_eq_mul_inv]
    _ = (2 : ℝ) ^
          (-σ *
            (Real.sqrt 5 * ((V + 1 : ℕ) : ℝ) +
              1 / Real.goldenRatio - 1)) /
        (1 - (2 : ℝ) ^ (-σ * Real.sqrt 5)) := by
      rfl

private theorem exp_neg_36911_lt_69139 :
    Real.exp (-(36911 / 100000 : ℝ)) < 69139 / 100000 := by
  rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
  have hsum := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 36911 / 100000 by norm_num) 5
  calc
    (69139 / 100000 : ℝ)⁻¹ <
        (∑ k ∈ Finset.range 5,
          (36911 / 100000 : ℝ) ^ k / k.factorial) := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    _ ≤ Real.exp (36911 / 100000) := hsum

private theorem exp_0065_lt_107 :
    Real.exp (13 / 200 : ℝ) < 107 / 100 := by
  have hbound := Real.exp_bound'
    (show (0 : ℝ) ≤ 13 / 200 by norm_num)
    (show (13 / 200 : ℝ) ≤ 1 by norm_num)
    (show (0 : ℕ) < 5 by norm_num)
  calc
    Real.exp (13 / 200 : ℝ) ≤
        (∑ m ∈ Finset.range 5,
          (13 / 200 : ℝ) ^ m / m.factorial) +
          (13 / 200 : ℝ) ^ 5 * (5 + 1) /
            ((5 : ℕ).factorial * 5) := hbound
    _ < 107 / 100 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]

theorem germLocalFactor_two_tail_Q_V60 :
    ∀ s ∈ Q, ‖germLocalFactor s 2 - g 60 s‖ < 58 / 10^11 := by
  intro s hsQ
  let sigma : ℝ := c.re - h
  have hsigma_pos : 0 < sigma := by norm_num [sigma, c, h]
  have hsigma_le : sigma ≤ s.re := by
    rw [Q_apply] at hsQ
    exact hsQ.1.1
  refine (germLocalFactor_two_tail_le hsigma_pos hsigma_le 60).trans_lt ?_
  let q : ℝ := (2 : ℝ) ^ (-sigma * Real.sqrt 5)
  let B : ℝ := (2 : ℝ) ^
    (sigma * (1 - 1 / Real.goldenRatio))
  have hsqrt_lo : (2236067977 / 1000000000 : ℝ) < Real.sqrt 5 :=
    (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have hsigma_lo : (238153294 / 1000000000 : ℝ) < sigma := by
    norm_num [sigma, c, h]
  have hsigma_hi : sigma < (238154 / 1000000 : ℝ) := by
    norm_num [sigma, c, h]
  have hsigmasqrt :
      (238153294 / 1000000000 : ℝ) *
          (2236067977 / 1000000000) < sigma * Real.sqrt 5 := by
    calc
      (238153294 / 1000000000 : ℝ) * (2236067977 / 1000000000) <
          sigma * (2236067977 / 1000000000) := by
        exact mul_lt_mul_of_pos_right hsigma_lo (by norm_num)
      _ < sigma * Real.sqrt 5 :=
        mul_lt_mul_of_pos_left hsqrt_lo hsigma_pos
  have hlogprod :
      ((238153294 / 1000000000 : ℝ) *
          (2236067977 / 1000000000)) * (6931471803 / 10000000000) <
        (sigma * Real.sqrt 5) * Real.log 2 := by
    have hloglo : (6931471803 / 10000000000 : ℝ) < Real.log 2 := by
      convert Real.log_two_gt_d9 using 1
      all_goals norm_num
    calc
      ((238153294 / 1000000000 : ℝ) *
          (2236067977 / 1000000000)) * (6931471803 / 10000000000) <
          (sigma * Real.sqrt 5) * (6931471803 / 10000000000) := by
        exact mul_lt_mul_of_pos_right hsigmasqrt (by norm_num)
      _ < (sigma * Real.sqrt 5) * Real.log 2 := by
        exact mul_lt_mul_of_pos_left hloglo
          (mul_pos hsigma_pos (Real.sqrt_pos.2 (by norm_num)))
  have ht_lo : (36911 / 100000 : ℝ) <
      sigma * Real.sqrt 5 * Real.log 2 := by
    exact lt_trans (by norm_num) hlogprod
  have hq : q < (69139 / 100000 : ℝ) := by
    dsimp [q]
    rw [Real.rpow_def_of_pos (by norm_num)]
    rw [show Real.log 2 * (-sigma * Real.sqrt 5) =
      -(sigma * Real.sqrt 5 * Real.log 2) by ring]
    exact (Real.exp_strictMono (by nlinarith)).trans exp_neg_36911_lt_69139
  have hcoeff_pos : 0 < 1 - 1 / Real.goldenRatio := by
    rw [one_div, Real.inv_goldenRatio, Real.goldenConj]
    have hsqrt_lt : Real.sqrt 5 < 3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), Real.sqrt_nonneg 5]
    nlinarith
  have hcoeff_hi : 1 - 1 / Real.goldenRatio < (382 / 1000 : ℝ) := by
    rw [one_div, Real.inv_goldenRatio, Real.goldenConj]
    nlinarith
  have hlog_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hexponent_hi :
      Real.log 2 * (sigma * (1 - 1 / Real.goldenRatio)) < 13 / 200 := by
    have hloghi : Real.log 2 < (6931471808 / 10000000000 : ℝ) := by
      convert Real.log_two_lt_d9 using 1
      all_goals norm_num
    have hsigcoeff :
        sigma * (1 - 1 / Real.goldenRatio) <
          (238154 / 1000000 : ℝ) * (382 / 1000) := by
      calc
        sigma * (1 - 1 / Real.goldenRatio) <
            (238154 / 1000000 : ℝ) * (1 - 1 / Real.goldenRatio) :=
          mul_lt_mul_of_pos_right hsigma_hi hcoeff_pos
        _ < (238154 / 1000000 : ℝ) * (382 / 1000) :=
          mul_lt_mul_of_pos_left hcoeff_hi (by norm_num)
    calc
      Real.log 2 * (sigma * (1 - 1 / Real.goldenRatio)) <
          (6931471808 / 10000000000 : ℝ) *
            (sigma * (1 - 1 / Real.goldenRatio)) := by
        exact mul_lt_mul_of_pos_right hloghi
          (mul_pos hsigma_pos hcoeff_pos)
      _ < (6931471808 / 10000000000 : ℝ) *
          ((238154 / 1000000) * (382 / 1000)) := by
        exact mul_lt_mul_of_pos_left hsigcoeff (by norm_num)
      _ < 13 / 200 := by norm_num
  have hB : B < (107 / 100 : ℝ) := by
    dsimp [B]
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact (Real.exp_strictMono hexponent_hi).trans exp_0065_lt_107
  have hA :
      (2 : ℝ) ^
          (-sigma *
            (Real.sqrt 5 * (((60 + 1 : ℕ) : ℝ)) +
              1 / Real.goldenRatio - 1)) = q ^ 61 * B := by
    dsimp [q, B]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_add (by norm_num)]
    congr 1
    norm_num
    ring
  rw [hA]
  have hq_nonneg : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hB_nonneg : 0 ≤ B := Real.rpow_nonneg (by norm_num) _
  have hqpow : q ^ 61 ≤ (69139 / 100000 : ℝ) ^ 61 := by
    gcongr
  have hnum : q ^ 61 * B <
      (69139 / 100000 : ℝ) ^ 61 * (107 / 100) := by
    calc
      q ^ 61 * B ≤ (69139 / 100000 : ℝ) ^ 61 * B := by
        exact mul_le_mul_of_nonneg_right hqpow hB_nonneg
      _ < (69139 / 100000 : ℝ) ^ 61 * (107 / 100) := by
        exact mul_lt_mul_of_pos_left hB (pow_pos (by norm_num) 61)
  have hden_pos : 0 < 1 - q := sub_pos.mpr (hq.trans (by norm_num))
  rw [div_lt_iff₀ hden_pos]
  calc
    q ^ 61 * B < (69139 / 100000 : ℝ) ^ 61 * (107 / 100) := hnum
    _ < (58 / 10^11 : ℝ) * (1 - 69139 / 100000) := by norm_num
    _ < (58 / 10^11 : ℝ) * (1 - q) := by
      gcongr

theorem rouche_exists_zero_rectangle_of_unique_simple
    {f a : ℂ → ℂ} {z w r : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    (ha : AnalyticOnNhd ℂ a (Rectangle z w))
    (hbdry : ∀ s ∈ RectangleBorder z w, ‖f s - a s‖ < ‖a s‖)
    (hr : r ∈ Rectangle z w)
    (hzero : ∀ s ∈ Rectangle z w, (a s = 0 ↔ s = r))
    (hsimple : analyticOrderNatAt a r = 1) :
    ∃ s ∈ Rectangle z w, f s = 0 := by
  have hzborder : z ∈ RectangleBorder z w :=
    Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))
  have haz : a z ≠ 0 := by
    intro haz
    have := hbdry z hzborder
    rw [haz, norm_zero] at this
    exact (not_lt_of_ge (norm_nonneg _)) this
  have hfz : f z ≠ 0 := by
    intro hfz
    have hlt := hbdry z hzborder
    rw [hfz, zero_sub, norm_neg] at hlt
    exact (lt_irrefl _ hlt)
  let Zf : Finset ℂ :=
    (Zeta23.Analytic.finite_zeros_rectangle hf
      (rectangleBorder_subset_rectangle z w hzborder) hfz).toFinset
  let Za : Finset ℂ := {r}
  have hZf : ∀ s ∈ Rectangle z w, (f s = 0 ↔ s ∈ Zf) := by
    intro s hs
    simp [Zf, hs]
  have hZfsub : (Zf : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    have hs' : s ∈ Rectangle z w ∧ f s = 0 := by
      simpa [Zf] using hs
    exact hs'.1
  have hZa : ∀ s ∈ Rectangle z w, (a s = 0 ↔ s ∈ Za) := by
    intro s hs
    simpa [Za] using hzero s hs
  have hZasub : (Za : Set ℂ) ⊆ Rectangle z w := by
    intro s hs
    have hsr : s = r := by simpa [Za] using hs
    simpa [hsr] using hr
  have hcount := rectangle_zero_count_eq_of_norm_sub_lt
    hre him hf ha hbdry Zf Za hZf hZfsub hZa hZasub
  have hsum : ∑ rho ∈ Zf, analyticOrderNatAt f rho = 1 := by
    simpa [Za, hsimple] using hcount
  have hne : Zf.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty] at hsum
    simp at hsum
  obtain ⟨s, hs⟩ := hne
  exact ⟨s, hZfsub hs, (hZf s (hZfsub hs)).mpr hs⟩

private theorem Q_border_norm_sub_center_ge {s : ℂ}
    (hs : s ∈ RectangleBorder (c - h - h * I) (c + h + h * I)) :
    h ≤ ‖s - c‖ := by
  simp only [RectangleBorder, mem_union, mem_reProdIm, mem_uIcc,
    mem_singleton_iff, sub_re, ofReal_re, add_re, mul_re, ofReal_im,
    I_re, mul_one, sub_zero, add_zero, sub_im, I_im, mul_zero,
    add_im] at hs
  obtain hs123 | hs4 := hs
  · obtain hs12 | hs3 := hs123
    · obtain hs1 | hs2 := hs12
      · have heq : (s - c).im = -h := by
          simp only [sub_im]
          rw [hs1.2]
          simp
        calc
          h = |(s - c).im| := by rw [heq, abs_neg, abs_of_nonneg]; norm_num [h]
          _ ≤ ‖s - c‖ := Complex.abs_im_le_norm _
      · have heq : (s - c).re = -h := by
          simp only [sub_re]
          rw [hs2.1]
          simp
        calc
          h = |(s - c).re| := by rw [heq, abs_neg, abs_of_nonneg]; norm_num [h]
          _ ≤ ‖s - c‖ := Complex.abs_re_le_norm _
    · have heq : (s - c).im = h := by
        simp only [sub_im]
        rw [hs3.2]
        simp
      calc
        h = |(s - c).im| := by rw [heq, abs_of_nonneg]; norm_num [h]
        _ ≤ ‖s - c‖ := Complex.abs_im_le_norm _
  · have heq : (s - c).re = h := by
      simp only [sub_re]
      rw [hs4.1]
      simp
    calc
      h = |(s - c).re| := by rw [heq, abs_of_nonneg]; norm_num [h]
      _ ≤ ‖s - c‖ := Complex.abs_re_le_norm _

private def affineJet (s : ℂ) : ℂ :=
  g 60 c + deriv (g 60) c * (s - c)

private def affineRoot : ℂ :=
  c - g 60 c / deriv (g 60) c

private theorem g_analytic (V : ℕ) (s : ℂ) : AnalyticAt ℂ (g V) s := by
  unfold g
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  exact Filter.Eventually.of_forall fun x => DifferentiableAt.fun_sum fun v hv =>
    (differentiableAt_id.neg.mul_const (o5Beta v : ℂ)).const_cpow
      (.inl (by norm_num : (2 : ℂ) ≠ 0))

theorem truncation_taylor_remainder_of_curv
    (hcurv : ∀ s ∈ Q, ‖deriv (deriv (g 60)) s‖ ≤ 400) :
    ∀ s ∈ Q,
      ‖g 60 s - (g 60 c + deriv (g 60) c * (s - c))‖ ≤
        4 / 10 ^ 14 := by
  change ∀ s ∈ Q, ‖g 60 s - affineJet s‖ ≤ 4 / 10 ^ 14
  intro s hs
  have hconvex : Convex ℝ Q := by
    rw [Q, rectangle_eq_convexHull]
    exact convex_convexHull ℝ _
  have hcQ : c ∈ Q := c_mem_Q
  have hderiv_diff : ∀ x ∈ Q,
      ‖deriv (g 60) x - deriv (g 60) c‖ ≤
        400 * ‖x - c‖ := by
    intro x hx
    exact hconvex.norm_image_sub_le_of_norm_deriv_le
      (fun y _ => (g_analytic 60 y).deriv.differentiableAt)
      hcurv hcQ hx
  have hderiv_uniform : ∀ x ∈ Q,
      ‖deriv (g 60) x - deriv (g 60) c‖ ≤ 1 / 250000 := by
    intro x hx
    have hxball := Q_subset_ball hx
    rw [mem_ball, dist_eq] at hxball
    calc
      ‖deriv (g 60) x - deriv (g 60) c‖ ≤ 400 * ‖x - c‖ :=
        hderiv_diff x hx
      _ ≤ 400 * (1 / 10^8 : ℝ) := by gcongr
      _ = 1 / 250000 := by norm_num
  let R : ℂ → ℂ := fun x =>
    g 60 x - g 60 c - deriv (g 60) c * (x - c)
  have hRdiff : ∀ x ∈ Q, DifferentiableAt ℂ R x := by
    intro x hx
    dsimp [R]
    exact ((g_analytic 60 x).differentiableAt.sub_const _).sub (by fun_prop)
  have hRderiv : ∀ x ∈ Q,
      deriv R x = deriv (g 60) x - deriv (g 60) c := by
    intro x hx
    have hgdiff : DifferentiableAt ℂ (g 60) x :=
      (g_analytic 60 x).differentiableAt
    have hfirst : HasDerivAt (fun y : ℂ => g 60 y - g 60 c)
        (deriv (g 60) x) x := hgdiff.hasDerivAt.sub_const _
    have hlin : HasDerivAt
        (fun y : ℂ => deriv (g 60) c * (y - c))
        (deriv (g 60) c) x := by
      simpa using ((hasDerivAt_id x).sub_const c).const_mul (deriv (g 60) c)
    exact (hfirst.sub hlin).deriv
  have hRbound : ∀ x ∈ Q, ‖deriv R x‖ ≤ 1 / 250000 := by
    intro x hx
    rw [hRderiv x hx]
    exact hderiv_uniform x hx
  have hmean := hconvex.norm_image_sub_le_of_norm_deriv_le
    hRdiff hRbound hcQ hs
  have hRc : R c = 0 := by simp [R]
  have hRs : R s = g 60 s - affineJet s := by
    simp only [R, affineJet]
    ring
  rw [hRs, hRc, sub_zero] at hmean
  have hsball := Q_subset_ball hs
  rw [mem_ball, dist_eq] at hsball
  calc
    ‖g 60 s - affineJet s‖ ≤ (1 / 250000 : ℝ) * ‖s - c‖ := hmean
    _ ≤ (1 / 250000 : ℝ) * (1 / 10^8) := by
      gcongr
    _ = 4 / 10^14 := by norm_num

theorem germ_zero_of_center_jet
    (hval : ‖g 60 c‖ < 4 / 10 ^ 10)
    (hder : 187 / 100 < (deriv (g 60) c).re)
    (hcurv : ∀ s ∈ Q, ‖deriv (deriv (g 60)) s‖ ≤ 400) :
    ∃ z ∈ Metric.ball c (1 / 10^8), germLocalFactor z 2 = 0 := by
  let d : ℂ := deriv (g 60) c
  have hd_norm : (187 / 100 : ℝ) < ‖d‖ := by
    apply hder.trans_le
    exact (le_abs_self d.re).trans (Complex.abs_re_le_norm d)
  have hd : d ≠ 0 := by
    exact norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 187 / 100).trans hd_norm)
  have hdisp : ‖g 60 c / d‖ < h := by
    rw [norm_div, div_lt_iff₀ (norm_pos_iff.mpr hd)]
    calc
      ‖g 60 c‖ < 4 / 10^10 := hval
      _ < h * (187 / 100 : ℝ) := by norm_num [h]
      _ < h * ‖d‖ := mul_lt_mul_of_pos_left hd_norm (by norm_num [h])
  have hrootQ : affineRoot ∈ Q := by
    have hre : |(g 60 c / d).re| < h :=
      (Complex.abs_re_le_norm _).trans_lt hdisp
    have him : |(g 60 c / d).im| < h :=
      (Complex.abs_im_le_norm _).trans_lt hdisp
    rw [Q_apply]
    have hddef : d = deriv (g 60) c := rfl
    rw [affineRoot, ← hddef]
    rcases abs_lt.mp hre with ⟨hrelo, hrehi⟩
    rcases abs_lt.mp him with ⟨himlo, himhi⟩
    constructor
    · constructor
      · change c.re - h ≤ c.re - (g 60 c / d).re
        linarith
      · change c.re - (g 60 c / d).re ≤ c.re + h
        linarith
    · constructor
      · change c.im - h ≤ c.im - (g 60 c / d).im
        linarith
      · change c.im - (g 60 c / d).im ≤ c.im + h
        linarith
  have ha : AnalyticOnNhd ℂ affineJet Q := by
    intro s hs
    unfold affineJet
    fun_prop
  have hzero : ∀ s ∈ Q, (affineJet s = 0 ↔ s = affineRoot) := by
    intro s hs
    constructor
    · intro hA
      have hmul : d * (s - c) = -(g 60 c) := by
        unfold affineJet at hA
        linear_combination hA
      have hsc : s - c = -(g 60 c) / d := by
        apply (eq_div_iff hd).2
        rw [mul_comm]
        exact hmul
      rw [affineRoot]
      calc
        s = c + (s - c) := by ring
        _ = c - g 60 c / deriv (g 60) c := by rw [hsc]; ring
    · intro hsr
      rw [hsr]
      unfold affineJet affineRoot
      have hd' : deriv (g 60) c ≠ 0 := by simpa [d] using hd
      field_simp [hd']
      all_goals ring
  have hrootzero : affineJet affineRoot = 0 :=
    (hzero affineRoot hrootQ).2 rfl
  have haderiv : deriv affineJet affineRoot = d := by
    have hlin : HasDerivAt
        (fun s : ℂ => deriv (g 60) c * (s - c))
        (deriv (g 60) c) affineRoot := by
      simpa using ((hasDerivAt_id affineRoot).sub_const c).const_mul
        (deriv (g 60) c)
    have hjet := hlin.const_add (g 60 c)
    change deriv
        (fun s : ℂ => g 60 c + deriv (g 60) c * (s - c)) affineRoot =
      deriv (g 60) c
    exact hjet.deriv
  have hsimple : analyticOrderNatAt affineJet affineRoot = 1 := by
    have hord := (ha affineRoot hrootQ).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
      hrootzero (by simpa [haderiv] using hd)
    rw [analyticOrderNatAt, hord]
    rfl
  have ha_lower : ∀ s ∈ RectangleBorder (c - h - h * I) (c + h + h * I),
      (895 / 10^11 : ℝ) < ‖affineJet s‖ := by
    intro s hs
    have hsc := Q_border_norm_sub_center_ge hs
    have hlinear : (187 / 100 : ℝ) * h < ‖d * (s - c)‖ := by
      rw [norm_mul]
      calc
        (187 / 100 : ℝ) * h < ‖d‖ * h :=
          mul_lt_mul_of_pos_right hd_norm (by norm_num [h])
        _ ≤ ‖d‖ * ‖s - c‖ := by gcongr
    have hreverse : ‖d * (s - c)‖ - ‖g 60 c‖ ≤ ‖affineJet s‖ := by
      simpa [affineJet, d, sub_neg, add_comm] using
        (norm_sub_norm_le (d * (s - c)) (-(g 60 c)))
    calc
      (895 / 10^11 : ℝ) = (187 / 100 : ℝ) * h - 4 / 10^10 := by
        norm_num [h]
      _ < ‖d * (s - c)‖ - ‖g 60 c‖ := sub_lt_sub hlinear hval
      _ ≤ ‖affineJet s‖ := hreverse
  have hrem := truncation_taylor_remainder_of_curv hcurv
  have hbdry : ∀ s ∈ RectangleBorder (c - h - h * I) (c + h + h * I),
      ‖germLocalFactor s 2 - affineJet s‖ < ‖affineJet s‖ := by
    intro s hs
    have hsQ : s ∈ Q := by
      rw [Q]
      exact rectangleBorder_subset_rectangle _ _ hs
    have htail := germLocalFactor_two_tail_Q_V60 s hsQ
    have hremainder : ‖g 60 s - affineJet s‖ ≤ 4 / 10 ^ 14 := by
      simpa [affineJet] using hrem s hsQ
    have htriangle :
        ‖germLocalFactor s 2 - affineJet s‖ ≤
          ‖germLocalFactor s 2 - g 60 s‖ + ‖g 60 s - affineJet s‖ := by
      calc
        ‖germLocalFactor s 2 - affineJet s‖ =
            ‖(germLocalFactor s 2 - g 60 s) +
              (g 60 s - affineJet s)‖ := by congr 1; ring
        _ ≤ ‖germLocalFactor s 2 - g 60 s‖ +
            ‖g 60 s - affineJet s‖ := norm_add_le _ _
    exact lt_of_le_of_lt htriangle (lt_trans (by nlinarith) (ha_lower s hs))
  have hh : (0 : ℝ) < h := by norm_num [h]
  have hre : (c - h - h * I).re < (c + h + h * I).re := by
    norm_num [h]
    linarith
  have him : (c - h - h * I).im < (c + h + h * I).im := by
    norm_num [h]
    linarith
  have hF : AnalyticOnNhd ℂ (fun s => germLocalFactor s 2) Q :=
    (germLocalFactor_analyticOnNhd_pos 2 (by norm_num)).mono Q_subset_re_pos
  obtain ⟨z, hzQ, hz⟩ := rouche_exists_zero_rectangle_of_unique_simple
    hre him (by simpa [Q] using hF) (by simpa [Q] using ha) hbdry
    (by simpa [Q] using hrootQ)
    (by intro s hs; exact hzero s (by simpa [Q] using hs)) hsimple
  exact ⟨z, Q_subset_ball (by simpa [Q] using hzQ), hz⟩


-- Fidelity witnesses: the conditional theorem consumes exactly the three
-- registered jet hypotheses, and the candidate square is inhabited.
example
    (hval : ‖g 60 c‖ < 4 / 10 ^ 10)
    (hder : 187 / 100 < (deriv (g 60) c).re)
    (hcurv : ∀ s ∈ Q, ‖deriv (deriv (g 60)) s‖ ≤ 400) :
    ∃ z ∈ Metric.ball c (1 / 10 ^ 8), germLocalFactor z 2 = 0 :=
  germ_zero_of_center_jet hval hder hcurv

example : Q.Nonempty := ⟨c, c_mem_Q⟩

#print axioms Q_apply
#print axioms Q_subset_ball
#print axioms Q_subset_re_pos
#print axioms c_in_golden_window
#print axioms c_mem_Q
#print axioms beta_nonneg
#print axioms local_term_norm
#print axioms local_terms_summable
#print axioms germLocalFactor_eq_trunc_add_tail
#print axioms local_term_norm_le_growth
#print axioms germLocalFactor_two_tail_le
#print axioms exp_neg_36911_lt_69139
#print axioms exp_0065_lt_107
#print axioms germLocalFactor_two_tail_Q_V60
#print axioms rouche_exists_zero_rectangle_of_unique_simple
#print axioms Q_border_norm_sub_center_ge
#print axioms g_analytic
#print axioms truncation_taylor_remainder_of_curv
#print axioms germ_zero_of_center_jet

end D5.S3.Analytic.GermWindow.GermZeroCertificateReduction
