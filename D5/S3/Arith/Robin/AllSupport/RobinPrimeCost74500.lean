/- GID: D5/S3/Arith/Robin/AllSupport/RobinPrimeCost74500
   generality: I
   mirror-B: none(waiver:analytic-input-for-RobinLargeHeightMargin)
   mirror-E: none(waiver:analytic-prime-cost-estimate)
   anchors: []
   utility: none
   digest: A weighted prime block supplies an explicit normalized Robin prime-cost lower bound under RH. -/

/-
The choice of the interval and the structure of the prime-square estimate follow
Robin1984's PrimeCostExplicitCoefficient.lean at the commit below (Apache-2.0).
The constants here use the native weighted tail and root estimates.
https://github.com/kimihiro64/Robin1984/blob/5ce18bf3487c68d9353276ef5811057f60d17808/Robin1984/Analytic/PrimeCostExplicitCoefficient.lean
-/

import D5.S3.Arith.Robin.AllSupport.PrimeBlock
import D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel
import D5.S3.Arith.GoldenResource.RobinRationalBasis
import D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.AllSupport

open MeasureTheory Set Real
open D5.S3.Arith.GoldenResource.RobinRationalBasis
open D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero firstLiMass)
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
  (H J weight J_log_bounds firstLiMass_lt_twentieth log_two_pi_lt_two)
open D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope (on_line)

private lemma log_height_lower :
    (56 / 5 : ℝ) ≤ Real.log (74500 : ℝ) := by
  have htwo := log_two_decimal_bounds.1
  have hratio := Real.one_sub_inv_le_log_of_pos
    (show (0 : ℝ) < (18625 : ℝ) / 16384 by norm_num)
  have hfactor : (74500 : ℝ) = 2 ^ 16 * ((18625 : ℝ) / 16384) := by
    norm_num
  have hlogid : Real.log (74500 : ℝ) =
      16 * Real.log 2 + Real.log ((18625 : ℝ) / 16384) := by
    rw [hfactor, Real.log_mul (by norm_num) (by norm_num), Real.log_pow] <;> norm_num
  rw [hlogid]
  have hrat : (2241 / 18625 : ℝ) ≤ Real.log (18625 / 16384) := by
    convert hratio using 1 <;> norm_num
  linarith only [htwo, hrat]

private lemma sqrt_log_half {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  congr 1
  ring

private lemma root_power_bounds_386 {u : ℝ} (hu : Real.log 386 ≤ u) :
    Real.exp (-(1 / 6 : ℝ) * u) ≤ 371 / 1000 ∧
    Real.exp (-(3 / 10 : ℝ) * u) ≤ 168 / 1000 ∧
    Real.exp (-(1 / 4 : ℝ) * u) ≤ 226 / 1000 ∧
    Real.exp (-(1 / 3 : ℝ) * u) ≤ 138 / 1000 ∧
    Real.exp (-(2 / 5 : ℝ) * u) ≤ 93 / 1000 := by
  have hbase {a : ℕ} :
      Real.exp (-(a : ℝ) * Real.log 386) = (1 / 386 : ℝ) ^ a := by
    rw [show -(a : ℝ) * Real.log 386 = (a : ℝ) * (-Real.log 386) by ring,
      Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 386), one_div]
  have bound (a d : ℕ) (hd : d ≠ 0) {c q : ℝ} (hq : 0 ≤ q)
      (hc : (d : ℝ) * c = a) (hcert : (1 / 386 : ℝ) ^ a ≤ q ^ d) :
      Real.exp (-c * u) ≤ q := by
    apply (pow_le_pow_iff_left₀ (Real.exp_nonneg _) hq hd).mp
    rw [← Real.exp_nat_mul,
      show (d : ℝ) * (-c * u) = -(a : ℝ) * u by
        rw [show (d : ℝ) * (-c * u) = -((d : ℝ) * c) * u by ring, hc]]
    calc
      Real.exp (-(a : ℝ) * u) ≤ Real.exp (-(a : ℝ) * Real.log 386) :=
        Real.exp_le_exp.mpr
          (mul_le_mul_of_nonpos_left hu (neg_nonpos.mpr (Nat.cast_nonneg a)))
      _ = (1 / 386 : ℝ) ^ a := hbase
      _ ≤ q ^ d := hcert
  exact ⟨bound 1 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    bound 3 10 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    bound 1 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    bound 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    bound 2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

private lemma J_two_normalized_74500
    (hline : ∀ k : ℕ, (actualZero k).re = 1 / 2) {x : ℝ} (hx : 2 ≤ x) :
    -((1 / 20 : ℝ) * (2 + 1 / Real.log x) / Real.sqrt x + 2 / x) ≤
        x * Real.log x * J 2 x ∧
    x * Real.log x * J 2 x ≤
      (1 / 20 : ℝ) * (2 + 1 / Real.log x) / Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hu : 0 < Real.log x := Real.log_pos (by linarith)
  have hlog : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  obtain ⟨hlo, hhi⟩ := J_log_bounds hline (j := 2) (by norm_num) (by norm_num) hlog
  have hscale : 0 ≤ x * Real.log x := by positivity
  have hm : x * Real.log x *
      (firstLiMass * Real.exp ((1 / 2 - 2) * Real.log x) * H 2 (Real.log x)) =
      firstLiMass * (2 + 1 / Real.log x) / Real.sqrt x := by
    have hs : Real.exp ((1 / 2 - 2) * Real.log x) = (x * Real.sqrt x)⁻¹ := by
      rw [show (1 / 2 - 2 : ℝ) * Real.log x =
        -(Real.log x + Real.log x / 2) by ring,
        Real.exp_neg, Real.exp_add, Real.exp_log hx0, ← sqrt_log_half hx0]
    rw [hs]
    unfold H
    field_simp [hx0.ne', hu.ne', (Real.sqrt_pos.mpr hx0).ne'] <;> ring
  have hc : x * Real.log x *
      (Real.log (2 * Real.pi) * Real.exp (-2 * Real.log x) / Real.log x) =
      Real.log (2 * Real.pi) / x := by
    have he : Real.exp (-2 * Real.log x) = (x ^ 2)⁻¹ := by
      rw [show -2 * Real.log x = -(Real.log x * 2) by ring,
        Real.exp_neg, Real.exp_mul, Real.exp_log hx0, Real.rpow_two]
    rw [he]
    field_simp [hx0.ne', hu.ne']
  rw [Real.exp_log hx0] at hlo hhi
  have h1 := mul_le_mul_of_nonneg_left hlo hscale
  rw [mul_sub, mul_neg, hm, hc] at h1
  have h2 := mul_le_mul_of_nonneg_left hhi hscale
  rw [hm] at h2
  have hM := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right firstLiMass_lt_twentieth.le
      (show 0 ≤ 2 + 1 / Real.log x by positivity)) (Real.sqrt_nonneg x)
  have hC := div_le_div_of_nonneg_right log_two_pi_lt_two.le hx0.le
  exact ⟨by linarith only [h1, hM, hC], h2.trans hM⟩

private lemma B_two_normalized_74500 {x : ℝ} (hx : 1 < x) :
    2 - 1 / Real.log x ≤ x * Real.log x * B 2 1 (Real.log x) ∧
    x * Real.log x * B 2 1 (Real.log x) ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hu := Real.log_pos hx
  have hlo := mul_le_mul_of_nonneg_left (B_two_lower hu)
    (show 0 ≤ x * Real.log x by positivity)
  have hhi := mul_le_mul_of_nonneg_left
    (B_upper (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) < 2) hu)
    (show 0 ≤ x * Real.log x by positivity)
  have he : Real.exp (-Real.log x) = x⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hx0]
  rw [he] at hlo
  rw [show (1 - 2 : ℝ) = -1 by norm_num, neg_one_mul, he] at hhi
  constructor
  · convert hlo using 1 <;> field_simp [hx0.ne', hu.ne'] <;> ring
  · convert hhi using 1 <;> field_simp [hx0.ne', hu.ne'] <;> norm_num

private lemma normalized_P_two_74500
    (hline : ∀ k : ℕ, (actualZero k).re = 1 / 2) {x : ℝ}
    (hx : 386 ≤ x) (hv : 1189 / 200 ≤ Real.log x) :
    x * Real.sqrt x * Real.log x * P 2 x ≤ 211 / 100 := by
  have hx0 : 0 < x := by linarith
  let u := Real.log x
  have hu : 0 < u := by dsimp [u]; linarith
  have hlog : Real.log 386 ≤ u := by
    dsimp [u]
    exact Real.log_le_log (by norm_num) hx
  obtain ⟨h6, h310, h4, h3, h25⟩ := root_power_bounds_386 hlog
  have hk {k : ℝ} (hk : 1 ≤ k) (hk5 : k ≤ 5) : Real.log 2 ≤ u / k := by
    refine (le_div_iff₀ (by linarith : 0 < k)).mpr ?_
    have h := mul_le_mul (show Real.log 2 ≤ 7 / 10 by linarith [Real.log_two_lt_d9]) hk5
      (by linarith) (by norm_num)
    dsimp [u]
    linarith
  have h2 := normalized_root_bound hline (k := 2) (by norm_num) (by norm_num) hu
    (hk (by norm_num) (by norm_num))
  have h3' := normalized_root_bound hline (k := 3) (by norm_num) (by norm_num) hu
    (hk (by norm_num) (by norm_num))
  have h5 := normalized_root_bound hline (k := 5) (by norm_num) (by norm_num) hu
    (hk (by norm_num) (by norm_num))
  norm_num at h2 h3' h5
  have hrw : Real.exp ((3 / 2 : ℝ) * u) = x * Real.sqrt x := by
    dsimp [u]
    rw [show (3 / 2 : ℝ) * Real.log x = Real.log x + Real.log x / 2 by ring,
      Real.exp_add, Real.exp_log hx0, ← sqrt_log_half hx0]
  rw [Real.exp_log hx0] at h2 h3' h5
  have hi : 1 / u ≤ 200 / 1189 := by
    apply (div_le_iff₀ hu).mpr
    dsimp [u]
    linarith
  have c2 : 2 + 1 / u ≤ 2 + 200 / 1189 := by linarith
  simp only [div_eq_mul_inv, one_mul] at c2
  simp only [neg_mul] at h6 h310 h4 h3 h25
  have hscale : 0 ≤ Real.exp ((3 / 2 : ℝ) * u) * u := by positivity
  have hP := mul_le_mul_of_nonneg_left
    (P_upper_root (j := 2) (by norm_num) (by linarith : 1 < x)) hscale
  rw [hrw] at hP
  have hterm2 : Real.exp ((3 / 2 : ℝ) * u) * u *
      (B 2 (2 : ℝ)⁻¹ u + (1 / 2) * J 4 (x ^ (2 : ℝ)⁻¹)) ≤
      (4 / 3 : ℝ) + 2 * (1 / 20) * (2 + 200 / 1189) * (226 / 1000) := by
    norm_num
    refine h2.trans ?_
    have h := mul_le_mul c2 h4 (Real.exp_nonneg _) (show 0 ≤ (2 + 200 / 1189 : ℝ) by norm_num)
    nlinarith only [h]
  have hterm3 : Real.exp ((3 / 2 : ℝ) * u) * u *
      (B 2 (3 : ℝ)⁻¹ u + (1 / 3) * J 6 (x ^ (3 : ℝ)⁻¹)) ≤
      (6 / 5 : ℝ) * (371 / 1000) +
        3 * (1 / 20) * (2 + 200 / 1189) * (138 / 1000) := by
    norm_num
    refine h3'.trans ?_
    have h := mul_le_mul c2 h3 (Real.exp_nonneg _) (show 0 ≤ (2 + 200 / 1189 : ℝ) by norm_num)
    nlinarith only [h, h6]
  have hterm5 : Real.exp ((3 / 2 : ℝ) * u) * u *
      (B 2 (5 : ℝ)⁻¹ u + (1 / 5) * J 10 (x ^ (5 : ℝ)⁻¹)) ≤
      (10 / 9 : ℝ) * (168 / 1000) +
        5 * (1 / 20) * (2 + 200 / 1189) * (93 / 1000) := by
    norm_num
    refine h5.trans ?_
    have h := mul_le_mul c2 h25 (Real.exp_nonneg _) (show 0 ≤ (2 + 200 / 1189 : ℝ) by norm_num)
    nlinarith only [h, h310]
  rw [hrw] at hterm2 hterm3 hterm5
  norm_num at hP hterm2 hterm3 hterm5
  linarith only [hP, hterm2, hterm3, hterm5]

private lemma T_two_lower_74500
    (hline : ∀ k : ℕ, (actualZero k).re = 1 / 2) {x : ℝ}
    (hx : 386 ≤ x) (hu : 1189 / 200 ≤ Real.log x) :
    1713 / 1000 ≤ x * Real.log x * T 2 x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hv : 0 < Real.log x := by linarith
  have hs : 98 / 5 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hi : 1 / Real.log x ≤ 200 / 1189 := (div_le_iff₀ hv).mpr (by linarith)
  have hP := normalized_P_two_74500 hline hx hu
  have hP' : x * Real.log x * P 2 x ≤ (211 / 100) / Real.sqrt x := by
    apply (le_div_iff₀ hs0).2
    convert hP using 1 <;> ring
  have hPr := hP'.trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 98 / 5) hs)
  have hJ := (J_two_normalized_74500 hline (by linarith : 2 ≤ x)).1
  have hJ1 : (1 / 20 : ℝ) * (2 + 1 / Real.log x) / Real.sqrt x ≤
      (1 / 20) * (2 + 200 / 1189) / (98 / 5) := by
    apply (div_le_div_of_nonneg_left (by positivity :
      0 ≤ (1 / 20 : ℝ) * (2 + 1 / Real.log x)) (by norm_num : (0 : ℝ) < 98 / 5) hs).trans
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith only [hi]
  have hJ2 : 2 / x ≤ 2 / 386 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hB := (B_two_normalized_74500 hx1).1
  rw [T_eq (by norm_num) hx1]
  rw [mul_sub, mul_add]
  linarith only [hPr, hJ, hJ1, hJ2, hB, hi]

private lemma T_two_upper_74500
    (hline : ∀ k : ℕ, (actualZero k).re = 1 / 2) {x : ℝ}
    (hx : 2 ≤ x) :
    x * Real.log x * T 2 x ≤ 2 + (2 + 1 / Real.log x) / (20 * Real.sqrt x) := by
  have hx1 : 1 < x := by linarith
  have hJ := (J_two_normalized_74500 hline hx).2
  have hB := (B_two_normalized_74500 hx1).2
  have hP : 0 ≤ x * Real.log x * P 2 x :=
    mul_nonneg (mul_nonneg (by linarith [hx]) (Real.log_pos hx1).le) (P_nonneg (by norm_num) hx1)
  rw [T_eq (by norm_num) hx1]
  rw [mul_sub, mul_add, div_mul_eq_div_div]
  have he : (2 + 1 / Real.log x) / 20 = (1 / 20) * (2 + 1 / Real.log x) := by ring
  rw [he]
  linarith only [hB, hJ, hP]

/-- The RH-conditional normalized lower bound for the actual prime-cost block. -/
theorem theta_weight_two_block_normalized_lower
    (hRH : RiemannHypothesis) {h : ℝ} (hh : 74500 ≤ h) :
    (2264003 / 1000000 : ℝ) ≤
      (Real.sqrt h * Real.log h) *
        (∫ t in Set.Ioc (Real.sqrt (2 * h)) (h / 2),
          Chebyshev.theta t * weight 2 t) := by
  let s := Real.sqrt (2 * h)
  let b := h / 2
  let u := Real.log s
  let v := Real.log b
  let D := Real.sqrt h * Real.log h
  change (2264003 / 1000000 : ℝ) ≤ D * (∫ t in Set.Ioc s b, Chebyshev.theta t * weight 2 t)
  have hh0 : 0 < h := by linarith
  have hlog_h : (56 / 5 : ℝ) ≤ Real.log h :=
    log_height_lower.trans (Real.log_le_log (by norm_num) hh)
  have hD : 0 ≤ D :=
    mul_nonneg (Real.sqrt_nonneg h) (by linarith [hlog_h])
  have hlog2u : Real.log 2 ≤ 347 / 500 := by linarith [log_two_decimal_bounds.2]
  have hsqrt_h : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hs0 : 0 < s := by
    dsimp [s]
    positivity
  have hs : 386 ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  have hloga : u = (Real.log h + Real.log 2) / 2 := by
    dsimp [u, s]
    rw [Real.log_sqrt (by positivity), Real.log_mul (by norm_num) hh0.ne']
    ring
  have hu : (1189 / 200 : ℝ) ≤ u := by
    rw [hloga]
    linarith [log_two_decimal_bounds.1, hlog_h]
  have hu0 : 0 < u := by linarith
  have hb : 37250 ≤ b := by dsimp [b]; linarith
  have hlogb : v = Real.log h - Real.log 2 := by
    dsimp [v, b]
    rw [Real.log_div hh0.ne' (by norm_num)]
  have hv : (5253 / 500 : ℝ) ≤ v := by
    rw [hlogb]
    linarith only [hlog2u, hlog_h]
  have hv0 : 0 < v := by linarith
  have hb0 : 0 < b := by linarith
  have hsb : s ≤ b := by
    dsimp [s, b]
    refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
    nlinarith only [mul_nonneg hh0.le (sub_nonneg.mpr (show (8 : ℝ) ≤ h by linarith))]
  have hline : ∀ k : ℕ, (actualZero k).re = 1 / 2 :=
    on_line hRH
  have hTs : (1713 / 1000 : ℝ) ≤ s * u * T 2 s :=
    T_two_lower_74500 hline hs hu
  have hTb : b * v * T 2 b ≤ 2 + (2 + 1 / v) / (20 * Real.sqrt b) :=
    T_two_upper_74500 hline (by linarith [hb])
  have hDs : (1331 / 1000 : ℝ) ≤ D / (s * u) := by
    have hsum : 0 < Real.log h + Real.log 2 := by
      linarith only [hloga, hu0]
    have hratio : D / (s * u) =
        Real.sqrt 2 * Real.log h / (Real.log h + Real.log 2) := by
      have hsprod : s = Real.sqrt 2 * Real.sqrt h :=
        Real.sqrt_mul (by norm_num) h
      have hs2 : 0 < Real.sqrt (2 : ℝ) := by positivity
      have hcancel : 2 / Real.sqrt 2 = Real.sqrt 2 := by
        apply (div_eq_iff hs2.ne').mpr
        rw [← pow_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [hloga, hsprod]
      dsimp only [D]
      calc
        _ = (2 / Real.sqrt 2) * Real.log h / (Real.log h + Real.log 2) := by
          field_simp [hs2.ne', hsqrt_h.ne', hsum.ne'] <;> ring
        _ = _ := by rw [hcancel]
    rw [hratio]
    have hsqrt2 : (7071 / 5000 : ℝ) ≤ Real.sqrt 2 := by
      exact Real.le_sqrt_of_sq_le (by norm_num)
    have hprod : (1331 / 1000 : ℝ) * Real.log 2 ≤
        (1331 / 1000) * (347 / 500) := by
      exact mul_le_mul_of_nonneg_left hlog2u (by norm_num)
    have hdiffL :
        ((7071 / 5000 : ℝ) - 1331 / 1000) * (56 / 5) ≤
          (Real.sqrt 2 - 1331 / 1000) * Real.log h := by
      have hcoef : (7071 / 5000 : ℝ) - 1331 / 1000 ≤
          Real.sqrt 2 - 1331 / 1000 := by linarith
      exact mul_le_mul hcoef hlog_h (by norm_num) (by linarith [hsqrt2])
    have hconst : (1331 / 1000 : ℝ) * (347 / 500) ≤
        ((7071 / 5000 : ℝ) - 1331 / 1000) * (56 / 5) := by
      norm_num
    have hgap : (1331 / 1000 : ℝ) * (Real.log h + Real.log 2) ≤
        Real.sqrt 2 * Real.log h := by
      nlinarith [hdiffL, hconst, hprod]
    exact (le_div_iff₀ hsum).mpr hgap
  have hDb : D / (b * v) ≤ 2 / 255 := by
    have hden : 0 < Real.log h - Real.log 2 := by linarith only [hv0, hlogb]
    have hratio : D / (b * v) =
        2 * Real.log h / (Real.sqrt h * (Real.log h - Real.log 2)) := by
      rw [hlogb]
      dsimp only [b, D]
      calc
        _ = (Real.sqrt h * Real.log h) /
            ((Real.sqrt h) ^ 2 / 2 * (Real.log h - Real.log 2)) := by
          rw [Real.sq_sqrt hh0.le]
        _ = _ := by field_simp [hsqrt_h.ne', hden.ne'] <;> ring
    rw [hratio]
    have hsqrt : (272 : ℝ) ≤ Real.sqrt h := Real.le_sqrt_of_sq_le (by nlinarith)
    have hfrac : Real.log h ≤ (16 / 15 : ℝ) * (Real.log h - Real.log 2) := by
      nlinarith [hlog_h, hlog2u]
    have hquot : 2 * Real.log h / (Real.log h - Real.log 2) ≤ 32 / 15 :=
      (div_le_iff₀ hden).mpr (by nlinarith [hfrac])
    have hscaled := mul_le_mul_of_nonneg_right hquot (by positivity : 0 ≤ (Real.sqrt h)⁻¹)
    have hsqrt_inv : (Real.sqrt h)⁻¹ ≤ (272 : ℝ)⁻¹ := by
      exact (inv_le_inv₀ (by positivity) (by norm_num)).mpr hsqrt
    have hmul := mul_le_mul_of_nonneg_left hsqrt_inv (by positivity : 0 ≤ (32 / 15 : ℝ))
    calc
      2 * Real.log h / (Real.sqrt h * (Real.log h - Real.log 2)) =
          (2 * Real.log h / (Real.log h - Real.log 2)) * (Real.sqrt h)⁻¹ := by
            field_simp [hsqrt_h.ne', hden.ne'] <;> ring
      _ ≤ (32 / 15) * (272 : ℝ)⁻¹ := hscaled.trans hmul
      _ = 2 / 255 := by norm_num
  have hAb : b * v * T 2 b ≤ 2001 / 1000 := by
    have hterm : (2 + 1 / v) / (20 * Real.sqrt b) ≤ 1 / 1000 := by
      have hsqrtb : (192 : ℝ) ≤ Real.sqrt b := Real.le_sqrt_of_sq_le (by nlinarith)
      have hinv : 1 / v ≤ 1 := (div_le_iff₀ hv0).mpr (by linarith)
      have hnum : 2 + 1 / v ≤ 3 := by linarith
      have hden : 20 * (192 : ℝ) ≤ 20 * Real.sqrt b := by nlinarith
      calc
        (2 + 1 / v) / (20 * Real.sqrt b) ≤
            3 / (20 * Real.sqrt b) :=
          div_le_div_of_nonneg_right hnum (by positivity)
        _ ≤ 3 / (20 * (192 : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
        _ ≤ 1 / 1000 := by norm_num
    linarith only [hTb, hterm]
  have hTnonneg : 0 ≤ T 2 b := by
    unfold T
    exact setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (Chebyshev.theta_nonneg t)
        (weight_nonneg (by norm_num) (by linarith [hb, show b < t from ht]))
  have hs_id : D * T 2 s = (D / (s * u)) * (s * u * T 2 s) := by
    field_simp [hs0.ne', hu0.ne'] <;> ring
  have hb_id : D * T 2 b = (D / (b * v)) * (b * v * T 2 b) := by
    field_simp [hb0.ne', hv0.ne'] <;> ring
  have hsTerm : (1331 / 1000 : ℝ) * (1713 / 1000) ≤ D * T 2 s := by
    rw [hs_id]
    exact mul_le_mul hDs hTs (by norm_num) (div_nonneg hD (mul_nonneg hs0.le hu0.le))
  have hbTerm : D * T 2 b < (16 / 1000 : ℝ) := by
    rw [hb_id]
    have hnonneg := mul_nonneg (mul_nonneg hb0.le hv0.le) hTnonneg
    exact (mul_le_mul hDb hAb hnonneg (by norm_num)).trans_lt (by norm_num)
  have htail := theta_interval_as_tail (j := 2) (a := s) (z := b)
    (by norm_num) (by linarith [hs]) hsb
  rw [intervalIntegral.integral_of_le hsb] at htail
  rw [htail, mul_sub]
  have hreserve : (2264003 / 1000000 : ℝ) ≤ D * T 2 s - D * T 2 b := by
    linarith only [hsTerm, hbTerm]
  exact hreserve

/-- The same normalized reserve paid by the actual prime-cost functional. -/
theorem primeCost_normalized_lower
    (hRH : RiemannHypothesis) {h : ℝ} (hh : 74500 ≤ h) :
    (2264003 / 1000000 : ℝ) ≤ (Real.sqrt h * Real.log h) * primeCost h := by
  have hblock := theta_weight_two_block_normalized_lower hRH hh
  have hcost := theta_weight_two_block_le_prime_cost (h := h) (by linarith)
  have hscale : 0 ≤ Real.sqrt h * Real.log h :=
    mul_nonneg (Real.sqrt_nonneg h) (Real.log_nonneg (by linarith [hh]))
  exact hblock.trans (mul_le_mul_of_nonneg_left hcost hscale)

end D5.S3.Arith.Robin.AllSupport
