/- GID: D5/S3/Arith/Robin/AllSupport/RobinSignedTail74500
   generality: I
   mirror-B: none(waiver:analytic-input-for-RobinLargeHeightMargin)
   mirror-E: none(waiver:explicit-signed-tail-estimate)
   anchors: []
   utility: none
   digest: The normalized adverse first-weight theta tail is strictly below 223/100 under RH for heights at least 74500. -/

import D5.S3.Arith.Robin.AllSupport.Cost
import D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope
import D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedPrimePowers
import D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedRootTransfer
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

/-!
# The signed first-weight Chebyshev tail above 74500

The estimate structure follows the Robin1984 contributors'
`robin_prime_power_sub_psi_tail_le_scalar` and
`robinMertensWeightedScalar_lt_113_div_50` (Apache-2.0).
The integral and zero bounds here use the native Chebyshev functions and actual zero data.

https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/Robin1984/NicolasLandau/MertensWeightedBound.lean#L64
https://github.com/kimihiro64/Robin1984/blob/acab1a31f31e0499518a4416b63281e0b4838f9c/Robin1984/Analytic/MertensExplicitCoefficient.lean#L43
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open D5.S3.Arith.Robin.ActualRobinClockCovariance (activationDensity)
open D5.S3.Arith.Robin.PriceRecord.Effective.RobinEffectiveAbel (B B_upper P)
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedZeroLaplace
  (H H_nonneg J J_eq_integral J_log_bounds J_one_eq_weightedTail
    actual_weighted_tail_lower firstLiMass_lt_twentieth weight)
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedPrimePowers
  (powerCorrection_le_roots)
open D5.S3.Weil.Mertens.IntegratedExplicit.RobinWeightedRootTransfer
  (square_root_power_main_bounds)
open D5.S3.Weil.ZeroData.ActualReciprocalSquareBounds (actualZero firstLiMass)

namespace D5.S3.Arith.Robin.AllSupport

private lemma signed_theta_tail_eq {h : ℝ} (hh : 2 ≤ h) :
    -thetaTail h = P 1 h - J 1 h := by
  have hh0 : 0 < h := by linarith
  have hw (t : ℝ) (ht : t ∈ Ioi h) : weight 1 t = activationDensity t := by
    have ht0 : 0 < t := hh0.trans ht
    have hlog : 0 < Real.log t := Real.log_pos (by linarith [show h < t from ht])
    unfold weight H activationDensity
    rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp [ht0.ne', hlog.ne'] <;> ring
  have hJ : J 1 h = ∫ t in Ioi h, (Chebyshev.psi t - t) * activationDensity t := by
    rw [J_eq_integral hh0]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [hw t ht])
  have hP : P 1 h =
      ∫ t in Ioi h, (Chebyshev.psi t - Chebyshev.theta t) * activationDensity t := by
    unfold P
    exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by rw [hw t ht])
  have hi := D5.S3.Arith.Robin.Analytic.RHSharpArithmeticEnvelope.tails hh
  have hsplit : J 1 h - P 1 h = thetaTail h := by
    rw [hJ, hP, ← integral_sub hi.1 hi.2.1, thetaTail]
    exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by ring)
  linarith only [hsplit]

private lemma log_height_bounds :
    (56 / 5 : ℝ) ≤ Real.log 74500 ∧ Real.log 74500 ≤ (1123 / 100 : ℝ) := by
  have hlog : Real.log (74500 : ℝ) = 16 * Real.log 2 + Real.log (18625 / 16384) := by
    rw [show (74500 : ℝ) = 2 ^ (16 : ℕ) * (18625 / 16384) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow] <;> norm_num
  have htwo := D5.S3.Arith.GoldenResource.RobinRationalBasis.log_two_decimal_bounds
  have hlo : (2241 / 18625 : ℝ) ≤ Real.log (18625 / 16384) := calc
    _ = 1 - (18625 / 16384 : ℝ)⁻¹ := by norm_num
    _ ≤ _ := Real.one_sub_inv_le_log_of_pos (by norm_num)
  have hhi : Real.log (18625 / 16384) ≤ (2241 / 16384 : ℝ) := calc
    _ ≤ (18625 / 16384 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    _ = _ := by norm_num
  rw [hlog]
  constructor
  · linarith only [htwo.1, hlo]
  · linarith only [htwo.2, hhi]

private lemma exp_power_at_height {a q : ℝ} {n m : ℕ}
    (hq : 0 ≤ q) (hn : 0 < n) (ha : (n : ℝ) * a = m)
    (hcert : ((74500 : ℝ) ^ m)⁻¹ ≤ q ^ n) :
    Real.exp (-a * Real.log 74500) ≤ q := by
  have hpow : (Real.exp (-a * Real.log 74500)) ^ n = ((74500 : ℝ) ^ m)⁻¹ := by
    calc
      _ = Real.exp (-((n : ℝ) * a) * Real.log 74500) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ = _ := by
        rw [ha, neg_mul, Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  exact (pow_le_pow_iff_left₀ (Real.exp_nonneg _) hq hn.ne').mp
    (hpow.trans_le hcert)

private lemma normalized_root_error (hline : ∀ k : ℕ, (actualZero k).re = 1 / 2)
    {k u : ℝ} (hk : 1 ≤ k) (hk' : k ≤ 10) (hu : 0 < u)
    (hroot : Real.log 2 ≤ u / k) :
    Real.exp (u / 2) * u * (k⁻¹ * J k ((Real.exp u) ^ k⁻¹)) ≤
      k * (1 / 20) * (1 + 1 / u) * Real.exp ((k⁻¹ / 2 - 1 / 2) * u) := by
  have hk0 : 0 < k := by linarith
  have hJ := (J_log_bounds hline hk hk' hroot).2
  have harg : (Real.exp u) ^ k⁻¹ = Real.exp (u / k) := by
    rw [← Real.exp_mul, div_eq_mul_inv]
  rw [← harg] at hJ
  have hMass : firstLiMass * Real.exp ((1 / 2 - k) * (u / k)) * H k (u / k) ≤
      (1 / 20) * Real.exp ((1 / 2 - k) * (u / k)) * H k (u / k) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right firstLiMass_lt_twentieth.le (Real.exp_nonneg _))
      (H_nonneg (by linarith) (div_pos hu hk0))
  have hExp : Real.exp (u / 2) * Real.exp ((1 / 2 - k) * (u / k)) =
      Real.exp ((k⁻¹ / 2 - 1 / 2) * u) := by
    rw [← Real.exp_add]
    congr 1
    field_simp [hk0.ne'] <;> ring
  calc
    _ ≤ Real.exp (u / 2) * u *
          (k⁻¹ * ((1 / 20) * Real.exp ((1 / 2 - k) * (u / k)) * H k (u / k))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hJ.trans hMass) (inv_nonneg.mpr hk0.le))
        (by positivity)
    _ = k * (1 / 20) * (1 + 1 / u) *
          (Real.exp (u / 2) * Real.exp ((1 / 2 - k) * (u / k))) := by
      unfold H
      field_simp [hk0.ne', hu.ne'] <;> ring
    _ = _ := by rw [hExp]

private lemma normalized_power_correction (hline : ∀ k : ℕ, (actualZero k).re = 1 / 2)
    {u : ℝ} (hu : (56 / 5 : ℝ) ≤ u) :
    Real.exp (u / 2) * u * P 1 (Real.exp u) ≤
      2 - 2 * u / (u + 2) ^ 2 +
        (3 / 2) * Real.exp (-(1 / 6) * u) + (5 / 4) * Real.exp (-(3 / 10) * u) +
        (1 + 1 / u) * ((1 / 10) * Real.exp (-(1 / 4) * u) +
          (3 / 20) * Real.exp (-(1 / 3) * u) + (1 / 4) * Real.exp (-(2 / 5) * u)) := by
  have hu0 : 0 < u := by linarith
  have hscale : 0 ≤ Real.exp (u / 2) * u := by positivity
  have hexp : 1 < Real.exp u := Real.one_lt_exp_iff.mpr hu0
  have hP := mul_le_mul_of_nonneg_left
    (powerCorrection_le_roots (j := 1) le_rfl hexp) hscale
  simp only [Real.log_exp, mul_one, mul_add] at hP
  have hmain2 : Real.exp (u / 2) * u * B 1 (2 : ℝ)⁻¹ u ≤
      2 - 2 * u / (u + 2) ^ 2 := by
    have hupper := (square_root_power_main_bounds hu0).2
    have hB : B 1 (2 : ℝ)⁻¹ u = ∫ v in Ioi u, Real.exp (-(1 / 2 : ℝ) * v) * H 1 v := by
      unfold B
      rw [show (2 : ℝ)⁻¹ - 1 = -(1 / 2 : ℝ) by norm_num]
    have hcancel : Real.exp (u / 2) * Real.exp (-(1 / 2 : ℝ) * u) = 1 := by
      rw [← Real.exp_add, show u / 2 + -(1 / 2 : ℝ) * u = 0 by ring, Real.exp_zero]
    rw [← hB] at hupper
    calc
      _ ≤ Real.exp (u / 2) * u *
          (2 * (Real.exp (-(1 / 2 : ℝ) * u) / u) -
            2 * Real.exp (-(1 / 2 : ℝ) * u) / (u + 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hupper hscale
      _ = (2 - 2 * u / (u + 2) ^ 2) *
          (Real.exp (u / 2) * Real.exp (-(1 / 2 : ℝ) * u)) := by
        field_simp [hu0.ne', show u + 2 ≠ 0 by linarith] <;> ring
      _ = _ := by rw [hcancel, mul_one]
  have main_bound {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
      Real.exp (u / 2) * u * B 1 r u ≤ (1 / (1 - r)) * Real.exp ((r - 1 / 2) * u) := by
    calc
      _ ≤ Real.exp (u / 2) * u * (1 / (1 - r) * Real.exp ((r - 1) * u) / u) :=
        mul_le_mul_of_nonneg_left (B_upper hr0 hr1 hu0) hscale
      _ = (1 / (1 - r)) * (Real.exp (u / 2) * Real.exp ((r - 1) * u)) := by
        field_simp [hu0.ne', (sub_pos.mpr hr1).ne'] <;> ring
      _ = _ := by rw [← Real.exp_add, show u / 2 + (r - 1) * u = (r - 1 / 2) * u by ring]
  have hmain3 : Real.exp (u / 2) * u * B 1 (3 : ℝ)⁻¹ u ≤
      (3 / 2) * Real.exp (-(1 / 6) * u) := by
    convert main_bound (r := (3 : ℝ)⁻¹) (by norm_num) (by norm_num) using 1 <;> norm_num
  have hmain5 : Real.exp (u / 2) * u * B 1 (5 : ℝ)⁻¹ u ≤
      (5 / 4) * Real.exp (-(3 / 10) * u) := by
    convert main_bound (r := (5 : ℝ)⁻¹) (by norm_num) (by norm_num) using 1 <;> norm_num
  have root_height {k : ℝ} (hk : 1 ≤ k) (hk5 : k ≤ 5) : Real.log 2 ≤ u / k := by
    have hk0 : 0 < k := by linarith
    have hlog2 : Real.log 2 ≤ 7 / 10 := by linarith [Real.log_two_lt_d9]
    have hm := mul_le_mul hlog2 hk5 hk0.le (by norm_num : (0 : ℝ) ≤ 7 / 10)
    exact (le_div_iff₀ hk0).mpr (by linarith)
  have herr2 : Real.exp (u / 2) * u * ((2 : ℝ)⁻¹ * J 2 ((Real.exp u) ^ (2 : ℝ)⁻¹)) ≤
      (1 / 10) * (1 + 1 / u) * Real.exp (-(1 / 4) * u) := by
    convert normalized_root_error hline (k := 2) (by norm_num) (by norm_num) hu0
      (root_height (by norm_num) (by norm_num)) using 1 <;> norm_num
  have herr3 : Real.exp (u / 2) * u * ((3 : ℝ)⁻¹ * J 3 ((Real.exp u) ^ (3 : ℝ)⁻¹)) ≤
      (3 / 20) * (1 + 1 / u) * Real.exp (-(1 / 3) * u) := by
    convert normalized_root_error hline (k := 3) (by norm_num) (by norm_num) hu0
      (root_height (by norm_num) (by norm_num)) using 1 <;> norm_num
  have herr5 : Real.exp (u / 2) * u * ((5 : ℝ)⁻¹ * J 5 ((Real.exp u) ^ (5 : ℝ)⁻¹)) ≤
      (1 / 4) * (1 + 1 / u) * Real.exp (-(2 / 5) * u) := by
    convert normalized_root_error hline (k := 5) (by norm_num) (by norm_num) hu0
      (root_height (by norm_num) (by norm_num)) using 1 <;> norm_num
  refine hP.trans ((add_le_add (add_le_add (add_le_add hmain2 herr2)
    (add_le_add hmain3 herr3)) (add_le_add hmain5 herr5)).trans_eq ?_)
  ring

private lemma scalar_lt_223_div_100 {h : ℝ} (hh : 74500 ≤ h) :
    let u := Real.log h
    2 - 2 * u / (u + 2) ^ 2 +
      (3 / 2) * Real.exp (-(1 / 6) * u) + (5 / 4) * Real.exp (-(3 / 10) * u) +
      (1 + 1 / u) * ((1 / 10) * Real.exp (-(1 / 4) * u) +
        (3 / 20) * Real.exp (-(1 / 3) * u) + (1 / 4) * Real.exp (-(2 / 5) * u)) +
      ((1 / 20) * (1 + 1 / u) + 2 * Real.exp (-(1 / 2) * u)) < (223 / 100 : ℝ) := by
  dsimp only
  let u := Real.log h
  have hh0 : 0 < h := by linarith
  have hu : (56 / 5 : ℝ) ≤ u :=
    log_height_bounds.1.trans (Real.log_le_log (by norm_num) hh)
  have hu0 : 0 < u := by linarith
  let e (a : ℝ) := Real.exp (-a * u)
  change 2 - 2 * u / (u + 2) ^ 2 + (3 / 2) * e (1 / 6) + (5 / 4) * e (3 / 10) +
    (1 + 1 / u) * ((1 / 10) * e (1 / 4) + (3 / 20) * e (1 / 3) + (1 / 4) * e (2 / 5)) +
    ((1 / 20) * (1 + 1 / u) + 2 * e (1 / 2)) < (223 / 100 : ℝ)
  have decay {a q : ℝ} (ha : 0 < a) (ha6 : a⁻¹ ≤ 6)
      (hq : Real.exp (-a * Real.log 74500) ≤ q) :
      u * e a ≤ (1123 / 100) * q := by
    have hbase : Real.exp a⁻¹ ≤ (74500 : ℝ) :=
      (Real.le_log_iff_exp_le (by norm_num)).mp
        (ha6.trans ((by norm_num : (6 : ℝ) ≤ 56 / 5).trans log_height_bounds.1))
    have hmono := Real.log_div_self_rpow_antitoneOn ha hbase (hbase.trans hh) hh
    have hrewrite (x : ℝ) (hx : 0 < x) :
        Real.log x / x ^ a = Real.log x * Real.exp (-a * Real.log x) := by
      rw [div_eq_mul_inv, Real.rpow_def_of_pos hx, ← Real.exp_neg]
      congr 2 <;> ring
    change Real.log h / h ^ a ≤ Real.log 74500 / (74500 : ℝ) ^ a at hmono
    rw [hrewrite h hh0, hrewrite 74500 (by norm_num)] at hmono
    exact hmono.trans (mul_le_mul log_height_bounds.2 hq (Real.exp_nonneg _) (by norm_num))
  have hd6 := decay (a := 1 / 6) (q := 771 / 5000) (by norm_num) (by norm_num)
    (exp_power_at_height (n := 6) (m := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hd310 := decay (a := 3 / 10) (q := 173 / 5000) (by norm_num) (by norm_num)
    (exp_power_at_height (n := 10) (m := 3) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hd4 := decay (a := 1 / 4) (q := 303 / 5000) (by norm_num) (by norm_num)
    (exp_power_at_height (n := 4) (m := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hd3 := decay (a := 1 / 3) (q := 119 / 5000) (by norm_num) (by norm_num)
    (exp_power_at_height (n := 3) (m := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hd25 := decay (a := 2 / 5) (q := 113 / 10000) (by norm_num) (by norm_num)
    (exp_power_at_height (n := 5) (m := 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  have hd2 := decay (a := 1 / 2) (q := 37 / 10000) (by norm_num) (by norm_num)
    (exp_power_at_height (n := 2) (m := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num))
  let errors := (1 / 10 : ℝ) * (u * e (1 / 4)) +
    (3 / 20) * (u * e (1 / 3)) + (1 / 4) * (u * e (2 / 5))
  have herrors0 : 0 ≤ errors := by dsimp only [errors]; positivity
  have herrors : errors ≤ (1123 / 100 : ℝ) *
      ((1 / 10) * (303 / 5000) + (3 / 20) * (119 / 5000) + (1 / 4) * (113 / 10000)) := by
    dsimp only [errors]
    linarith only [hd4, hd3, hd25]
  have hinv : 1 / u ≤ (5 / 56 : ℝ) := calc
    _ ≤ 1 / (56 / 5 : ℝ) := one_div_le_one_div_of_le (by norm_num) hu
    _ = _ := by norm_num
  have hweighted := mul_le_mul (show 1 + 1 / u ≤ (61 / 56 : ℝ) by linarith)
    herrors herrors0 (by norm_num : (0 : ℝ) ≤ 61 / 56)
  have hpositive : (3 / 2) * (u * e (1 / 6)) + (5 / 4) * (u * e (3 / 10)) +
      (1 + 1 / u) * errors + 2 * (u * e (1 / 2)) + 1 / 20 ≤
      (3772895293 / 1120000000 : ℝ) := by
    linarith only [hd6, hd310, hd2, hweighted]
  have hratio : (28 / 33 : ℝ) ≤ u / (u + 2) :=
    (le_div_iff₀ (by positivity : 0 < u + 2)).mpr (by linarith)
  have hratio_sq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 28 / 33) hratio 2
  have hbudget : (470428 / 136125 : ℝ) ≤ (18 / 100) * u + 2 * (u / (u + 2)) ^ 2 := by
    linarith only [hu, hratio_sq]
  have hgap : (3772895293 / 1120000000 : ℝ) < 470428 / 136125 := by norm_num
  have hlinear : u * ((1 / 20) * (1 + 1 / u)) = u / 20 + 1 / 20 := by
    field_simp [hu0.ne'] <;> ring
  have hsquare : u * (2 * u / (u + 2) ^ 2) = 2 * (u / (u + 2)) ^ 2 := by
    rw [div_pow]
    ring
  apply (mul_lt_mul_iff_right₀ hu0).mp
  calc
    _ = 2 * u - u * (2 * u / (u + 2) ^ 2) + u * ((1 / 20) * (1 + 1 / u)) +
          ((3 / 2) * (u * e (1 / 6)) + (5 / 4) * (u * e (3 / 10)) +
            (1 + 1 / u) * errors + 2 * (u * e (1 / 2))) := by
      dsimp only [errors]
      ring
    _ = 2 * u - 2 * (u / (u + 2)) ^ 2 + u / 20 +
          ((3 / 2) * (u * e (1 / 6)) + (5 / 4) * (u * e (3 / 10)) +
            (1 + 1 / u) * errors + 2 * (u * e (1 / 2)) + 1 / 20) := by
      rw [hlinear, hsquare]
      ring
    _ < _ := by linarith only [hpositive.trans_lt (hgap.trans_le hbudget)]

/-- Under RH the normalized negative activation-weighted Chebyshev tail is
strictly below the coefficient (223/100) for every real height at least 74500. -/
theorem normalized_neg_thetaTail_lt_223_div_100 (hRH : RiemannHypothesis)
    {h : ℝ} (hh : 74500 ≤ h) :
    -(Real.sqrt h * Real.log h) * thetaTail h < (223 / 100 : ℝ) := by
  let u := Real.log h
  have hh0 : 0 < h := by linarith
  have hh2 : 2 ≤ h := by linarith
  have hu : (56 / 5 : ℝ) ≤ u :=
    log_height_bounds.1.trans (Real.log_le_log (by norm_num) hh)
  have hline : ∀ k : ℕ, (actualZero k).re = 1 / 2 :=
    D5.S3.Weil.Mertens.IntegratedExplicit.RHSharpActualEnvelope.on_line hRH
  have hsqrt : Real.sqrt h = Real.exp (u / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hh0]
    change Real.exp (u * (1 / 2 : ℝ)) = Real.exp (u / 2)
    congr 1
    ring
  have hP := normalized_power_correction hline hu
  have hexp : Real.exp u = h := Real.exp_log hh0
  rw [hexp, ← hsqrt] at hP
  have hJ := actual_weighted_tail_lower hline hh2
  rw [← J_one_eq_weightedTail] at hJ
  change -((1 / 20 : ℝ) * (1 + 1 / u) + 2 / Real.sqrt h) ≤
    Real.sqrt h * u * J 1 h at hJ
  have hinv : 2 / Real.sqrt h = 2 * Real.exp (-(1 / 2 : ℝ) * u) := by
    rw [hsqrt, show -(1 / 2 : ℝ) * u = -(u / 2) by ring, Real.exp_neg, div_eq_mul_inv]
  rw [hinv] at hJ
  change -(Real.sqrt h * u) * thetaTail h < _
  rw [neg_mul, ← mul_neg, signed_theta_tail_eq hh2, mul_sub, sub_eq_add_neg]
  exact (add_le_add hP (by simpa only [neg_neg] using neg_le_neg hJ)).trans_lt
    (scalar_lt_223_div_100 hh)

end D5.S3.Arith.Robin.AllSupport
