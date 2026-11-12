import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceCandidate
import D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import Mathlib.Tactic

/-! Actual five-mode test predecessors from two independent BHP suppliers.

All five signed modes use distinct actual primes, their original valuations,
and complete insertion/deletion fees. Constants are uniform over full records
at arbitrary positive prices. The two BHP suppliers remain unverified hypotheses.
The resulting test slack does not establish prescribed bank payment or RH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlackCandidate

open Real Filter Finset
open scoped Topology BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.ActualReserve.HarmonicReference (referencePrice)
open D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open D5.S3.Arith.Robin.ActualPriceRecordPrimeStructure (price_record_prime_structure)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerLogSlope
  (beta gain beta_pos beta_nat log_beta_drop)
open D5.S3.Arith.Robin.PriceRecord.HigherLayerClampedCutoff
  (cutoff cutoff_spec cutoff_antitone)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerShrinkingPrimeRoster (root_atTop)
open D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature
  (d normalized_gain_bounds)
open D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
  (P actual_quartic_error)
open D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
  (layerPrime valuation_below_layer_prime valuation_above_layer_prime
   signed_exchange_certificate)
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceCandidate
  (FullRecord BHPMaximumGap BHPShortIntervalCount bhpExponent priceExponent
   comparisonCount primesIn logMass bhp_boundary_price_localization)

/- Price conversion is an inequality about the actual price, not an identification
of referencePrice X with beta 1 X. It is uniform in real X >= 2. -/

private theorem reference_price_sandwich {X : ℝ} (hX : 2 ≤ X) :
    0 < beta 1 X ∧
      (1 - 1 / X) * referencePrice X ≤ beta 1 X ∧
      beta 1 X ≤ referencePrice X := by
  have hX0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos (by linarith)
  have hr : 0 < referencePrice X := by
    dsimp [referencePrice]
    positivity
  obtain ⟨hlo, hhi, _, _⟩ := normalized_gain_bounds (by norm_num : 1 ≤ 1) hX
  have he : beta 1 X = (gain 1 X * X) * referencePrice X := by
    dsimp [beta, referencePrice]
    field_simp [hX0.ne', hL.ne']
    <;> ring
  refine ⟨beta_pos hX (by norm_num), ?_, ?_⟩
  · rw [he]
    exact mul_le_mul_of_nonneg_right (by simpa using hlo) hr.le
  · rw [he]
    have hhi' : gain 1 X * X ≤ 1 := by simpa only [pow_one] using hhi
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hhi' hr.le

private theorem reference_log_price_ratio {X : ℝ} (hX : 2 ≤ X) :
    0 ≤ log (referencePrice X / beta 1 X) ∧
      log (referencePrice X / beta 1 X) ≤ 2 / X := by
  obtain ⟨hb, hlo, hhi⟩ := reference_price_sandwich hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos (by linarith)
  have hr : 0 < referencePrice X := by dsimp [referencePrice]; positivity
  have ht : 0 < 1 - 1 / X := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hX
    linarith
  have hq : referencePrice X / beta 1 X ≤ 1 / (1 - 1 / X) := by
    apply (div_le_div_iff₀ hb ht).mpr
    simpa only [one_mul, mul_comm] using hlo
  have hsmall : 1 / (1 - 1 / X) - 1 ≤ 2 / X := by
    have he : 1 / (1 - 1 / X) - 1 = 1 / (X - 1) := by
      field_simp [hX0.ne', (by linarith : X - 1 ≠ 0)]
      <;> ring
    rw [he]
    apply (div_le_div_iff₀ (by linarith : 0 < X - 1) hX0).mpr
    linarith
  refine ⟨log_nonneg ((one_le_div hb).mpr hhi), ?_⟩
  exact (log_le_sub_one_of_pos (div_pos hr hb)).trans (by linarith)

private def actualOffset (j : ℕ) (X : ℝ) : ℝ :=
  (j : ℝ) * log (cutoff j (beta 1 X)) - log X

/- The reference root is required active here. This is proved eventually from
root_atTop below. Both cutoff_spec invocations retain the clamped endpoint. -/
private theorem clamped_log_price_transfer {j : ℕ} (hj : 2 ≤ j)
    {X : ℝ} (hX : 2 ≤ X) (hactive : 2 < cutoff j (referencePrice X)) :
    0 ≤ actualOffset j X - d j X ∧
      actualOffset j X - d j X ≤ 6 / X := by
  obtain ⟨hb, _, hbr⟩ := reference_price_sandwich hX
  have hX0 : 0 < X := by linarith
  have hL : 0 < log X := log_pos (by linarith)
  have hr : 0 < referencePrice X := by dsimp [referencePrice]; positivity
  let u := cutoff j (referencePrice X)
  let v := cutoff j (beta 1 X)
  have hu : 2 ≤ u := (cutoff_spec hj hr).1
  have huv : u ≤ v := cutoff_antitone hj hb hr hbr
  have hv : 2 < v := hactive.trans_le huv
  have hru : beta j u = referencePrice X := (cutoff_spec hj hr).2.2.1 hactive
  have hrv : beta j v = beta 1 X := (cutoff_spec hj hb).2.2.1 hv
  have hdrop := log_beta_drop hj hu huv
  rw [hru, hrv] at hdrop
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  rw [log_div hv0.ne' hu0.ne'] at hdrop
  have hlogs : 0 ≤ log v - log u := sub_nonneg.mpr (log_le_log hu0 huv)
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have he : actualOffset j X - d j X = (j : ℝ) * (log v - log u) := by
    dsimp [actualOffset, d, u, v]
    ring
  rw [he]
  refine ⟨mul_nonneg hj0 hlogs, ?_⟩
  have hh := (reference_log_price_ratio hX).2
  simp only [div_eq_mul_inv] at hdrop hh ⊢
  nlinarith only [hdrop, hh]

private theorem relative_price_log_distance {j : ℕ} (hj : 2 ≤ j)
    {u v lambda e : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v)
    (hlambda : 0 < lambda) (hroot : beta j v = lambda)
    (he : 0 ≤ e) (hehalf : e ≤ 1 / 2)
    (hband : |beta j u - lambda| ≤ e * lambda) :
    |(j : ℝ) * (log u - log v)| ≤ 6 * e := by
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hb : 0 < beta j u := beta_pos hu (by omega)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hband
  rcases le_total u v with huv | hvu
  · have hdrop := log_beta_drop hj hu huv
    rw [hroot, log_div hv0.ne' hu0.ne'] at hdrop
    have hratio : beta j u / lambda - 1 ≤ e := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hlambda).mpr
      nlinarith only [hhi]
    have hlog := (log_le_sub_one_of_pos (div_pos hb hlambda)).trans hratio
    have hnon : (j : ℝ) * (log u - log v) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hj0 (sub_nonpos.mpr (log_le_log hu0 huv))
    rw [abs_of_nonpos hnon]
    linarith
  · have hdrop := log_beta_drop hj hv hvu
    rw [hroot, log_div hu0.ne' hv0.ne'] at hdrop
    have hden : 0 < 1 - e := by linarith
    have hratio : lambda / beta j u ≤ 1 / (1 - e) := by
      apply (div_le_div_iff₀ hb hden).mpr
      nlinarith only [hlo]
    have hsmall : 1 / (1 - e) - 1 ≤ 2 * e := by
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hden).mpr
      nlinarith [mul_nonneg he (show 0 ≤ 1 - 2 * e by linarith)]
    have hlog : log (lambda / beta j u) ≤ 2 * e :=
      (log_le_sub_one_of_pos (div_pos hlambda hb)).trans (by linarith)
    have hnon : 0 ≤ (j : ℝ) * (log u - log v) :=
      mul_nonneg hj0 (sub_nonneg.mpr (log_le_log hv0 hvu))
    rw [abs_of_nonneg hnon]
    linarith

/- Consumes the SAME BHP localization endpoint. It is not a localization premise
and is not a second proof of the parent's boundary-price theorem. -/
private theorem uniform_boundary_root_log_transfer
    (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ A T : ℝ, 0 < A ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        |(j : ℝ) * log (layerPrime m j : ℝ) -
          (log (largestPrime m : ℝ) + actualOffset j (largestPrime m : ℝ))| ≤
          A * (largestPrime m : ℝ) ^ (-priceExponent j) := by
  obtain ⟨A, Ta, hA, hTa, hloc⟩ := bhp_boundary_price_localization hgap hcount j hj
  obtain ⟨Tg, hTg, hgeom⟩ :=
    ActualBoundaryPriceCandidate.uniform_coarse_geometry j hj
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hgamma : 0 < priceExponent j := by
    dsimp [priceExponent]
    positivity
  have hsmall : Tendsto (fun X : ℝ => A * X ^ (-priceExponent j)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_rpow_neg_atTop hgamma).const_mul A
  have hgood : ∀ᶠ X : ℝ in atTop,
      2 ≤ X ∧ 2 < cutoff j (referencePrice X) ∧ A * X ^ (-priceExponent j) ≤ 1 / 2 := by
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      (root_atTop hj).eventually_gt_atTop 2,
      hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with X hX hr he
    exact ⟨hX, hr, he.le⟩
  obtain ⟨Ts, hTs⟩ := eventually_atTop.mp hgood
  let T := max Ta (max Tg Ts)
  refine ⟨6 * A, T, by positivity, lt_of_lt_of_le hTa (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  let R : ℝ := largestPrime m
  have hTaR : Ta ≤ R := (le_max_left Ta (max Tg Ts)).trans hlarge
  have hTgR : Tg ≤ R :=
    (le_max_left Tg Ts).trans ((le_max_right Ta (max Tg Ts)).trans hlarge)
  have hTsR : Ts ≤ R :=
    (le_max_right Tg Ts).trans ((le_max_right Ta (max Tg Ts)).trans hlarge)
  obtain ⟨hR2, hr, hehalf⟩ := hTs R hTsR
  have hQ4 := (hgeom m hm mu hmu hrecord hTgR).2.1
  obtain ⟨hlambda, _, hle⟩ := reference_price_sandwich hR2
  have hrprice : 0 < referencePrice R := by
    dsimp [referencePrice]
    have hR0 : 0 < R := by linarith
    have hLR : 0 < log R := log_pos (by linarith)
    positivity
  have hrootactive : 2 < cutoff j (beta 1 R) :=
    hr.trans_le (cutoff_antitone hj hlambda hrprice hle)
  have hroot : beta j (cutoff j (beta 1 R)) = beta 1 R :=
    (cutoff_spec hj hlambda).2.2.1 hrootactive
  have he0 : 0 ≤ A * R ^ (-priceExponent j) := by positivity
  have hb := hloc m hm mu hmu hrecord hTaR
  have hb' : |beta j (layerPrime m j : ℝ) - beta 1 R| ≤
      (A * R ^ (-priceExponent j)) * beta 1 R := by
    simpa only [R, mul_assoc, mul_left_comm, mul_comm] using hb
  have hh := relative_price_log_distance hj (by linarith : 2 ≤ (layerPrime m j : ℝ))
    hrootactive.le hlambda hroot he0 hehalf hb'
  convert hh using 1
  · congr 1
    dsimp [actualOffset, R]
    ring
  · ring

/- The existing quartic theorem is now honestly transferred to beta 1 X.
No estimate for the actual record boundary layerPrime is asserted here. -/
private theorem actual_price_quartic_error {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun X : ℝ => log X ^ 4 *
      (actualOffset j X - (P (log j)).eval (1 / log X))) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun X : ℝ => log X ^ 4 / X) atTop (𝓝 0) := by
    simpa only [rpow_natCast, rpow_one] using
      (_root_.isLittleO_log_rpow_rpow_atTop (4 : ℕ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  have ht : Tendsto (fun X : ℝ => log X ^ 4 * (actualOffset j X - d j X))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun X : ℝ => 6 * (log X ^ 4 / X)) ?_
      (by simpa only [mul_zero] using hsmall.const_mul 6)
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      (root_atTop hj).eventually_gt_atTop 2] with X hX hr
    obtain ⟨h0, h1⟩ := clamped_log_price_transfer hj hX hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg (log_nonneg (show 1 ≤ X by linarith)) 4),
      abs_of_nonneg h0]
    have hh := mul_le_mul_of_nonneg_left h1 (pow_nonneg (log_nonneg (show 1 ≤ X by linarith)) 4)
    convert hh using 1 <;> ring
  have hh := ht.add (actual_quartic_error hj)
  simp only [add_zero] at hh
  convert hh using 1
  funext X
  ring

private def mesh1 (X : ℝ) : ℝ := actualOffset 2 X
private def mesh2 (X : ℝ) : ℝ := actualOffset 4 X - 2 * actualOffset 2 X
private def mesh3 (X : ℝ) : ℝ :=
  -actualOffset 8 X + 3 * actualOffset 4 X - 3 * actualOffset 2 X
private def mesh4 (X : ℝ) : ℝ :=
  actualOffset 16 X - 4 * actualOffset 8 X +
    6 * actualOffset 4 X - 4 * actualOffset 2 X

/- Exact quartic stencil algebra. Writing the polynomial in z avoids generic
inverse-function derivatives and exposes every lower-order cancellation. -/
private theorem stencil_polynomial (a z : ℝ) :
    a - (P a).eval z =
      a * z - (a + a ^ 2 / 2) * z ^ 2 +
        (a + 3 * a ^ 2 / 2 + a ^ 3 / 3) * z ^ 3 -
        (a + 3 * a ^ 2 + 11 * a ^ 3 / 6 + a ^ 4 / 4) * z ^ 4 ∧
    (P (2 * a)).eval z - 2 * (P a).eval z =
      a ^ 2 * z ^ 2 - (3 * a ^ 2 + 2 * a ^ 3) * z ^ 3 +
        (6 * a ^ 2 + 11 * a ^ 3 + 7 * a ^ 4 / 2) * z ^ 4 ∧
    -(P (3 * a)).eval z + 3 * (P (2 * a)).eval z - 3 * (P a).eval z =
      2 * a ^ 3 * z ^ 3 - (11 * a ^ 3 + 9 * a ^ 4) * z ^ 4 ∧
    (P (4 * a)).eval z - 4 * (P (3 * a)).eval z +
        6 * (P (2 * a)).eval z - 4 * (P a).eval z = 6 * a ^ 4 * z ^ 4 := by
  simp only [P, Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private theorem dyadic_logs :
    log (4 : ℝ) = 2 * log 2 ∧ log (8 : ℝ) = 3 * log 2 ∧
      log (16 : ℝ) = 4 * log 2 := by
  constructor
  · simpa only [show (2 : ℝ) ^ (2 : ℕ) = 4 by norm_num, Nat.cast_ofNat]
      using (log_pow (2 : ℝ) 2)
  constructor
  · simpa only [show (2 : ℝ) ^ (3 : ℕ) = 8 by norm_num, Nat.cast_ofNat]
      using (log_pow (2 : ℝ) 3)
  · simpa only [show (2 : ℝ) ^ (4 : ℕ) = 16 by norm_num, Nat.cast_ofNat]
      using (log_pow (2 : ℝ) 4)

private theorem actual_price_error_scaled {j : ℕ} (hj : 2 ≤ j)
    (n : ℕ) (hn : n ≤ 4) :
    Tendsto (fun X : ℝ => log X ^ n *
      (actualOffset j X - (P (log j)).eval (1 / log X))) atTop (𝓝 0) := by
  have hz : Tendsto (fun X : ℝ => 1 / log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have hh := (actual_price_quartic_error hj).mul (hz.pow (4 - n))
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
  have hL : log X ≠ 0 := (log_pos hX).ne'
  have hp : log X ^ 4 = log X ^ n * log X ^ (4 - n) := by
    have he : n + (4 - n) = 4 := by omega
    rw [← pow_add, he]
  rw [hp, one_div_pow]
  field_simp [pow_ne_zero (4 - n) hL]
  <;> ring

private theorem polynomial_stencil_limits (a : ℝ) :
    Tendsto (fun X : ℝ => log X * (a - (P a).eval (1 / log X)))
      atTop (𝓝 a) ∧
    Tendsto (fun X : ℝ => log X ^ 2 *
      ((P (2 * a)).eval (1 / log X) - 2 * (P a).eval (1 / log X)))
      atTop (𝓝 (a ^ 2)) ∧
    Tendsto (fun X : ℝ => log X ^ 3 *
      (-(P (3 * a)).eval (1 / log X) +
        3 * (P (2 * a)).eval (1 / log X) - 3 * (P a).eval (1 / log X)))
      atTop (𝓝 (2 * a ^ 3)) ∧
    Tendsto (fun X : ℝ => log X ^ 4 *
      ((P (4 * a)).eval (1 / log X) - 4 * (P (3 * a)).eval (1 / log X) +
        6 * (P (2 * a)).eval (1 / log X) - 4 * (P a).eval (1 / log X)))
      atTop (𝓝 (6 * a ^ 4)) := by
  have hz : Tendsto (fun X : ℝ => 1 / log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have h1c : Continuous (fun z : ℝ => a - (a + a ^ 2 / 2) * z +
      (a + 3 * a ^ 2 / 2 + a ^ 3 / 3) * z ^ 2 -
      (a + 3 * a ^ 2 + 11 * a ^ 3 / 6 + a ^ 4 / 4) * z ^ 3) := by fun_prop
  have h2c : Continuous (fun z : ℝ => a ^ 2 - (3 * a ^ 2 + 2 * a ^ 3) * z +
      (6 * a ^ 2 + 11 * a ^ 3 + 7 * a ^ 4 / 2) * z ^ 2) := by fun_prop
  have h3c : Continuous (fun z : ℝ => 2 * a ^ 3 - (11 * a ^ 3 + 9 * a ^ 4) * z) :=
    by fun_prop
  have h1 : Tendsto (fun X : ℝ => a - (a + a ^ 2 / 2) * (1 / log X) +
      (a + 3 * a ^ 2 / 2 + a ^ 3 / 3) * (1 / log X) ^ 2 -
      (a + 3 * a ^ 2 + 11 * a ^ 3 / 6 + a ^ 4 / 4) * (1 / log X) ^ 3)
      atTop (𝓝 a) := by simpa [Function.comp_def] using h1c.continuousAt.tendsto.comp hz
  have h2 : Tendsto (fun X : ℝ => a ^ 2 - (3 * a ^ 2 + 2 * a ^ 3) * (1 / log X) +
      (6 * a ^ 2 + 11 * a ^ 3 + 7 * a ^ 4 / 2) * (1 / log X) ^ 2)
      atTop (𝓝 (a ^ 2)) := by simpa [Function.comp_def] using h2c.continuousAt.tendsto.comp hz
  have h3 : Tendsto (fun X : ℝ => 2 * a ^ 3 - (11 * a ^ 3 + 9 * a ^ 4) * (1 / log X))
      atTop (𝓝 (2 * a ^ 3)) := by simpa [Function.comp_def] using h3c.continuousAt.tendsto.comp hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply h1.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [(stencil_polynomial a (1 / log X)).1]
    field_simp [(log_pos hX).ne']
    <;> ring
  · apply h2.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [(stencil_polynomial a (1 / log X)).2.1]
    field_simp [(log_pos hX).ne']
    <;> ring
  · apply h3.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [(stencil_polynomial a (1 / log X)).2.2.1]
    field_simp [(log_pos hX).ne']
    <;> ring
  · apply (tendsto_const_nhds : Tendsto (fun _ : ℝ => 6 * a ^ 4) atTop (𝓝 _)).congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    rw [(stencil_polynomial a (1 / log X)).2.2.2]
    field_simp [(log_pos hX).ne']
    <;> ring

private theorem actual_stencil_limits :
    Tendsto (fun X : ℝ => log X * (log 2 - mesh1 X)) atTop (𝓝 (log 2)) ∧
    Tendsto (fun X : ℝ => log X ^ 2 * mesh2 X) atTop (𝓝 (log 2 ^ 2)) ∧
    Tendsto (fun X : ℝ => log X ^ 3 * mesh3 X) atTop (𝓝 (2 * log 2 ^ 3)) ∧
    Tendsto (fun X : ℝ => log X ^ 4 * mesh4 X) atTop (𝓝 (6 * log 2 ^ 4)) := by
  obtain ⟨hl4, hl8, hl16⟩ := dyadic_logs
  obtain ⟨h1, h2, h3, h4⟩ := polynomial_stencil_limits (log 2)
  have herr (j n : ℕ) (hj : 2 ≤ j) (hn : n ≤ 4) := actual_price_error_scaled hj n hn
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hh := h1.sub (herr 2 1 (by norm_num) (by norm_num))
    simp only [sub_zero, pow_one] at hh
    convert hh using 1
    funext X
    dsimp [mesh1]
    ring
  · have he := (herr 4 2 (by norm_num) (by norm_num)).sub
      ((herr 2 2 (by norm_num) (by norm_num)).const_mul 2)
    simp only [mul_zero, sub_zero] at he
    have hh := h2.add he
    simp only [add_zero] at hh
    convert hh using 1
    funext X
    dsimp [mesh2]
    rw [hl4]
    ring
  · have he := (herr 8 3 (by norm_num) (by norm_num)).neg.add
      ((herr 4 3 (by norm_num) (by norm_num)).const_mul 3) |>.sub
        ((herr 2 3 (by norm_num) (by norm_num)).const_mul 3)
    simp only [neg_zero, mul_zero, add_zero, sub_zero] at he
    have hh := h3.add he
    simp only [add_zero] at hh
    convert hh using 1
    funext X
    dsimp [mesh3]
    rw [hl4, hl8]
    ring
  · have he := (herr 16 4 (by norm_num) (by norm_num)).sub
      ((herr 8 4 (by norm_num) (by norm_num)).const_mul 4) |>.add
        ((herr 4 4 (by norm_num) (by norm_num)).const_mul 6) |>.sub
        ((herr 2 4 (by norm_num) (by norm_num)).const_mul 4)
    simp only [mul_zero, sub_zero, add_zero] at he
    have hh := h4.add he
    simp only [add_zero] at hh
    convert hh using 1
    funext X
    dsimp [mesh4]
    rw [hl4, hl8, hl16]
    ring

/- A scalar floor step is enough for all three greedy coefficients. -/
private theorem greedy_step {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b) :
    0 ≤ t - (⌊t / b⌋₊ : ℝ) * b ∧
      t - (⌊t / b⌋₊ : ℝ) * b < b ∧
      (⌊t / b⌋₊ : ℝ) ≤ t / b := by
  have hq : 0 ≤ t / b := div_nonneg ht hb.le
  have hlo := Nat.floor_le hq
  have hhi := Nat.lt_floor_add_one (t / b)
  have hlo' := (le_div_iff₀ hb).mp hlo
  have hhi' := (div_lt_iff₀ hb).mp hhi
  exact ⟨by linarith, by linarith, hlo⟩

/- Coefficients are integer multiples of the five masses F_k. Their sum is
exactly zero. A mode 2^k coefficient still requires 2^k*|n_k| DISTINCT primes;
this algebra does not silently treat one repeated prime as that many changes. -/
private def stencilCoefficients (q2 q3 q4 : ℕ) : Fin 5 → ℤ :=
  ![-1 + (q2 : ℤ) + q3 + q4,
    1 - 2 * (q2 : ℤ) - 3 * q3 - 4 * q4,
    (q2 : ℤ) + 3 * q3 + 6 * q4,
    -(q3 : ℤ) - 4 * q4,
    (q4 : ℤ)]

private theorem stencil_coefficients_sum (q2 q3 q4 : ℕ) :
    ∑ k : Fin 5, stencilCoefficients q2 q3 q4 k = 0 := by
  simp [stencilCoefficients, Fin.sum_univ_succ]
  <;> ring

private theorem stencil_mass_identity (q2 q3 q4 : ℕ) (F0 F1 F2 F3 F4 : ℝ) :
    (∑ k : Fin 5, (stencilCoefficients q2 q3 q4 k : ℝ) *
      (![F0, F1, F2, F3, F4] k)) =
      (F1 - F0) + q2 * (F2 - 2 * F1 + F0) +
        q3 * (-F3 + 3 * F2 - 3 * F1 + F0) +
        q4 * (F4 - 4 * F3 + 6 * F2 - 4 * F1 + F0) := by
  have hzero : (∑ k : Fin 5, (stencilCoefficients q2 q3 q4 k : ℝ)) = 0 := by
    exact_mod_cast stencil_coefficients_sum q2 q3 q4
  calc
    _ = ∑ k : Fin 5, (stencilCoefficients q2 q3 q4 k : ℝ) *
        ((![F0, F1, F2, F3, F4] k) - F0) := by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, hzero, zero_mul, sub_zero]
    _ = _ := by
      simp [stencilCoefficients, Fin.sum_univ_succ]
      <;> push_cast <;> ring

private theorem greedy_three_meshes {a f b2 b3 b4 : ℝ}
    (hb2 : 0 < b2) (hb3 : 0 < b3) (hb4 : 0 < b4)
    (ht : 0 ≤ a - 2 * b4 - f) :
    ∃ q2 q3 q4 : ℕ,
      2 * b4 ≤ a - (f + q2 * b2 + q3 * b3 + q4 * b4) ∧
      a - (f + q2 * b2 + q3 * b3 + q4 * b4) < 3 * b4 ∧
      (q2 : ℝ) ≤ (a - 2 * b4 - f) / b2 ∧
      (q3 : ℝ) < b2 / b3 ∧ (q4 : ℝ) < b3 / b4 := by
  let t := a - 2 * b4 - f
  let q2 : ℕ := ⌊t / b2⌋₊
  let u := t - (q2 : ℝ) * b2
  have h2 := greedy_step ht hb2
  change 0 ≤ u ∧ u < b2 ∧ (q2 : ℝ) ≤ t / b2 at h2
  let q3 : ℕ := ⌊u / b3⌋₊
  let v := u - (q3 : ℝ) * b3
  have h3 := greedy_step h2.1 hb3
  change 0 ≤ v ∧ v < b3 ∧ (q3 : ℝ) ≤ u / b3 at h3
  let q4 : ℕ := ⌊v / b4⌋₊
  let w := v - (q4 : ℝ) * b4
  have h4 := greedy_step h3.1 hb4
  change 0 ≤ w ∧ w < b4 ∧ (q4 : ℝ) ≤ v / b4 at h4
  refine ⟨q2, q3, q4, ?_, ?_, h2.2.2, ?_, ?_⟩
  · dsimp [w, v, u, t] at h4
    linarith only [h4.1]
  · dsimp [w, v, u, t] at h4
    linarith only [h4.2.1]
  · exact h3.2.2.trans_lt ((div_lt_div_iff_of_pos_right hb3).mpr h2.2.1)
  · exact h4.2.2.trans_lt ((div_lt_div_iff_of_pos_right hb4).mpr h3.2.1)

private theorem eventual_greedy_ranges : ∃ B : ℝ, 0 < B ∧
    ∀ᶠ X : ℝ in atTop,
      1 ≤ log X ∧ 0 < mesh2 X ∧ 0 < mesh3 X ∧ 0 < mesh4 X ∧
      0 ≤ log 2 - 2 * mesh4 X - mesh1 X ∧
      (log 2 - 2 * mesh4 X - mesh1 X) / mesh2 X ≤ B * log X ∧
      mesh2 X / mesh3 X ≤ B * log X ∧
      mesh3 X / mesh4 X ≤ B * log X ∧ mesh4 X ≤ B / log X ^ 4 := by
  let a : ℝ := log 2
  have ha : 0 < a := log_pos (by norm_num)
  obtain ⟨h1, h2, h3, h4⟩ := actual_stencil_limits
  have hz : Tendsto (fun X : ℝ => 1 / log X) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_log_atTop
  have h4low : Tendsto (fun X : ℝ => log X * mesh4 X) atTop (𝓝 0) := by
    have hh := h4.mul (hz.pow 3)
    simp only [zero_pow (by norm_num : 3 ≠ 0), mul_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    field_simp [(log_pos hX).ne']
    <;> ring
  let t := fun X : ℝ => log 2 - 2 * mesh4 X - mesh1 X
  have ht : Tendsto (fun X : ℝ => log X * t X) atTop (𝓝 a) := by
    have hh := h1.sub (h4low.const_mul 2)
    simp only [mul_zero, sub_zero] at hh
    convert hh using 1
    funext X
    dsimp [t]
    ring
  have hp2 : ∀ᶠ X : ℝ in atTop, 0 < mesh2 X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      h2.eventually (eventually_gt_nhds (pow_pos ha 2))] with X hX h2X
    exact (mul_pos_iff_of_pos_left (pow_pos (log_pos hX) 2)).mp h2X
  have hp3 : ∀ᶠ X : ℝ in atTop, 0 < mesh3 X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      h3.eventually (eventually_gt_nhds (by dsimp [a] at ha; positivity :
        (0 : ℝ) < 2 * log 2 ^ 3))] with X hX h3X
    exact (mul_pos_iff_of_pos_left (pow_pos (log_pos hX) 3)).mp h3X
  have hp4 : ∀ᶠ X : ℝ in atTop, 0 < mesh4 X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      h4.eventually (eventually_gt_nhds (by dsimp [a] at ha; positivity :
        (0 : ℝ) < 6 * log 2 ^ 4))] with X hX h4X
    exact (mul_pos_iff_of_pos_left (pow_pos (log_pos hX) 4)).mp h4X
  have hpt : ∀ᶠ X : ℝ in atTop, 0 ≤ t X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      ht.eventually (eventually_gt_nhds ha)] with X hX htX
    exact ((mul_pos_iff_of_pos_left (log_pos hX)).mp htX).le
  have hr2 : Tendsto (fun X : ℝ => (t X / mesh2 X) / log X)
      atTop (𝓝 (a / a ^ 2)) := by
    have hh := ht.div h2 (pow_ne_zero 2 ha.ne')
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hp2] with X hX hb
    dsimp only [Pi.div_apply]
    field_simp [(log_pos hX).ne', hb.ne']
    <;> ring
  have hr3 : Tendsto (fun X : ℝ => (mesh2 X / mesh3 X) / log X)
      atTop (𝓝 (a ^ 2 / (2 * a ^ 3))) := by
    have hh := h2.div h3 (by positivity : (2 * log 2 ^ 3 : ℝ) ≠ 0)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hp3] with X hX hb
    dsimp only [Pi.div_apply]
    field_simp [(log_pos hX).ne', hb.ne']
    <;> ring
  have hr4 : Tendsto (fun X : ℝ => (mesh3 X / mesh4 X) / log X)
      atTop (𝓝 (2 * a ^ 3 / (6 * a ^ 4))) := by
    have hh := h3.div h4 (by positivity : (6 * log 2 ^ 4 : ℝ) ≠ 0)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hp4] with X hX hb
    dsimp only [Pi.div_apply]
    field_simp [(log_pos hX).ne', hb.ne']
    <;> ring
  let B : ℝ := 1 + |a / a ^ 2| + |a ^ 2 / (2 * a ^ 3)| +
    |2 * a ^ 3 / (6 * a ^ 4)| + |6 * a ^ 4|
  have hB : 0 < B := by dsimp [B]; positivity
  have hb2 : a / a ^ 2 < B := by
    dsimp [B]
    linarith [le_abs_self (a / a ^ 2), abs_nonneg (a ^ 2 / (2 * a ^ 3)),
      abs_nonneg (2 * a ^ 3 / (6 * a ^ 4)), abs_nonneg (6 * a ^ 4)]
  have hb3 : a ^ 2 / (2 * a ^ 3) < B := by
    dsimp [B]
    linarith [le_abs_self (a ^ 2 / (2 * a ^ 3)), abs_nonneg (a / a ^ 2),
      abs_nonneg (2 * a ^ 3 / (6 * a ^ 4)), abs_nonneg (6 * a ^ 4)]
  have hb4 : 2 * a ^ 3 / (6 * a ^ 4) < B := by
    dsimp [B]
    linarith [le_abs_self (2 * a ^ 3 / (6 * a ^ 4)), abs_nonneg (a / a ^ 2),
      abs_nonneg (a ^ 2 / (2 * a ^ 3)), abs_nonneg (6 * a ^ 4)]
  have hbu : 6 * a ^ 4 < B := by
    dsimp [B]
    linarith [le_abs_self (6 * a ^ 4), abs_nonneg (a / a ^ 2),
      abs_nonneg (a ^ 2 / (2 * a ^ 3)), abs_nonneg (2 * a ^ 3 / (6 * a ^ 4))]
  refine ⟨B, hB, ?_⟩
  filter_upwards [tendsto_log_atTop.eventually_ge_atTop 1, hp2, hp3, hp4, hpt,
    hr2.eventually (eventually_lt_nhds hb2), hr3.eventually (eventually_lt_nhds hb3),
    hr4.eventually (eventually_lt_nhds hb4), h4.eventually (eventually_lt_nhds hbu)]
    with X hL h2X h3X h4X htX hq2 hq3 hq4 hu
  have hL0 : 0 < log X := by linarith
  refine ⟨hL, h2X, h3X, h4X, htX,
    (div_le_iff₀ hL0).mp hq2.le, (div_le_iff₀ hL0).mp hq3.le,
    (div_le_iff₀ hL0).mp hq4.le, ?_⟩
  apply (le_div_iff₀ (pow_pos hL0 4)).mpr
  simpa only [mul_comm] using hu.le

private def rootMasses (X : ℝ) : Fin 5 → ℝ :=
  ![log X, log X + actualOffset 2 X, log X + actualOffset 4 X,
    log X + actualOffset 8 X, log X + actualOffset 16 X]

/- This is the ideal stencil at the actual price beta 1 X, NOT an integer
predecessor theorem. No supplied inventory or small-slack assumption occurs. -/
private theorem actual_root_greedy_stencil : ∃ B T : ℝ, 0 < B ∧ 0 < T ∧
    ∀ X : ℝ, T ≤ X → ∃ v : Fin 5 → ℤ,
      (∑ k : Fin 5, v k) = 0 ∧
      (∀ k : Fin 5, |(v k : ℝ)| ≤ B * log X) ∧
      0 < mesh4 X ∧ mesh4 X ≤ B / log X ^ 4 ∧
      2 * mesh4 X ≤ log 2 - ∑ k : Fin 5, (v k : ℝ) * rootMasses X k ∧
      log 2 - ∑ k : Fin 5, (v k : ℝ) * rootMasses X k < 3 * mesh4 X := by
  obtain ⟨B, hB, hg⟩ := eventual_greedy_ranges
  obtain ⟨T, hT⟩ := eventually_atTop.mp hg
  let B' : ℝ := 1 + 13 * B
  have hB' : 0 < B' := by dsimp [B']; positivity
  refine ⟨B', max T 2, hB', lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro X hX
  obtain ⟨hL, hb2, hb3, hb4, ht, hq2b, hq3b, hq4b, hu⟩ :=
    hT X ((le_max_left T 2).trans hX)
  obtain ⟨q2, q3, q4, hlo, hhi, hq2, hq3, hq4⟩ :=
    greedy_three_meshes hb2 hb3 hb4 ht
  have h2 : (q2 : ℝ) ≤ B * log X := hq2.trans hq2b
  have h3 : (q3 : ℝ) ≤ B * log X := hq3.le.trans hq3b
  have h4 : (q4 : ℝ) ≤ B * log X := hq4.le.trans hq4b
  have hB0 : 0 ≤ B * log X := mul_nonneg hB.le (by linarith)
  have hc : ∀ k : Fin 5, |(stencilCoefficients q2 q3 q4 k : ℝ)| ≤ B' * log X := by
    intro k
    fin_cases k <;> simp only [stencilCoefficients, Matrix.cons_val_zero,
      Matrix.cons_val_succ] <;> push_cast <;> rw [abs_le] <;>
      constructor <;> dsimp [B'] <;>
      nlinarith [Nat.cast_nonneg (α := ℝ) q2, Nat.cast_nonneg (α := ℝ) q3,
        Nat.cast_nonneg (α := ℝ) q4]
  have hm : (∑ k : Fin 5, (stencilCoefficients q2 q3 q4 k : ℝ) * rootMasses X k) =
      mesh1 X + q2 * mesh2 X + q3 * mesh3 X + q4 * mesh4 X := by
    rw [rootMasses, stencil_mass_identity]
    dsimp [mesh1, mesh2, mesh3, mesh4]
    ring
  refine ⟨stencilCoefficients q2 q3 q4, stencil_coefficients_sum q2 q3 q4,
    hc, hb4, ?_, ?_, ?_⟩
  · exact hu.trans ((div_le_div_iff_of_pos_right (pow_pos (by linarith : 0 < log X) 4)).mpr
      (by dsimp [B']; linarith))
  · rwa [hm]
  · rwa [hm]

/- The next two lemmas use the visibility-only parent patch. They select actual
prime sets from the actual BHP short-interval counts and prove original exponent
legality. They do not assume pools or substitute ideal cutoff occupancy. -/
private theorem actual_high_inventory
    (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ A W T : ℝ, 0 < A ∧ 0 < W ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        let Q : ℝ := layerPrime m j
        let R : ℝ := largestPrime m
        ∃ Lo Hi : Finset ℕ,
          Lo.card = comparisonCount j R ∧ Hi.card = comparisonCount j R ∧
          Disjoint Lo Hi ∧ R ≤ Q ^ j ∧ W * Q ^ bhpExponent ≤ Q / 2 ∧
          |beta j Q - beta 1 R| ≤ A * beta 1 R * R ^ (-priceExponent j) ∧
          (∀ p ∈ Lo, p.Prime ∧ 2 < p ∧ m.factorization p = j ∧
            Q - W * Q ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q) ∧
          (∀ p ∈ Hi, p.Prime ∧ 2 < p ∧ m.factorization p = j - 1 ∧
            Q < (p : ℝ) ∧ (p : ℝ) ≤ Q + W * Q ^ bhpExponent) := by
  have hcounted := hcount
  obtain ⟨W, c, X, hW, hc, _, hshort⟩ := hcounted
  obtain ⟨A, Ta, hA, hTa, hloc⟩ := bhp_boundary_price_localization hgap hcount j hj
  obtain ⟨Tg, hTg, hgeom⟩ :=
    ActualBoundaryPriceCandidate.uniform_higher_geometry j hj W c (max X 5) hW hc
  refine ⟨A, W, max Ta Tg, hA, hW, lt_of_lt_of_le hTa (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  dsimp only
  let Q : ℝ := layerPrime m j
  let R : ℝ := largestPrime m
  let w : ℝ := W * Q ^ bhpExponent
  obtain ⟨hXQ, hcap, hw, hbelow, habove, hRQ⟩ :=
    hgeom m hm mu hmu hrecord ((le_max_right Ta Tg).trans hlarge)
  have hQ5 : 5 ≤ Q := (le_max_right X 5).trans hXQ
  have hXQ' : X ≤ Q := (le_max_left X 5).trans hXQ
  obtain ⟨Lo, Hi, hLo, hHi, hLoI, hHiI⟩ :=
    ActualBoundaryPriceCandidate.counted_higher_pools hshort hXQ' hcap
  have hanti := (price_record_prime_structure hm hmu hrecord).1
  have hlo (p : ℕ) (hp : p ∈ Lo) :
      p.Prime ∧ 2 < p ∧ m.factorization p = j ∧
        Q - w ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q := by
    obtain ⟨hpprime, hpQlo, hpQhi⟩ := hLoI p hp
    have hpQnat : p ≤ layerPrime m j := by exact_mod_cast hpQhi
    have hpnext : layerPrime m (j + 1) < p := by
      exact_mod_cast hbelow.trans_le hpQlo
    have hjlo := valuation_below_layer_prime hpprime hanti hpQnat
    have hjhi := valuation_above_layer_prime (by omega : 0 < m)
      (by omega : 1 ≤ j + 1) hpprime hpnext
    have hp2r : (2 : ℝ) < p := by dsimp [w] at *; linarith
    exact ⟨hpprime, by exact_mod_cast hp2r, by omega, hpQlo, hpQhi⟩
  have hhi (p : ℕ) (hp : p ∈ Hi) :
      p.Prime ∧ 2 < p ∧ m.factorization p = j - 1 ∧
        Q < (p : ℝ) ∧ (p : ℝ) ≤ Q + w := by
    obtain ⟨hpprime, hpQlo, hpQhi⟩ := hHiI p hp
    have hpQnat : layerPrime m j < p := by exact_mod_cast hpQlo
    have hpprev : p ≤ layerPrime m (j - 1) := by exact_mod_cast hpQhi.trans habove
    have hjlo := valuation_below_layer_prime hpprime hanti hpprev
    have hjhi := valuation_above_layer_prime (by omega : 0 < m)
      (by omega : 1 ≤ j) hpprime hpQnat
    have hp2r : (2 : ℝ) < p := by linarith
    exact ⟨hpprime, by exact_mod_cast hp2r, by omega, hpQlo, hpQhi⟩
  have hdis : Disjoint Lo Hi := disjoint_left.mpr (by
    intro p hpL hpH
    have hL := (hlo p hpL).2.2.1
    have hH := (hhi p hpH).2.2.1
    omega)
  exact ⟨Lo, Hi, hLo, hHi, hdis, hRQ, hw,
    hloc m hm mu hmu hrecord ((le_max_left Ta Tg).trans hlarge), hlo, hhi⟩

private theorem actual_first_inventory (hcount : BHPShortIntervalCount) :
    ∃ W T : ℝ, 0 < W ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        let R : ℝ := largestPrime m
        ∃ Lo Hi : Finset ℕ,
          Lo.card = comparisonCount 16 R ∧ Hi.card = comparisonCount 16 R ∧
          Disjoint Lo Hi ∧ W * R ^ bhpExponent ≤ R / 2 ∧
          (∀ p ∈ Lo, p.Prime ∧ 2 < p ∧ m.factorization p = 1 ∧
            R - W * R ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ R) ∧
          (∀ p ∈ Hi, p.Prime ∧ 2 < p ∧ m.factorization p = 0 ∧
            R < (p : ℝ) ∧ (p : ℝ) ≤ R + W * R ^ bhpExponent) := by
  obtain ⟨W, c, X, hW, hc, _, hshort⟩ := hcount
  obtain ⟨Tf, hTf, hfirst⟩ :=
    ActualBoundaryPriceCandidate.uniform_counted_first_pools 16 (by norm_num)
      W c X hW hc hshort
  obtain ⟨Tg, hTg, hgeom⟩ :=
    ActualBoundaryPriceCandidate.uniform_coarse_geometry 2 (by norm_num)
  refine ⟨W, max 8 (max Tf Tg), hW,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  dsimp only
  let R : ℝ := largestPrime m
  have hR8 : 8 ≤ R := (le_max_left 8 (max Tf Tg)).trans hlarge
  have hTfR : Tf ≤ R :=
    (le_max_left Tf Tg).trans ((le_max_right 8 (max Tf Tg)).trans hlarge)
  have hTgR : Tg ≤ R :=
    (le_max_right Tf Tg).trans ((le_max_right 8 (max Tf Tg)).trans hlarge)
  obtain ⟨_, _, hw, Lo, Hi, hLo, hHi, hLoI, hHiI⟩ := hfirst (largestPrime m) hTfR
  obtain ⟨_, _, _, hQ2, _⟩ := hgeom m hm mu hmu hrecord hTgR
  obtain ⟨_, hsupport⟩ := price_record_prime_structure hm hmu hrecord
  have hlo (p : ℕ) (hp : p ∈ Lo) :
      p.Prime ∧ 2 < p ∧ m.factorization p = 1 ∧
        R - W * R ^ bhpExponent ≤ (p : ℝ) ∧ (p : ℝ) ≤ R := by
    obtain ⟨hpprime, hpRlo, hpRhi⟩ := hLoI p hp
    have hpmem : p ∈ m.primeFactors := by
      rw [hsupport]
      exact Nat.mem_primesLE.mpr ⟨by exact_mod_cast hpRhi, hpprime⟩
    have hpdiv : p ∣ m := Nat.dvd_of_mem_primeFactors hpmem
    have hval1 : 1 ≤ m.factorization p :=
      (hpprime.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mp hpdiv
    have hpQ2 : layerPrime m 2 < p := by exact_mod_cast (by linarith :
      (layerPrime m 2 : ℝ) < p)
    have hval2 := valuation_above_layer_prime (by omega : 0 < m)
      (by norm_num : 1 ≤ 2) hpprime hpQ2
    have hp2 : (2 : ℝ) < p := by linarith
    exact ⟨hpprime, by exact_mod_cast hp2, by omega, hpRlo, hpRhi⟩
  have hhi (p : ℕ) (hp : p ∈ Hi) :
      p.Prime ∧ 2 < p ∧ m.factorization p = 0 ∧
        R < (p : ℝ) ∧ (p : ℝ) ≤ R + W * R ^ bhpExponent := by
    obtain ⟨hpprime, hpRlo, hpRhi⟩ := hHiI p hp
    have hpnot : p ∉ m.primeFactors := by
      rw [hsupport]
      intro hp'
      have hpR : (p : ℝ) ≤ R := by
        change (p : ℝ) ≤ (largestPrime m : ℝ)
        exact_mod_cast (Nat.mem_primesLE.mp hp').1
      exact hpRlo.not_ge hpR
    have hval : m.factorization p = 0 := by
      simpa only [← Nat.support_factorization, Finsupp.mem_support_iff, not_not] using hpnot
    have hp2 : (2 : ℝ) < p := by linarith
    exact ⟨hpprime, by exact_mod_cast hp2, hval, hpRlo, hpRhi⟩
  have hdis : Disjoint Lo Hi := disjoint_left.mpr (by
    intro p hpL hpH
    have hL := (hlo p hpL).2.2.1
    have hH := (hhi p hpH).2.2.1
    omega)
  exact ⟨Lo, Hi, hLo, hHi, hdis, hw, hlo, hhi⟩

private theorem two_dvd_actual_record {m : ℕ} (hm : 2 ≤ m)
    {mu : ℝ} (hmu : 0 < mu) (hrecord : FullRecord m mu) : 2 ∣ m := by
  have hs := (price_record_prime_structure hm hmu hrecord).2
  have hex : m.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  obtain ⟨p, hp⟩ := hex
  have hpprime := Nat.prime_of_mem_primeFactors hp
  have hpP : p ≤ largestPrime m := (Nat.mem_primesLE.mp (hs ▸ hp)).1
  have hP : 2 ≤ largestPrime m := hpprime.two_le.trans hpP
  have h2mem : 2 ∈ m.primeFactors := by
    rw [hs]
    exact Nat.mem_primesLE.mpr ⟨hP, Nat.prime_two⟩
  exact Nat.dvd_of_mem_primeFactors h2mem

private def topGain (lambda : ℝ) (m : ℕ) : ℝ :=
  lambda * log 2 - goldenLayerMarginal 2 (m.factorization 2) * log 2

private def auxiliaryGain (lambda : ℝ) (m : ℕ) (D U : Finset ℕ) : ℝ :=
  (∑ p ∈ U, (goldenLayerMarginal p (m.factorization p + 1) - lambda) * log p) -
    ∑ p ∈ D, (goldenLayerMarginal p (m.factorization p) - lambda) * log p

private theorem prime_product_log (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    log ((∏ p ∈ S, p : ℕ) : ℝ) = logMass S := by
  rw [Nat.cast_prod]
  exact Real.log_prod (fun p hp => by exact_mod_cast (hS p hp).ne_zero)

/- Finite exact integer realization, using the existing signed certificate and
the unchanged objective_exchange_delta through a separate visibility patch.
Only mass positivity is an intermediate input. The global proof must derive
it by substituting selected actual pools into actual_root_greedy_stencil.
Every auxiliary prime is changed once and the actual highest 2-layer is deleted.
No hypothetical recordhood at lambda is used: recordhood stays at arbitrary mu.
-/
private theorem actual_finite_predecessor {m : ℕ} (hm : 2 ≤ m)
    {mu lambda : ℝ} (hmu : 0 < mu) (hrecord : FullRecord m mu)
    (D U : Finset ℕ)
    (hD : ∀ p ∈ D, p.Prime ∧ 2 < p ∧ p ∣ m)
    (hU : ∀ p ∈ U, p.Prime ∧ 2 < p)
    (hDU : Disjoint D U)
    (hmass : 0 < log 2 + logMass D - logMass U) :
    ∃ n : ℕ, 0 < n ∧ n < m ∧
      log (m : ℝ) - log (n : ℝ) = log 2 + logMass D - logMass U ∧
      n.factorization 2 + 1 = m.factorization 2 ∧
      goldenResourceObjective lambda n - goldenResourceObjective lambda m =
        topGain lambda m + auxiliaryGain lambda m D U ∧
      topGain lambda m < (lambda - mu) * (log (m : ℝ) - log (n : ℝ)) -
        auxiliaryGain lambda m D U := by
  classical
  have hm0 : 0 < m := by omega
  have h2dvd := two_dvd_actual_record hm hmu hrecord
  have h2D : 2 ∉ D := by intro hp; have := (hD 2 hp).2.1; omega
  have h2U : 2 ∉ U := by intro hp; have := (hU 2 hp).2; omega
  let S := insert 2 D
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime := by
    rcases mem_insert.mp hp with rfl | hp
    · exact Nat.prime_two
    · exact (hD p hp).1
  have hSd (p : ℕ) (hp : p ∈ S) : p ∣ m := by
    rcases mem_insert.mp hp with rfl | hp
    · exact h2dvd
    · exact (hD p hp).2.2
  have hUp (p : ℕ) (hp : p ∈ U) : p.Prime := (hU p hp).1
  have hSU : Disjoint S U := disjoint_left.mpr (by
    intro p hpS hpU
    rcases mem_insert.mp hpS with rfl | hpD
    · exact h2U hpU
    · exact disjoint_left.mp hDU hpD hpU)
  have hmassS : logMass S = log 2 + logMass D := by
    dsimp [S, logMass]
    rw [sum_insert h2D]
    norm_num
  let d0 : ℕ := ∏ p ∈ S, p
  let u0 : ℕ := ∏ p ∈ U, p
  have hdpos : 0 < d0 := Finset.prod_pos (fun p hp => (hS p hp).pos)
  have hupos : 0 < u0 := Finset.prod_pos (fun p hp => (hUp p hp).pos)
  have hdR : (0 : ℝ) < d0 := by exact_mod_cast hdpos
  have huR : (0 : ℝ) < u0 := by exact_mod_cast hupos
  have hdlog : log (d0 : ℝ) = log 2 + logMass D := by
    exact (prime_product_log S hS).trans hmassS
  have hulog : log (u0 : ℝ) = logMass U := prime_product_log U hUp
  have hprodR : (u0 : ℝ) < d0 := (log_lt_log_iff huR hdR).mp (by
    rw [hdlog, hulog]
    linarith only [hmass])
  have hprod : u0 < d0 := by exact_mod_cast hprodR
  let r : ℕ := m / d0
  let n : ℕ := r * u0
  have hcert := signed_exchange_certificate mu hm0 hrecord S U hS hUp hSd hSU hprod
  have hnpos : 0 < n := hcert.1
  have hnm : n < m := hcert.2.1
  have hSmem : S ⊆ m.primeFactors := fun p hp =>
    Nat.mem_primeFactors.mpr ⟨hS p hp, hSd p hp, hm0.ne'⟩
  have hdvd : d0 ∣ m :=
    (prod_dvd_prod_of_subset S m.primeFactors id hSmem).trans (Nat.prod_primeFactors_dvd m)
  have hrpos : 0 < r := Nat.div_pos (Nat.le_of_dvd hm0 hdvd) hdpos
  have hrd : r * d0 = m := Nat.div_mul_cancel hdvd
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have hlogm : log (m : ℝ) = log (r : ℝ) + log (d0 : ℝ) := by
    rw [← hrd, Nat.cast_mul, log_mul hrR.ne' hdR.ne']
  have hlogn : log (n : ℝ) = log (r : ℝ) + log (u0 : ℝ) := by
    change log ((r * u0 : ℕ) : ℝ) = _
    rw [Nat.cast_mul, log_mul hrR.ne' huR.ne']
  have heta : log (m : ℝ) - log (n : ℝ) = log 2 + logMass D - logMass U := by
    rw [hlogm, hlogn, hdlog, hulog]
    ring
  have hdfac : d0.factorization 2 = 1 := by
    simpa [d0, S, D5.S3.Factorization.PrimePowers.FiniteCrtJoin.primePowerProduct] using
      (D5.S3.Arith.Robin.PrimeValuation5040Bridge.primeBlock_factorization
        hS (fun _ => 1) 2)
  have hufac : u0.factorization 2 = 0 := by
    simpa [u0, h2U, D5.S3.Factorization.PrimePowers.FiniteCrtJoin.primePowerProduct] using
      (D5.S3.Arith.Robin.PrimeValuation5040Bridge.primeBlock_factorization
        hUp (fun _ => 1) 2)
  have hmf : m.factorization 2 = r.factorization 2 + 1 := by
    rw [← hrd, Nat.factorization_mul hrpos.ne' hdpos.ne', Finsupp.add_apply, hdfac]
  have hnf : n.factorization 2 = r.factorization 2 := by
    change (r * u0).factorization 2 = _
    rw [Nat.factorization_mul hrpos.ne' hupos.ne', Finsupp.add_apply, hufac, add_zero]
  have hdelta := FixedLayerRigidity.objective_exchange_delta lambda hm0 S U hS hUp hSd hSU
  have hgain : goldenResourceObjective lambda n - goldenResourceObjective lambda m =
      topGain lambda m + auxiliaryGain lambda m D U := by
    change goldenResourceObjective lambda n - goldenResourceObjective lambda m = _ at hdelta
    rw [hdlog, hulog] at hdelta
    change goldenResourceObjective lambda n - goldenResourceObjective lambda m = _
    rw [hdelta]
    dsimp [S, topGain, auxiliaryGain]
    rw [sum_insert h2D]
    simp only [sub_mul, sum_sub_distrib, ← mul_sum]
    dsimp [logMass]
    ring
  have hrec : goldenResourceObjective mu n - goldenResourceObjective mu m < 0 :=
    sub_neg.mpr (hrecord n hnpos hnm)
  have hprice : goldenResourceObjective mu n - goldenResourceObjective mu m =
      (goldenResourceObjective lambda n - goldenResourceObjective lambda m) -
        (lambda - mu) * (log (m : ℝ) - log (n : ℝ)) := by
    unfold goldenResourceObjective
    ring
  refine ⟨n, hnpos, hnm, heta, by omega, hgain, ?_⟩
  rw [hprice, hgain] at hrec
  linarith only [hrec]

/- Exact arbitrary-record clock comparison is already supplied by the pinned
record_mass_limits theorem. This conversion does not identify mu with a clock
price and assumes no power bound for Chebyshev.theta. -/
private theorem uniform_actual_clock : ∃ T : ℝ, 0 < T ∧
    ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
      T ≤ (largestPrime m : ℝ) →
      1 ≤ log (largestPrime m : ℝ) ∧ 0 < log (log (m : ℝ)) ∧
      log (largestPrime m : ℝ) / 2 ≤ log (log (m : ℝ)) ∧
      log (log (m : ℝ)) ≤ 2 * log (largestPrime m : ℝ) := by
  let S := {v : ℕ × ℝ // 2 ≤ v.1 ∧ 0 < v.2 ∧ FullRecord v.1 v.2}
  let m : S → ℕ := fun x => x.1.1
  let mu : S → ℝ := fun x => x.1.2
  let R : S → ℝ := fun x => largestPrime (m x)
  let L : S → ℝ := fun x => log (R x)
  let M : S → ℝ := fun x => log (log (m x : ℝ))
  let l : Filter S := comap R atTop
  have hR : Tendsto R l atTop := tendsto_comap
  have hL : Tendsto L l atTop := tendsto_log_atTop.comp hR
  have hm (x : S) : 2 ≤ m x := x.2.1
  have hmu (x : S) : 0 < mu x := x.2.2.1
  have hrec (x : S) : FullRecord (m x) (mu x) := x.2.2.2
  have hmass := FullArithmeticCorrectionSecondOrder.record_mass_limits
    m mu hm hmu hrec hR
  have hr : Tendsto (fun x => log (m x : ℝ) / R x) l (𝓝 1) := hmass.2.2.1
  have hlogr : Tendsto (fun x => log (log (m x : ℝ) / R x)) l (𝓝 0) := by
    simpa only [log_one, Function.comp_def] using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hr
  have hz : Tendsto (fun x => log (log (m x : ℝ) / R x) / L x) l (𝓝 0) :=
    hlogr.div_atTop hL
  have hratio : Tendsto (fun x => M x / L x) l (𝓝 1) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : S => (1 : ℝ)) l (𝓝 1)).add hz
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hR.eventually_gt_atTop 1] with x hx
    have hlogm : 0 < log (m x : ℝ) :=
      log_pos (by exact_mod_cast (show 1 < m x from lt_of_lt_of_le (by norm_num) (hm x)))
    dsimp [M, L]
    rw [log_div hlogm.ne' (by linarith : R x ≠ 0)]
    field_simp [(log_pos hx).ne']
    <;> ring
  have hall : ∀ᶠ x in l,
      1 ≤ L x ∧ 0 < M x ∧ L x / 2 ≤ M x ∧ M x ≤ 2 * L x := by
    filter_upwards [hL.eventually_ge_atTop 1,
      hratio.eventually (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1)),
      hratio.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))]
      with x hLx hlo hhi
    have hL0 : 0 < L x := by linarith
    have hlo' := (lt_div_iff₀ hL0).mp hlo
    have hhi' := (div_lt_iff₀ hL0).mp hhi
    exact ⟨hLx, by linarith, by linarith, hhi'.le⟩
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp hall)
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), ?_⟩
  intro n hn nu hnu hrecord hlarge
  let x : S := ⟨(n, nu), hn, hnu, hrecord⟩
  exact hT (largestPrime n : ℝ) ((le_max_left T 2).trans hlarge) x rfl

/- A complete mass error of size K log(P) P^(-19/640), once derived by the
simultaneous selection below, is o(mesh4). This has a proved real threshold
before all records; it is not an assumed small-slack producer. -/
private theorem eventual_mass_error_absorption (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ X : ℝ in atTop,
      0 < mesh4 X ∧ K * log X * X ^ (-(19 / 640 : ℝ)) ≤ mesh4 X / 2 := by
  have hmesh := actual_stencil_limits.2.2.2
  have ha : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hc : 0 < 6 * log (2 : ℝ) ^ 4 := by positivity
  have hsmall : Tendsto (fun X : ℝ => log X ^ 5 / X ^ (19 / 640 : ℝ))
      atTop (𝓝 0) := by
    simpa only [rpow_natCast] using
      (_root_.isLittleO_log_rpow_rpow_atTop (5 : ℕ) (by norm_num : (0 : ℝ) < 19 / 640)).tendsto_div_nhds_zero
  have hp : ∀ᶠ X : ℝ in atTop, 0 < mesh4 X := by
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hmesh.eventually (eventually_gt_nhds hc)] with X hX hmeshX
    exact (mul_pos_iff_of_pos_left (pow_pos (log_pos hX) 4)).mp hmeshX
  have hratio : Tendsto
      (fun X : ℝ => (K * log X * X ^ (-(19 / 640 : ℝ))) / mesh4 X)
      atTop (𝓝 0) := by
    have hh := (hsmall.const_mul K).div hmesh hc.ne'
    simp only [mul_zero, zero_div] at hh
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ), hp] with X hX hmeshX
    dsimp only [Pi.div_apply]
    rw [rpow_neg (by linarith : 0 ≤ X)]
    field_simp [(log_pos hX).ne', hmeshX.ne',
      (rpow_pos_of_pos (by linarith : 0 < X) (19 / 640 : ℝ)).ne']
    <;> ring
  filter_upwards [hp, hratio.eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with X hX hr
  exact ⟨hX, by linarith [(div_le_iff₀ hX).mp hr.le]⟩

/- Pointwise estimates retain the original prime and its original layer index.
The three analytic declarations below are reused by visibility-only exposure;
no beta derivative or boundary-localization proof is duplicated. -/
private theorem interval_log_distance {Q w x : ℝ} (hQ : 4 ≤ Q)
    (hw : 0 ≤ w) (hwQ : w ≤ Q / 2)
    (hxlo : Q - w ≤ x) (hxhi : x ≤ Q + w) :
    |log x - log Q| ≤ 2 * w / Q := by
  have hQ0 : 0 < Q := by linarith
  have ha : 0 < Q / 2 := by positivity
  have hx : Q / 2 ≤ x := by linarith
  have hd : ∀ t ∈ Set.Ici (Q / 2), HasDerivAt log (t⁻¹) t := by
    intro t ht
    exact hasDerivAt_log (ne_of_gt (ha.trans_le ht))
  have hb : ∀ t ∈ Set.Ici (Q / 2), ‖t⁻¹‖ ≤ 2 / Q := by
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (ha.le.trans ht))]
    have hh := one_div_le_one_div_of_le ha ht
    calc
      _ = 1 / t := by simp
      _ ≤ 1 / (Q / 2) := hh
      _ = 2 / Q := by field_simp [hQ0.ne'] <;> ring
  have hv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t ht => (hd t ht).hasDerivWithinAt) hb
    (convex_Ici (Q / 2)) (by linarith : Q / 2 ≤ Q) hx
  have habs : |x - Q| ≤ w := abs_le.mpr ⟨by linarith, by linarith⟩
  have hh : |log x - log Q| ≤ (2 / Q) * |x - Q| := by
    simpa only [Real.norm_eq_abs] using hv
  calc
    _ ≤ (2 / Q) * |x - Q| := hh
    _ ≤ (2 / Q) * w := mul_le_mul_of_nonneg_left habs (by positivity)
    _ = _ := by ring

private theorem width_power_transfer {j : ℕ} (hj : 1 ≤ j)
    {R Q : ℝ} (hR : 1 ≤ R) (hQ : 0 < Q) (hRQ : R ≤ Q ^ j) :
    Q ^ (bhpExponent - 1) ≤ R ^ (-priceExponent j) := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hgamma : 0 < priceExponent j := by dsimp [priceExponent]; positivity
  have hh := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < R) hRQ
    (neg_nonpos.mpr hgamma.le)
  have he : (Q ^ j) ^ (-priceExponent j) = Q ^ (bhpExponent - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hQ.le]
    congr 1
    dsimp [priceExponent, bhpExponent]
    field_simp [hj0.ne'] <;> ring
  rwa [he] at hh

private theorem pointwise_boundary_estimates {j : ℕ} (hj : 1 ≤ j)
    {R Q W A H root : ℝ} (hR : 4 ≤ R) (hQ : 4 ≤ Q) (hQR : Q ≤ R)
    (hRQ : R ≤ Q ^ j) (hW : 0 ≤ W) (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hlog : log R / (4 * (j : ℝ)) ≤ log (Q / 2))
    (hwidth : W * Q ^ bhpExponent ≤ Q / 2)
    (hband : |beta j Q - beta 1 R| ≤ A * beta 1 R * R ^ (-priceExponent j))
    (hroot : |(j : ℝ) * log Q - root| ≤ H * R ^ (-priceExponent j)) :
    ∀ p : ℕ, p.Prime → Q - W * Q ^ bhpExponent ≤ (p : ℝ) →
      (p : ℝ) ≤ Q + W * Q ^ bhpExponent →
      |log (p : ℝ) - root / (j : ℝ)| ≤
        (2 * W + H) * R ^ (-priceExponent j) ∧
      |(goldenLayerMarginal p j - beta 1 R) * log (p : ℝ)| ≤
        (2 * (A + 2 * W *
          (((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))))) *
          beta 1 R * log R * R ^ (-priceExponent j) := by
  intro p hp hlo hhi
  let t := R ^ (-priceExponent j)
  let B := ((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))
  have hR0 : 0 < R := by linarith
  have hQ0 : 0 < Q := by linarith
  have hL : 0 < log R := log_pos (by linarith)
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast (show 0 < j by omega)
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have ht : 0 ≤ t := rpow_nonneg hR0.le _
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlambda : 0 < beta 1 R := beta_pos (by linarith) (by norm_num)
  have hw : 0 ≤ W * Q ^ bhpExponent := by positivity
  have hpQ : Q / 2 ≤ (p : ℝ) := by linarith
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hplog : 0 ≤ log (p : ℝ) := log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hpR2 : (p : ℝ) ≤ R ^ 2 := by nlinarith [sq_nonneg (R - 1)]
  have hlogp : log (p : ℝ) ≤ 2 * log R := by
    have hh := log_le_log hp0 hpR2
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hpow := width_power_transfer hj (by linarith : 1 ≤ R) hQ0 hRQ
  have hwidthRatio : W * Q ^ bhpExponent / Q ≤ W * t := by
    have he : Q ^ bhpExponent / Q = Q ^ (bhpExponent - 1) := by
      rw [Real.rpow_sub hQ0, Real.rpow_one]
    calc
      _ = W * Q ^ (bhpExponent - 1) := by rw [← he]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow hW
  have hlogdist : |log (p : ℝ) - log Q| ≤ 2 * W * t := by
    calc
      _ ≤ 2 * (W * Q ^ bhpExponent) / Q := interval_log_distance hQ hw hwidth hlo hhi
      _ = 2 * (W * Q ^ bhpExponent / Q) := by ring
      _ ≤ 2 * (W * t) := mul_le_mul_of_nonneg_left hwidthRatio (by norm_num)
      _ = _ := by ring
  have hroot' : |log Q - root / (j : ℝ)| ≤ H * t := by
    have he : (j : ℝ) * (log Q - root / (j : ℝ)) = (j : ℝ) * log Q - root := by
      field_simp [hj0.ne'] <;> ring
    have hh : (j : ℝ) * |log Q - root / (j : ℝ)| ≤ H * t := by
      calc
        _ = |(j : ℝ) * (log Q - root / (j : ℝ))| := by
          rw [abs_mul, abs_of_pos hj0]
        _ ≤ H * t := by rw [he]; exact hroot
    have hmul := mul_le_mul_of_nonneg_right hj1
      (abs_nonneg (log Q - root / (j : ℝ)))
    have hmul' : |log Q - root / (j : ℝ)| ≤
        (j : ℝ) * |log Q - root / (j : ℝ)| := by simpa only [one_mul] using hmul
    exact hmul'.trans hh
  refine ⟨(abs_sub_le (log (p : ℝ)) (log Q) (root / (j : ℝ))).trans
    (by nlinarith), ?_⟩
  have hLip := ActualBoundaryPriceCandidate.priceLip_half_bound j
    (by linarith : 1 < R) hQ (by positivity : 0 < 4 * (j : ℝ)) hlog
  have hbase := ActualBoundaryPriceCandidate.first_beta_lower (by linarith : 2 ≤ R)
  have hnorm : ActualBoundaryPriceCandidate.priceLip j (Q / 2) *
      (W * Q ^ bhpExponent) ≤ (2 * W * B) * beta 1 R * t := by
    have he : Q ^ bhpExponent = Q ^ (bhpExponent - 1) * Q := by
      calc
        _ = Q ^ ((bhpExponent - 1) + 1) := by congr 1 <;> ring
        _ = _ := by rw [Real.rpow_add hQ0, Real.rpow_one]
    calc
      _ ≤ (B / (Q ^ (j + 1) * log R)) * (W * Q ^ bhpExponent) :=
        mul_le_mul_of_nonneg_right hLip hw
      _ = (W * B) * (1 / (Q ^ j * log R)) * Q ^ (bhpExponent - 1) := by
        rw [he, pow_succ]
        field_simp [hQ0.ne', hL.ne'] <;> ring
      _ ≤ (W * B) * (1 / (R * log R)) * t := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (one_div_le_one_div_of_le (by positivity)
              (mul_le_mul_of_nonneg_right hRQ hL.le)) (mul_nonneg hW hB)
        · exact hpow
        · positivity
        · positivity
      _ ≤ (W * B) * (2 * beta 1 R) * t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbase (mul_nonneg hW hB)) ht
      _ = _ := by ring
  have hLip0 : 0 ≤ ActualBoundaryPriceCandidate.priceLip j (Q / 2) := by
    unfold ActualBoundaryPriceCandidate.priceLip
    have hlogQ : 0 < log (Q / 2) := log_pos (by linarith)
    positivity
  have hdist : |(p : ℝ) - Q| ≤ W * Q ^ bhpExponent :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hvar := (ActualBoundaryPriceCandidate.price_variation hj
    (by linarith : 2 ≤ Q / 2) (by linarith : Q / 2 ≤ Q) hpQ).trans
      (mul_le_mul_of_nonneg_left hdist hLip0)
  have hprice : |beta j (p : ℝ) - beta 1 R| ≤ (A + 2 * W * B) * beta 1 R * t :=
    (abs_sub_le (beta j (p : ℝ)) (beta j Q) (beta 1 R)).trans (by nlinarith)
  rw [← beta_nat hp hj, abs_mul, abs_of_nonneg hplog]
  calc
    _ ≤ ((A + 2 * W * B) * beta 1 R * t) * (2 * log R) :=
      mul_le_mul hprice hlogp hplog (by positivity)
    _ = _ := by dsimp [B]; ring

private def modeIndex (k : Fin 5) : ℕ := 2 ^ k.val
private def countIndex (k : Fin 5) : ℕ := if k = 0 then 16 else modeIndex k
private def rootLog (R : ℝ) (k : Fin 5) : ℝ :=
  if k = 0 then log R else log (cutoff (modeIndex k) (beta 1 R))

private theorem mode_index_bounds (k : Fin 5) :
    1 ≤ modeIndex k ∧ modeIndex k ≤ 16 ∧ 2 ≤ countIndex k ∧
      19 / 640 ≤ priceExponent (modeIndex k) := by
  fin_cases k <;> norm_num [modeIndex, countIndex, priceExponent]

/- The two scale fields are deliberately present even though original exponent
labels separate all the other pairs. In particular exponent 1 is shared. -/
private def ModeAtom (m : ℕ) (k : Fin 5) (up : Bool) (p : ℕ) : Prop :=
  p.Prime ∧ 2 < p ∧
    m.factorization p + (if up then 1 else 0) = modeIndex k ∧
    (k = 0 → (largestPrime m : ℝ) / 2 ≤ (p : ℝ)) ∧
    (k = 1 → (p : ℝ) ≤ 3 * (layerPrime m 2 : ℝ) / 2)

private def ModeEstimate (A : ℝ) (R : ℝ) (k : Fin 5) (p : ℕ) : Prop :=
  |log (p : ℝ) - rootLog R k| ≤ A * R ^ (-priceExponent (modeIndex k)) ∧
    |(goldenLayerMarginal p (modeIndex k) - beta 1 R) * log (p : ℝ)| ≤
      A * beta 1 R * log R * R ^ (-priceExponent (modeIndex k))

private theorem root_mass_coordinate (k : Fin 5) (hk : k ≠ 0) (R : ℝ) :
    rootMasses R k = log R + actualOffset (modeIndex k) R := by
  fin_cases k <;> simp_all [rootMasses, modeIndex]

private theorem root_log_mass (k : Fin 5) (R : ℝ) :
    rootLog R k = rootMasses R k / (modeIndex k : ℝ) := by
  by_cases hk : k = 0
  · subst k; simp [rootLog, rootMasses, modeIndex]
  · have hj0 : (modeIndex k : ℝ) ≠ 0 := by
      have hj := (mode_index_bounds k).1
      exact_mod_cast (show modeIndex k ≠ 0 by omega)
    rw [rootLog, if_neg hk, root_mass_coordinate k hk R]
    dsimp [actualOffset]
    field_simp [hj0] <;> ring

/- Fixed-mode constants and thresholds precede all original integers and prices.
Both pools are actual original-boundary pools; no ideal exponent is supplied. -/
private theorem uniform_mode_inventory
    (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount) (k : Fin 5) :
    ∃ A T : ℝ, 0 < A ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) → ∃ Lo Hi : Finset ℕ,
          Lo.card = comparisonCount (countIndex k) (largestPrime m) ∧
          Hi.card = comparisonCount (countIndex k) (largestPrime m) ∧
          (∀ p ∈ Lo, ModeAtom m k false p ∧ ModeEstimate A (largestPrime m) k p) ∧
          (∀ p ∈ Hi, ModeAtom m k true p ∧ ModeEstimate A (largestPrime m) k p) := by
  classical
  by_cases hk : k = 0
  · subst k
    obtain ⟨W, Ti, hW, hTi, hi⟩ := actual_first_inventory hcount
    let A : ℝ := 1 + 2 * W + 2 * (2 * W * ((1 + 2) * 2 ^ (1 + 1) * (4 * 1)))
    refine ⟨A, max 4 Ti, by dsimp [A]; positivity,
      lt_of_lt_of_le (by norm_num) (le_max_left _ _), ?_⟩
    intro m hm mu hmu hrecord hlarge
    let R : ℝ := largestPrime m
    have hR4 : 4 ≤ R := (le_max_left 4 Ti).trans hlarge
    obtain ⟨Lo, Hi, hLo, hHi, _, hw, hlo, hhi⟩ :=
      hi m hm mu hmu hrecord ((le_max_right 4 Ti).trans hlarge)
    have hlog : log R / (4 * (1 : ℝ)) ≤ log (R / 2) := by
      have hh := log_le_log (by norm_num : (0 : ℝ) < 4) hR4
      have he : log (4 : ℝ) = 2 * log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      rw [he] at hh
      rw [log_div (by linarith : R ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
      linarith [log_pos (by norm_num : (1 : ℝ) < 2)]
    have hpoint := pointwise_boundary_estimates (j := 1) (root := log R) (by norm_num)
      hR4 hR4 (le_refl R) (by simp) hW.le (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
      (by simpa only [Nat.cast_one] using hlog) hw (by simp) (by simp)
    have pack (p : ℕ) (hp : p.Prime) (hp2 : 2 < p)
        (hv : m.factorization p + (if false then 1 else 0) = 1)
        (hl : R - W * R ^ bhpExponent ≤ (p : ℝ))
        (hu : (p : ℝ) ≤ R + W * R ^ bhpExponent) :
        ModeAtom m 0 false p ∧ ModeEstimate A R 0 p := by
      have hh := hpoint p hp hl hu
      have ht : 0 ≤ R ^ (-priceExponent 1) := by positivity
      have hlambda : 0 ≤ beta 1 R := (beta_pos (by linarith) (by norm_num)).le
      have hL : 0 ≤ log R := log_nonneg (by linarith)
      refine ⟨⟨hp, hp2, by simpa [modeIndex] using hv, ?_, by simp⟩, ?_⟩
      · intro _; dsimp [R] at *; linarith
      · dsimp [ModeEstimate, rootLog, rootMasses, modeIndex]
        norm_num at hh ⊢
        constructor
        · exact hh.1.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; nlinarith) ht)
        · have hconst : 2 * (2 * W * 48) ≤ A := by dsimp [A]; nlinarith
          exact hh.2.trans (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hconst hlambda) hL) ht)
    refine ⟨Lo, Hi, by simpa [countIndex] using hLo,
      by simpa [countIndex] using hHi, ?_, ?_⟩
    · intro p hp
      obtain ⟨hpP, hp2, hv, hl, hu⟩ := hlo p hp
      exact pack p hpP hp2 (by simpa using hv) hl (hu.trans (le_add_of_nonneg_right (by positivity)))
    · intro p hp
      obtain ⟨hpP, hp2, hv, hl, hu⟩ := hhi p hp
      have hh := hpoint p hpP (by linarith [show 0 ≤ W * R ^ bhpExponent by positivity]) hu
      have ht : 0 ≤ R ^ (-priceExponent 1) := by positivity
      have hlambda : 0 ≤ beta 1 R := (beta_pos (by linarith) (by norm_num)).le
      have hL : 0 ≤ log R := log_nonneg (by linarith)
      refine ⟨⟨hpP, hp2, by simpa [modeIndex, hv], by intro _; linarith, by simp⟩, ?_⟩
      dsimp [ModeEstimate, rootLog, rootMasses, modeIndex]
      norm_num at hh ⊢
      constructor
      · exact hh.1.trans (mul_le_mul_of_nonneg_right (by dsimp [A]; nlinarith) ht)
      · have hconst : 2 * (2 * W * 48) ≤ A := by dsimp [A]; nlinarith
        exact hh.2.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hconst hlambda) hL) ht)
  · let j := modeIndex k
    have hj : 2 ≤ j := by fin_cases k <;> simp_all [j, modeIndex]
    obtain ⟨Ai, W, Ti, hAi, hW, hTi, hi⟩ := actual_high_inventory hgap hcount j hj
    obtain ⟨H, Tr, hH, hTr, hr⟩ := uniform_boundary_root_log_transfer hgap hcount j hj
    obtain ⟨Tg, hTg, hg⟩ := ActualBoundaryPriceCandidate.uniform_coarse_geometry j hj
    let B : ℝ := ((j : ℝ) + 2) * (2 : ℝ) ^ (j + 1) * (4 * (j : ℝ))
    let A : ℝ := 1 + (2 * W + H) + 2 * (Ai + 2 * W * B)
    let T := max Ti (max Tr Tg)
    refine ⟨A, T, by dsimp [A, B]; positivity,
      lt_of_lt_of_le hTi (le_max_left _ _), ?_⟩
    intro m hm mu hmu hrecord hlarge
    let R : ℝ := largestPrime m
    let Q : ℝ := layerPrime m j
    have hTiR : Ti ≤ R := (le_max_left Ti (max Tr Tg)).trans hlarge
    have hTrR : Tr ≤ R := (le_max_left Tr Tg).trans ((le_max_right Ti _).trans hlarge)
    have hTgR : Tg ≤ R := (le_max_right Tr Tg).trans ((le_max_right Ti _).trans hlarge)
    obtain ⟨Lo, Hi, hLo, hHi, _, hRQ, hw, hband, hlo, hhi⟩ :=
      hi m hm mu hmu hrecord hTiR
    obtain ⟨hR4, hQ4, hQR, _, hlog⟩ := hg m hm mu hmu hrecord hTgR
    have hroot := hr m hm mu hmu hrecord hTrR
    rw [← root_mass_coordinate k hk R] at hroot
    have hpoint := pointwise_boundary_estimates (by omega : 1 ≤ j) hR4 hQ4
      (by linarith : Q ≤ R) hRQ hW.le hAi.le hH.le hlog hw hband hroot
    have pack (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) (up : Bool)
        (hv : m.factorization p + (if up then 1 else 0) = j)
        (hl : Q - W * Q ^ bhpExponent ≤ (p : ℝ))
        (hu : (p : ℝ) ≤ Q + W * Q ^ bhpExponent) :
        ModeAtom m k up p ∧ ModeEstimate A R k p := by
      obtain ⟨hplog, hpfee⟩ := hpoint p hp hl hu
      have ht : 0 ≤ R ^ (-priceExponent j) := by positivity
      have hlambda : 0 ≤ beta 1 R := (beta_pos (by linarith) (by norm_num)).le
      have hL : 0 ≤ log R := log_nonneg (by linarith)
      have hB : 0 ≤ B := by dsimp [B]; positivity
      refine ⟨⟨hp, hp2, hv, by simp [hk], ?_⟩, ?_⟩
      · intro hk1
        have hj2 : j = 2 := by simp [j, modeIndex, hk1]
        have hQeq : Q = (layerPrime m 2 : ℝ) := by dsimp only [Q]; rw [hj2]
        rw [← hQeq]
        linarith
      · constructor
        · rw [root_log_mass k R]
          exact hplog.trans (mul_le_mul_of_nonneg_right
            (by dsimp only [A]; nlinarith [mul_nonneg hW.le hB]) ht)
        · exact hpfee.trans (by
            have hconst : 2 * (Ai + 2 * W * B) ≤ A := by
              dsimp [A]; linarith [mul_pos (by norm_num : (0 : ℝ) < 2) hW]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right hconst hlambda) hL) ht)
    refine ⟨Lo, Hi, by simpa [countIndex, hk, j] using hLo,
      by simpa [countIndex, hk, j] using hHi, ?_, ?_⟩
    · intro p hp
      obtain ⟨hpP, hp2, hv, hl, hu⟩ := hlo p hp
      exact pack p hpP hp2 false (by simpa using hv) hl
        (hu.trans (by
          change Q ≤ Q + W * Q ^ bhpExponent
          exact le_add_of_nonneg_right (by positivity)))
    · intro p hp
      obtain ⟨hpP, hp2, hv, hl, hu⟩ := hhi p hp
      exact pack p hpP hp2 true (by change m.factorization p + 1 = j; omega)
        (by
          change Q - W * Q ^ bhpExponent ≤ (p : ℝ)
          have hln : Q < (p : ℝ) := hl
          linarith [show 0 ≤ W * Q ^ bhpExponent by positivity]) hu

private theorem uniform_five_mode_pools
    (hgap : BHPMaximumGap) (hcount : BHPShortIntervalCount) :
    ∃ A T : ℝ, 0 < A ∧ 0 < T ∧
      ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
        T ≤ (largestPrime m : ℝ) →
        (layerPrime m 2 : ℝ) ≤ (largestPrime m : ℝ) / 8 ∧
        ∃ Lo Hi : Fin 5 → Finset ℕ, ∀ k : Fin 5,
          (Lo k).card = comparisonCount (countIndex k) (largestPrime m) ∧
          (Hi k).card = comparisonCount (countIndex k) (largestPrime m) ∧
          (∀ p ∈ Lo k, ModeAtom m k false p ∧ ModeEstimate A (largestPrime m) k p) ∧
          (∀ p ∈ Hi k, ModeAtom m k true p ∧ ModeEstimate A (largestPrime m) k p) := by
  classical
  choose a t ha ht hpool using uniform_mode_inventory hgap hcount
  obtain ⟨Tg, hTg, hg⟩ := ActualBoundaryPriceCandidate.uniform_coarse_geometry 2 (by norm_num)
  let A := 1 + ∑ k : Fin 5, a k
  let T := 1 + Tg + ∑ k : Fin 5, t k
  have hsumA : 0 ≤ ∑ k : Fin 5, a k := sum_nonneg (fun k _ => (ha k).le)
  have hsumT : 0 ≤ ∑ k : Fin 5, t k := sum_nonneg (fun k _ => (ht k).le)
  have haA (k : Fin 5) : a k ≤ A := by
    have hh := single_le_sum (s := (univ : Finset (Fin 5)))
      (fun i _ => (ha i).le) (mem_univ k)
    dsimp [A]; linarith
  have htT (k : Fin 5) : t k ≤ T := by
    have hh := single_le_sum (s := (univ : Finset (Fin 5)))
      (fun i _ => (ht i).le) (mem_univ k)
    dsimp [T]; linarith
  refine ⟨A, T, by dsimp [A]; linarith, by dsimp [T]; linarith, ?_⟩
  intro m hm mu hmu hrecord hlarge
  have hTg : Tg ≤ (largestPrime m : ℝ) := by dsimp [T] at hlarge; linarith
  have hQ8 := (hg m hm mu hmu hrecord hTg).2.2.1
  have hR4 := (hg m hm mu hmu hrecord hTg).1
  have hR0 : (0 : ℝ) < largestPrime m := by linarith
  have hL : 0 ≤ log (largestPrime m : ℝ) := log_nonneg (by linarith)
  have hlam : 0 ≤ beta 1 (largestPrime m : ℝ) := (beta_pos (by linarith) (by norm_num)).le
  choose Lo Hi hLo hHi hlo hhi using
    (fun k : Fin 5 => hpool k m hm mu hmu hrecord ((htT k).trans hlarge))
  refine ⟨hQ8, Lo, Hi, ?_⟩
  intro k
  have liftEstimate (p : ℕ) (hp : ModeEstimate (a k) (largestPrime m) k p) :
      ModeEstimate A (largestPrime m) k p := by
    have he : 0 ≤ (largestPrime m : ℝ) ^ (-priceExponent (modeIndex k)) := by positivity
    exact ⟨hp.1.trans (mul_le_mul_of_nonneg_right (haA k) he),
      hp.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (haA k) hlam) hL) he)⟩
  exact ⟨hLo k, hHi k,
    fun p hp => ⟨(hlo k p hp).1, liftEstimate p (hlo k p hp).2⟩,
    fun p hp => ⟨(hhi k p hp).1, liftEstimate p (hhi k p hp).2⟩⟩

private theorem uniform_selection_capacity (B : ℝ) :
    ∀ᶠ R : ℝ in atTop, ∀ k : Fin 5, ∀ z : ℤ,
      |(z : ℝ)| ≤ B * log R →
        modeIndex k * z.natAbs ≤ comparisonCount (countIndex k) R := by
  have hone (k : Fin 5) : ∀ᶠ R : ℝ in atTop,
      (modeIndex k : ℝ) * B * log R ≤ R ^ priceExponent (countIndex k) := by
    have hgamma : 0 < priceExponent (countIndex k) := by
      have hj := (mode_index_bounds k).2.2.1
      have hj0 : (0 : ℝ) < countIndex k := by
        exact_mod_cast (show 0 < countIndex k by omega)
      dsimp [priceExponent]; positivity
    have hlim : Tendsto (fun R : ℝ => log R / R ^ priceExponent (countIndex k))
        atTop (𝓝 0) := by
      simpa only [rpow_one] using
        (_root_.isLittleO_log_rpow_rpow_atTop 1 hgamma).tendsto_div_nhds_zero
    have hh := hlim.const_mul ((modeIndex k : ℝ) * B)
    simp only [mul_zero] at hh
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hh.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))]
      with R hR hbound
    have hp : 0 < R ^ priceExponent (countIndex k) := rpow_pos_of_pos (by linarith) _
    have he : (modeIndex k : ℝ) * B * (log R / R ^ priceExponent (countIndex k)) =
        ((modeIndex k : ℝ) * B * log R) / R ^ priceExponent (countIndex k) := by ring
    rw [he] at hbound
    exact ((div_lt_one hp).mp hbound).le
  filter_upwards [Filter.eventually_all.mpr hone] with R hR k z hz
  have habs : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hcard : ((modeIndex k * z.natAbs : ℕ) : ℝ) ≤
      (comparisonCount (countIndex k) R : ℝ) := by
    calc
      _ = (modeIndex k : ℝ) * |(z : ℝ)| := by rw [Nat.cast_mul, habs]
      _ ≤ (modeIndex k : ℝ) * B * log R := by
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _)
      _ ≤ R ^ priceExponent (countIndex k) := hR k
      _ ≤ _ := Nat.le_ceil _
  exact_mod_cast hcard

private theorem mode_atoms_separate {m : ℕ} {R : ℝ} (hR : R = largestPrime m)
    (hRpos : 0 < R) (hQ8 : (layerPrime m 2 : ℝ) ≤ R / 8)
    {k l : Fin 5} (hkl : k ≠ l) {up vp : Bool} {p : ℕ}
    (hp : ModeAtom m k up p) (hq : ModeAtom m l vp p) : False := by
  obtain ⟨_, _, hvk, hk0, hk1⟩ := hp
  obtain ⟨_, _, hvl, hl0, hl1⟩ := hq
  have hscale : 3 * (layerPrime m 2 : ℝ) / 2 < (largestPrime m : ℝ) / 2 := by
    rw [← hR]; linarith
  generalize hval : m.factorization p = a at hvk hvl
  fin_cases k <;> fin_cases l <;> cases up <;> cases vp
  all_goals try exact (hkl rfl).elim
  all_goals norm_num [modeIndex] at hvk hvl
  all_goals first
    | omega
    | (norm_num at hk0 hk1 hl0 hl1 <;> linarith)

private theorem finite_sum_point_error (S : Finset ℕ) (f : ℕ → ℝ)
    (a E : ℝ) (h : ∀ p ∈ S, |f p - a| ≤ E) :
    |(∑ p ∈ S, f p) - (S.card : ℝ) * a| ≤ (S.card : ℝ) * E := by
  calc
    _ = |∑ p ∈ S, (f p - a)| := by
      congr 1
      simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
    _ ≤ ∑ p ∈ S, |f p - a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, E := sum_le_sum h
    _ = _ := by simp

private def positiveModes (v : Fin 5 → ℤ) : Finset (Fin 5) :=
  univ.filter (fun k => 0 ≤ v k)
private def negativeModes (v : Fin 5 → ℤ) : Finset (Fin 5) :=
  univ.filter (fun k => v k < 0)

/- G2–G4 are one finite construction. Each chosen S_k has exactly j_k*|v_k|
DISTINCT original primes. Both signed unions, every log error, and every
insertion/deletion fee are summed before taking the common exponent. -/
private theorem finite_five_mode_selection {m : ℕ} (hm : 2 ≤ m)
    {R A B : ℝ} (hRdef : R = largestPrime m) (hR : 4 ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hQ8 : (layerPrime m 2 : ℝ) ≤ R / 8)
    (Lo Hi : Fin 5 → Finset ℕ)
    (hpools : ∀ k : Fin 5,
      (Lo k).card = comparisonCount (countIndex k) R ∧
      (Hi k).card = comparisonCount (countIndex k) R ∧
      (∀ p ∈ Lo k, ModeAtom m k false p ∧ ModeEstimate A R k p) ∧
      (∀ p ∈ Hi k, ModeAtom m k true p ∧ ModeEstimate A R k p))
    (v : Fin 5 → ℤ) (hv : ∀ k, |(v k : ℝ)| ≤ B * log R)
    (hcap : ∀ k, modeIndex k * (v k).natAbs ≤ comparisonCount (countIndex k) R) :
    ∃ D U : Finset ℕ, Disjoint D U ∧
      (∀ p ∈ D, p.Prime ∧ 2 < p ∧ p ∣ m) ∧
      (∀ p ∈ U, p.Prime ∧ 2 < p) ∧
      |(logMass U - logMass D) - ∑ k : Fin 5, (v k : ℝ) * rootMasses R k| ≤
        (80 * A * B) * log R * R ^ (-(19 / 640 : ℝ)) ∧
      |auxiliaryGain (beta 1 R) m D U| ≤
        (80 * A * B) * beta 1 R * log R ^ 2 * R ^ (-(19 / 640 : ℝ)) := by
  classical
  have choose_mode (k : Fin 5) : ∃ S : Finset ℕ,
      S.card = modeIndex k * (v k).natAbs ∧
      ∀ p ∈ S, ModeAtom m k (decide (0 ≤ v k)) p ∧ ModeEstimate A R k p := by
    by_cases hk : 0 ≤ v k
    · obtain ⟨S, hS, hc⟩ := exists_subset_card_eq ((hcap k).trans_eq (hpools k).2.1.symm)
      exact ⟨S, hc, fun p hp => by simpa [hk] using (hpools k).2.2.2 p (hS hp)⟩
    · obtain ⟨S, hS, hc⟩ := exists_subset_card_eq ((hcap k).trans_eq (hpools k).1.symm)
      exact ⟨S, hc, fun p hp => by simpa [hk] using (hpools k).2.2.1 p (hS hp)⟩
  choose S hSc hS using choose_mode
  have hpair : Pairwise (fun k l : Fin 5 => Disjoint (S k) (S l)) := by
    intro k l hkl
    exact disjoint_left.mpr (fun p hp hq =>
      mode_atoms_separate hRdef (by linarith) hQ8 hkl (hS k p hp).1 (hS l p hq).1)
  let D := (negativeModes v).biUnion S
  let U := (positiveModes v).biUnion S
  have hDmem {p : ℕ} : p ∈ D ↔ ∃ k, v k < 0 ∧ p ∈ S k := by
    simp [D, negativeModes]
  have hUmem {p : ℕ} : p ∈ U ↔ ∃ k, 0 ≤ v k ∧ p ∈ S k := by
    simp [U, positiveModes]
  have hDU : Disjoint D U := disjoint_left.mpr (by
    intro p hp hq
    obtain ⟨k, hk, hpk⟩ := hDmem.mp hp
    obtain ⟨l, hl, hpl⟩ := hUmem.mp hq
    by_cases hkl : k = l
    · subst l; omega
    · exact disjoint_left.mp (hpair hkl) hpk hpl)
  have hDlegal : ∀ p ∈ D, p.Prime ∧ 2 < p ∧ p ∣ m := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := hDmem.mp hp
    have ha := (hS k p hpk).1
    have hvp : m.factorization p = modeIndex k := by
      simpa [ModeAtom, show ¬0 ≤ v k by omega] using ha.2.2.1
    refine ⟨ha.1, ha.2.1, ?_⟩
    exact (ha.1.dvd_iff_one_le_factorization (by omega : m ≠ 0)).mpr
      (by rw [hvp]; exact (mode_index_bounds k).1)
  have hUlegal : ∀ p ∈ U, p.Prime ∧ 2 < p := by
    intro p hp
    obtain ⟨k, hk, hpk⟩ := hUmem.mp hp
    exact ⟨(hS k p hpk).1.1, (hS k p hpk).1.2.1⟩
  have hsumUnion (I : Finset (Fin 5)) (f : ℕ → ℝ) :
      (∑ p ∈ I.biUnion S, f p) = ∑ k ∈ I, ∑ p ∈ S k, f p := by
    exact sum_biUnion (fun k _ l _ hkl => hpair hkl)
  have habs (k : Fin 5) : (((v k).natAbs : ℕ) : ℝ) = |(v k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hcard (k : Fin 5) : ((S k).card : ℝ) = (modeIndex k : ℝ) * |(v k : ℝ)| := by
    rw [hSc, Nat.cast_mul, habs]
  have hR0 : 0 < R := by linarith
  have hL : 0 ≤ log R := log_nonneg (by linarith)
  have hlam : 0 ≤ beta 1 R := (beta_pos (by linarith) (by norm_num)).le
  have ht : 0 ≤ R ^ (-(19 / 640 : ℝ)) := by positivity
  have htexp (k : Fin 5) :
      R ^ (-priceExponent (modeIndex k)) ≤ R ^ (-(19 / 640 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith)
      (neg_le_neg (mode_index_bounds k).2.2.2)
  have hcardBound (k : Fin 5) : ((S k).card : ℝ) ≤ 16 * B * log R := by
    rw [hcard]
    calc
      _ ≤ (modeIndex k : ℝ) * (B * log R) :=
        mul_le_mul_of_nonneg_left (hv k) (Nat.cast_nonneg _)
      _ ≤ 16 * B * log R := by
        have hj : (modeIndex k : ℝ) ≤ 16 := by exact_mod_cast (mode_index_bounds k).2.1
        simpa only [mul_assoc] using
          mul_le_mul_of_nonneg_right hj (mul_nonneg hB hL)
  let signedMass : Fin 5 → ℝ := fun k => if 0 ≤ v k then logMass (S k) else -logMass (S k)
  let signedFee : Fin 5 → ℝ := fun k =>
    if 0 ≤ v k then
      ∑ p ∈ S k, (goldenLayerMarginal p (m.factorization p + 1) - beta 1 R) * log (p : ℝ)
    else -(∑ p ∈ S k, (goldenLayerMarginal p (m.factorization p) - beta 1 R) * log (p : ℝ))
  have hmassId : logMass U - logMass D = ∑ k : Fin 5, signedMass k := by
    dsimp [logMass, D, U]
    rw [hsumUnion, hsumUnion]
    simp only [positiveModes, negativeModes, sum_filter, signedMass, logMass]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    split_ifs <;> first | omega | ring
  have hfeeId : auxiliaryGain (beta 1 R) m D U = ∑ k : Fin 5, signedFee k := by
    dsimp [auxiliaryGain, D, U]
    rw [hsumUnion, hsumUnion]
    simp only [positiveModes, negativeModes, sum_filter, signedFee]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro k _
    split_ifs <;> first | omega | ring
  have hmassOne (k : Fin 5) :
      |signedMass k - (v k : ℝ) * rootMasses R k| ≤
        (16 * A * B) * log R * R ^ (-(19 / 640 : ℝ)) := by
    have hpoint := finite_sum_point_error (S k) (fun p => log (p : ℝ))
      (rootLog R k) (A * R ^ (-priceExponent (modeIndex k)))
      (fun p hp => (hS k p hp).2.1)
    have hj0 : (modeIndex k : ℝ) ≠ 0 := by
      have := (mode_index_bounds k).1; exact_mod_cast (by omega : modeIndex k ≠ 0)
    have he : (S k).card * rootLog R k = |(v k : ℝ)| * rootMasses R k := by
      rw [hcard, root_log_mass k R]
      field_simp [hj0] <;> ring
    change |logMass (S k) - (S k).card * rootLog R k| ≤ _ at hpoint
    rw [he] at hpoint
    have hsign : |signedMass k - (v k : ℝ) * rootMasses R k| =
        |logMass (S k) - |(v k : ℝ)| * rootMasses R k| := by
      by_cases hk : 0 ≤ v k
      · have hkR : 0 ≤ (v k : ℝ) := by exact_mod_cast hk
        simp [signedMass, hk, abs_of_nonneg hkR]
      · have hkR : (v k : ℝ) < 0 := by exact_mod_cast (show v k < 0 by omega)
        dsimp only [signedMass]
        rw [if_neg hk, abs_of_neg hkR]
        convert abs_neg (logMass (S k) + (v k : ℝ) * rootMasses R k) using 1 <;> congr 1 <;> ring
    rw [hsign]
    exact hpoint.trans (by
      calc
        _ ≤ (16 * B * log R) * (A * R ^ (-(19 / 640 : ℝ))) :=
          mul_le_mul (hcardBound k) (mul_le_mul_of_nonneg_left (htexp k) hA)
            (by positivity) (by positivity)
        _ = _ := by ring)
  have hfeeOne (k : Fin 5) : |signedFee k| ≤
      (16 * A * B) * beta 1 R * log R ^ 2 * R ^ (-(19 / 640 : ℝ)) := by
    let f : ℕ → ℝ := fun p => (goldenLayerMarginal p (modeIndex k) - beta 1 R) * log (p : ℝ)
    have hpoint : |∑ p ∈ S k, f p| ≤ (S k).card *
        (A * beta 1 R * log R * R ^ (-priceExponent (modeIndex k))) := by
      simpa only [sub_zero, mul_zero] using
        finite_sum_point_error (S k) f 0
          (A * beta 1 R * log R * R ^ (-priceExponent (modeIndex k)))
          (fun p hp => by simpa [f] using (hS k p hp).2.2)
    have he : |signedFee k| = |∑ p ∈ S k, f p| := by
      by_cases hk : 0 ≤ v k
      · dsimp [signedFee]; rw [if_pos hk]
        congr 1
        apply sum_congr rfl
        intro p hp
        have hvp : m.factorization p + 1 = modeIndex k := by
          simpa [hk] using (hS k p hp).1.2.2.1
        rw [hvp]
      · dsimp [signedFee]; rw [if_neg hk, abs_neg]
        congr 1
        apply sum_congr rfl
        intro p hp
        have hvp : m.factorization p = modeIndex k := by
          simpa [hk] using (hS k p hp).1.2.2.1
        rw [hvp]
    rw [he]
    exact hpoint.trans (by
      calc
        _ ≤ (16 * B * log R) *
            (A * beta 1 R * log R * R ^ (-(19 / 640 : ℝ))) := by
          apply mul_le_mul (hcardBound k)
          · exact mul_le_mul_of_nonneg_left (htexp k) (by positivity)
          · positivity
          · positivity
        _ = _ := by ring)
  refine ⟨D, U, hDU, hDlegal, hUlegal, ?_, ?_⟩
  · rw [hmassId, ← sum_sub_distrib]
    calc
      _ ≤ ∑ k : Fin 5, |signedMass k - (v k : ℝ) * rootMasses R k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 5, (16 * A * B) * log R * R ^ (-(19 / 640 : ℝ)) :=
        sum_le_sum (fun k _ => hmassOne k)
      _ = _ := by simp; ring
  · rw [hfeeId]
    calc
      _ ≤ ∑ k : Fin 5, |signedFee k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 5, (16 * A * B) * beta 1 R * log R ^ 2 * R ^ (-(19 / 640 : ℝ)) :=
        sum_le_sum (fun k _ => hfeeOne k)
      _ = _ := by simp; ring

private theorem clock_rescaling {L M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hlo : L / 2 ≤ M) (hhi : M ≤ 2 * L) :
    1 / L ^ 4 ≤ 16 * M ^ (-(4 : ℝ)) ∧ L ^ 2 ≤ 4 * M ^ 2 := by
  have hfour : M ^ 4 ≤ 16 * L ^ 4 := by
    have hh := pow_le_pow_left₀ hM.le hhi 4
    norm_num [mul_pow] at hh
    exact hh
  have htwo : L ^ 2 ≤ (2 * M) ^ 2 :=
    pow_le_pow_left₀ hL.le (by linarith) 2
  have hneg : M ^ (-(4 : ℝ)) = 1 / M ^ 4 := by
    rw [Real.rpow_neg hM.le]
    norm_num
  refine ⟨?_, by nlinarith only [htwo]⟩
  rw [hneg, show (16 : ℝ) * (1 / M ^ 4) = 16 / M ^ 4 by ring]
  apply (div_le_div_iff₀ (pow_pos hL 4) (pow_pos hM 4)).mpr
  nlinarith only [hfour]

/-- Uniform actual test-predecessor slack under two independent BHP hypotheses.
The slack is for this predecessor; prescribed bank payment and RH remain open. -/
theorem bhp_actual_five_mode_small_slack :
    BHPMaximumGap → BHPShortIntervalCount →
      ∃ C T : ℝ, 0 < C ∧ 0 < T ∧
        ∀ m : ℕ, 2 ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
          T ≤ (largestPrime m : ℝ) →
          let lambda := beta 1 (largestPrime m : ℝ)
          let Dtop := lambda * Real.log 2 -
            goldenLayerMarginal 2 (m.factorization 2) * Real.log 2
          ∃ n : ℕ, 0 < n ∧ n < m ∧
            let eta := Real.log (m : ℝ) - Real.log (n : ℝ)
            0 < eta ∧
            eta ≤ C * Real.log (Real.log (m : ℝ)) ^ (-(4 : ℝ)) ∧
            |(goldenResourceObjective lambda n - goldenResourceObjective lambda m) - Dtop| ≤
              C * lambda * Real.log (Real.log (m : ℝ)) ^ 2 *
                (largestPrime m : ℝ) ^ (-(19 / 640 : ℝ)) ∧
            Dtop ≤ (lambda - mu) * eta +
              C * lambda * Real.log (Real.log (m : ℝ)) ^ 2 *
                (largestPrime m : ℝ) ^ (-(19 / 640 : ℝ)) := by
  classical
  intro hgap hcount
  obtain ⟨A, Ti, hA, hTi, hi⟩ := uniform_five_mode_pools hgap hcount
  obtain ⟨B, Tv, hB, hTv, hv⟩ := actual_root_greedy_stencil
  obtain ⟨Tc, hTc, hc⟩ := uniform_actual_clock
  let K : ℝ := 80 * A * B
  have hK : 0 < K := by dsimp [K]; positivity
  have hgood : ∀ᶠ R : ℝ in atTop,
      4 ≤ R ∧
      (∀ k : Fin 5, ∀ z : ℤ, |(z : ℝ)| ≤ B * log R →
        modeIndex k * z.natAbs ≤ comparisonCount (countIndex k) R) ∧
      0 < mesh4 R ∧ K * log R * R ^ (-(19 / 640 : ℝ)) ≤ mesh4 R / 2 := by
    filter_upwards [eventually_ge_atTop (4 : ℝ), uniform_selection_capacity B,
      eventual_mass_error_absorption K hK.le] with R hR hcap habs
    exact ⟨hR, hcap, habs⟩
  obtain ⟨Ts, hTs⟩ := eventually_atTop.mp hgood
  let C : ℝ := 1 + 64 * B + 4 * K
  let T := max Ti (max Tv (max Tc Ts))
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, T, hC, lt_of_lt_of_le hTi (le_max_left _ _), ?_⟩
  intro m hm mu hmu hrecord hlarge
  dsimp only
  let R : ℝ := largestPrime m
  let lambda := beta 1 R
  let M := log (log (m : ℝ))
  have hTiR : Ti ≤ R := (le_max_left Ti _).trans hlarge
  have hTvR : Tv ≤ R := (le_max_left Tv _).trans ((le_max_right Ti _).trans hlarge)
  have hTcR : Tc ≤ R := (le_max_left Tc Ts).trans
    ((le_max_right Tv _).trans ((le_max_right Ti _).trans hlarge))
  have hTsR : Ts ≤ R := (le_max_right Tc Ts).trans
    ((le_max_right Tv _).trans ((le_max_right Ti _).trans hlarge))
  obtain ⟨hR4, hcapacity, hmesh, habsorb⟩ := hTs R hTsR
  obtain ⟨hL1, hM, hclockLo, hclockHi⟩ := hc m hm mu hmu hrecord hTcR
  have hL : 0 < log R := by linarith
  have hlam : 0 < lambda := beta_pos (by linarith) (by norm_num)
  have ht : 0 ≤ R ^ (-(19 / 640 : ℝ)) := by positivity
  obtain ⟨hQ8, Lo, Hi, hpools⟩ := hi m hm mu hmu hrecord hTiR
  obtain ⟨v, _hsum, hvbound, _hmesh, hmeshUpper, hidealLo, hidealHi⟩ := hv R hTvR
  have hcap (k : Fin 5) : modeIndex k * (v k).natAbs ≤ comparisonCount (countIndex k) R :=
    hcapacity k (v k) (hvbound k)
  obtain ⟨D, U, hDU, hD, hU, hmassError, hfee⟩ :=
    finite_five_mode_selection hm (show R = largestPrime m from rfl) hR4 hA.le hB.le
      hQ8 Lo Hi hpools v hvbound hcap
  let eta0 := log 2 + logMass D - logMass U
  have heta0 : 0 < eta0 := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hmassError
    dsimp [eta0, K] at *
    linarith only [hidealLo, hhi, habsorb, hmesh]
  have heta4 : eta0 ≤ 4 * mesh4 R := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hmassError
    dsimp [eta0, K] at *
    linarith only [hidealHi, hlo, habsorb, hmesh]
  obtain ⟨n, hnpos, hnm, heta, _htop, hgain, hrecordGain⟩ :=
    actual_finite_predecessor hm hmu hrecord (lambda := lambda) D U hD hU hDU heta0
  have hetaPos : 0 < log (m : ℝ) - log (n : ℝ) := by rwa [heta]
  obtain ⟨hinv, hsq⟩ := clock_rescaling hL hM hclockLo hclockHi
  have h64 : 64 * B ≤ C := by dsimp [C]; linarith
  have h4K : 4 * K ≤ C := by dsimp [C]; linarith
  have hgainBound : |auxiliaryGain lambda m D U| ≤ C * lambda * M ^ 2 *
      R ^ (-(19 / 640 : ℝ)) := by
    calc
      _ ≤ K * lambda * log R ^ 2 * R ^ (-(19 / 640 : ℝ)) := hfee
      _ ≤ K * lambda * (4 * M ^ 2) * R ^ (-(19 / 640 : ℝ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsq (mul_nonneg hK.le hlam.le)) ht
      _ = (4 * K) * lambda * M ^ 2 * R ^ (-(19 / 640 : ℝ)) := by ring
      _ ≤ C * lambda * M ^ 2 * R ^ (-(19 / 640 : ℝ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right h4K hlam.le) (sq_nonneg M)) ht
  refine ⟨n, hnpos, hnm, hetaPos, ?_, ?_, ?_⟩
  · calc
      _ = eta0 := heta
      _ ≤ 4 * mesh4 R := heta4
      _ ≤ 4 * (B / log R ^ 4) := mul_le_mul_of_nonneg_left hmeshUpper (by norm_num)
      _ = (4 * B) * (1 / log R ^ 4) := by ring
      _ ≤ (4 * B) * (16 * M ^ (-(4 : ℝ))) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (64 * B) * M ^ (-(4 : ℝ)) := by ring
      _ ≤ C * M ^ (-(4 : ℝ)) :=
        mul_le_mul_of_nonneg_right h64 (by positivity)
  · change |(goldenResourceObjective lambda n - goldenResourceObjective lambda m) -
        topGain lambda m| ≤ _
    rw [hgain, add_sub_cancel_left]
    exact hgainBound
  · change topGain lambda m ≤ (lambda - mu) * (log (m : ℝ) - log (n : ℝ)) + _
    have hneg : -auxiliaryGain lambda m D U ≤ |auxiliaryGain lambda m D U| :=
      neg_le_abs _
    exact hrecordGain.le.trans (by linarith only [hneg, hgainBound])

end D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlackCandidate
