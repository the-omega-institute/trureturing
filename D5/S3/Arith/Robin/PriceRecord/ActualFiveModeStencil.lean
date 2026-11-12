/- GID: D5/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualFiveModeStencil
   mirror-E: none(waiver:elementary-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Actual-cutoff dyadic stencil and uniform greedy coefficients. -/
/- proof_shape: content
admission_basis: escape-witness
utility: none. These are unbounded conditional estimates, asymptotic laws and
finite-set identities for arbitrary inputs, not bounded enumeration, a checker,
a numerical reduction or a certified instance. Auxiliary bind-only statements
are consumed in the subsequent actual-record construction. -/
import D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
import D5.S3.Arith.Robin.PriceRecord.ActualMixedCutoffFourthOrder
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack

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
open D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization
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

def actualOffset (j : ℕ) (X : ℝ) : ℝ :=
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
theorem uniform_boundary_root_log_transfer
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
    ActualBoundaryPriceLocalization.uniform_coarse_geometry j hj
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

def mesh1 (X : ℝ) : ℝ := actualOffset 2 X
def mesh2 (X : ℝ) : ℝ := actualOffset 4 X - 2 * actualOffset 2 X
def mesh3 (X : ℝ) : ℝ :=
  -actualOffset 8 X + 3 * actualOffset 4 X - 3 * actualOffset 2 X
def mesh4 (X : ℝ) : ℝ :=
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

theorem actual_stencil_limits :
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

def rootMasses (X : ℝ) : Fin 5 → ℝ :=
  ![log X, log X + actualOffset 2 X, log X + actualOffset 4 X,
    log X + actualOffset 8 X, log X + actualOffset 16 X]

/- This is the ideal stencil at the actual price beta 1 X, NOT an integer
predecessor theorem. No supplied inventory or small-slack assumption occurs. -/
theorem actual_root_greedy_stencil : ∃ B T : ℝ, 0 < B ∧ 0 < T ∧
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

end D5.S3.Arith.Robin.PriceRecord.ActualFiveModeSmallSlack
