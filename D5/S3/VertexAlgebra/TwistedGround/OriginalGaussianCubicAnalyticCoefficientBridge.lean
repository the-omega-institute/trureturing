/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicAnalyticCoefficientBridge
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalGaussianCubicAnalyticCoefficientBridge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The actual half-binomial, inverse-period and literal kernel power series are integrated on fixed contours with proved continuity and termwise convergence. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalytic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-!
Cauchy expansions of the literal cubic kernels after integration in the
annular variable. The external amplitude remains an arbitrary complex number.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators Topology ENNReal NNReal
open Filter Metric Set MeasureTheory

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalyticCoefficientBridge

open D5.S3.VertexAlgebra.LatticeHalfFockFiniteCorrection
open OriginalGaussianCubicKernel OriginalGaussianCubicAnalytic OriginalGaussianMatrix OriginalGaussianResolvent

private lemma beta_positive {b : ℂ} (hb : b ≠ 0) : 0 < beta b :=
  lt_min (by norm_num) (norm_pos_iff.mpr hb)

private lemma mem_complex_eball {x : ℂ} {R : ℝ≥0} :
    x ∈ eball (0 : ℂ) (R : ℝ≥0∞) ↔ ‖x‖ < (R : ℝ) := by
  rw [mem_eball_zero_iff, enorm_lt_coe]
  exact NNReal.coe_lt_coe.symm

private lemma half_norm_bound (n : ℕ) : ‖halfBinomial n‖ ≤ 1 := by
  rw [halfBinomial_eq_signed_centralWeight, norm_mul, norm_pow]
  simpa [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (centralWeight_nonneg n)] using weight_le_one n

/-- Absolute convergence refers to the original half-binomial coefficients. -/
theorem H_hasSum {v : ℂ} (hv : ‖v‖ < 1) :
    HasSum (fun n : ℕ => halfBinomial n * v ^ n) (H v) ∧
      Summable (fun n : ℕ => ‖halfBinomial n * v ^ n‖) := by
  have hs : Summable (fun n : ℕ => ‖halfBinomial n * v ^ n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) (summable_geometric_of_lt_one (norm_nonneg v) hv)
    rw [norm_mul, norm_pow]
    exact (mul_le_mul_of_nonneg_right (half_norm_bound n)
      (pow_nonneg (norm_nonneg v) n)).trans_eq (one_mul _)
  exact ⟨hs.of_norm.hasSum, hs⟩

private lemma H_powerSeries :
    HasFPowerSeriesOnBall H (binomialSeries ℂ (-1 / 2 : ℂ)) 0 1 := by
  apply Complex.one_add_cpow_hasFPowerSeriesOnBall_zero.congr
  intro v hv
  have hv' : ‖v‖ < 1 := (mem_complex_eball (R := 1)).mp hv
  have hc := (Complex.one_add_cpow_hasFPowerSeriesOnBall_zero
    (a := (-1 / 2 : ℂ))).hasSum hv
  have he : HasSum (fun n : ℕ => halfBinomial n * v ^ n)
      ((1 + v) ^ (-1 / 2 : ℂ)) := by
    simpa only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq,
      smul_eq_mul, zero_add, halfBinomial_choose] using hc
  exact he.unique (H_hasSum hv').1

private lemma H_continuousAt {v : ℂ} (hv : ‖v‖ < 1) : ContinuousAt H v := by
  exact (H_powerSeries.analyticAt_of_mem ((mem_complex_eball (R := 1)).mpr hv)).continuousAt

private lemma scalar_product_hasSum {p q : PowerSeries ℂ} {x u v : ℂ}
    (hp : HasSum (fun n : ℕ => PowerSeries.coeff n p * x ^ n) u)
    (hq : HasSum (fun n : ℕ => PowerSeries.coeff n q * x ^ n) v) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (p * q) * x ^ n) (u * v) := by
  have h := hasSum_sum_range_mul_of_summable_norm hp.summable.norm hq.summable.norm
  rw [hp.tsum_eq, hq.tsum_eq] at h
  convert h using 1
  funext n
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  change (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
    (PowerSeries.coeff ij.1 p * PowerSeries.coeff ij.2 q) * x ^ n) = _
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k + (n - k) = n := Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hpow : x ^ n = x ^ k * x ^ (n - k) := by rw [← pow_add, hkn]
  rw [hpow]
  ring

private lemma scalar_coefficients_mul {f g : ℂ → ℂ} {p q : PowerSeries ℂ}
    (hp : HasFPowerSeriesAt f (.ofScalars ℂ (fun n => PowerSeries.coeff n p)) 0)
    (hq : HasFPowerSeriesAt g (.ofScalars ℂ (fun n => PowerSeries.coeff n q)) 0) :
    HasFPowerSeriesAt (fun x => f x * g x)
      (.ofScalars ℂ (fun n => PowerSeries.coeff n (p * q))) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [hasFPowerSeriesAt_iff.mp hp, hasFPowerSeriesAt_iff.mp hq] with x hx hy
  have hx' : HasSum (fun n => PowerSeries.coeff n p * x ^ n) (f x) := by
    simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul,
      mul_comm] using hx
  have hy' : HasSum (fun n => PowerSeries.coeff n q * x ^ n) (g x) := by
    simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul,
      mul_comm] using hy
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul,
    mul_comm] using scalar_product_hasSum hx' hy'

private lemma scalar_coefficients_sub {f g : ℂ → ℂ} {p q : PowerSeries ℂ}
    (hp : HasFPowerSeriesAt f (.ofScalars ℂ (fun n => PowerSeries.coeff n p)) 0)
    (hq : HasFPowerSeriesAt g (.ofScalars ℂ (fun n => PowerSeries.coeff n q)) 0) :
    HasFPowerSeriesAt (fun x => f x - g x)
      (.ofScalars ℂ (fun n => PowerSeries.coeff n (p - q))) 0 := by
  have he : (fun n => PowerSeries.coeff n (p - q)) =
      (fun n => PowerSeries.coeff n p) - (fun n => PowerSeries.coeff n q) := by
    funext n
    exact map_sub _ _ _
  rw [he, FormalMultilinearSeries.ofScalars_sub]
  exact hp.sub hq

private lemma scalar_coefficients_const (c : ℂ) :
    HasFPowerSeriesAt (fun _ : ℂ => c)
      (.ofScalars ℂ (fun n => PowerSeries.coeff n (PowerSeries.C c))) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [] with x
  have hs : HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.C c) * x ^ n)
      (PowerSeries.coeff 0 (PowerSeries.C c) * x ^ 0) := by
    apply hasSum_single 0
    intro n hn
    simp [PowerSeries.coeff_C, hn]
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul,
    PowerSeries.coeff_zero_C, pow_zero, mul_one, mul_comm] using hs

private lemma scalar_coefficients_X :
    HasFPowerSeriesAt (fun x : ℂ => x)
      (.ofScalars ℂ (fun n => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ))) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [] with x
  have hs : HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.X : PowerSeries ℂ) * x ^ n)
      (PowerSeries.coeff 1 (PowerSeries.X : PowerSeries ℂ) * x ^ 1) := by
    apply hasSum_single 1
    intro n hn
    simp [PowerSeries.coeff_X, hn]
  simpa only [FormalMultilinearSeries.coeff_ofScalars, zero_add, smul_eq_mul,
    PowerSeries.coeff_one_X, pow_one, one_mul, mul_one, mul_comm] using hs

private lemma scalar_coefficients_injective {p q : PowerSeries ℂ}
    (h : FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n p) =
      .ofScalars ℂ (fun n => PowerSeries.coeff n q)) : p = q := by
  ext n
  simpa only [FormalMultilinearSeries.coeff_ofScalars] using
    congrArg (fun k : FormalMultilinearSeries ℂ ℂ ℂ => k.coeff n) h

private lemma period_original_hasSum {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff n periodSeries * x ^ n)
      (D5.S3.Analytic.OriginalHalfBinomialPeriod.period x) := by
  have hs : Summable (fun n : ℕ => ‖halfBinomial n ^ 2 * x ^ n‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => ?_) (summable_geometric_of_lt_one (norm_nonneg x) hx)
    rw [norm_mul, norm_pow x n]
    have hn : ‖halfBinomial n ^ 2‖ ≤ 1 := by
      simpa [norm_pow] using pow_le_pow_left₀ (norm_nonneg _) (half_norm_bound n) 2
    exact (mul_le_mul_of_nonneg_right hn (pow_nonneg (norm_nonneg x) n)).trans_eq (one_mul _)
  simpa only [periodSeries, PowerSeries.coeff_mk,
    D5.S3.Analytic.OriginalHalfBinomialPeriod.period] using hs.of_norm.hasSum

private lemma period_coefficients_at :
    HasFPowerSeriesAt D5.S3.Analytic.OriginalHalfBinomialPeriod.period
      (.ofScalars ℂ (fun n => PowerSeries.coeff n periodSeries)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with x hx
  have hx' : ‖x‖ < 1 := by simpa using hx
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add,
    mul_comm] using period_original_hasSum hx'

/-- The reciprocal is derived from the actual nonvanishing period and Cauchy
product uniqueness; its coefficients are the existing formal inverse. -/
theorem period_inverse_powerSeries {eta : ℝ≥0} (heta : 0 < eta) (heta1 : (eta : ℝ) < 1) :
    HasFPowerSeriesOnBall (fun x => (D5.S3.Analytic.OriginalHalfBinomialPeriod.period x)⁻¹)
      (.ofScalars ℂ (fun n => PowerSeries.coeff n (periodSeries⁻¹))) 0 eta := by
  let G : ℂ → ℂ := fun x => (D5.S3.Analytic.OriginalHalfBinomialPeriod.period x)⁻¹
  have hD : DifferentiableOn ℂ G (closedBall (0 : ℂ) eta) := by
    intro x hx
    have hx1 : ‖x‖ < 1 := (show ‖x‖ ≤ eta by simpa using hx).trans_lt heta1
    exact ((D5.S3.Analytic.OriginalHalfBinomialPeriod.picard_fuchs hx1).1.inv
      (OriginalGaussianPeriodIdentity.period_ne_zero hx1)).differentiableWithinAt
  let P := cauchyPowerSeries G 0 eta
  let q : PowerSeries ℂ := PowerSeries.mk (fun n => P.coeff n)
  have he : FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n q) = P := by
    funext n
    calc
      _ = ContinuousMultilinearMap.mkPiRing ℂ (Fin n)
          ((FormalMultilinearSeries.ofScalars ℂ (fun n => PowerSeries.coeff n q)).coeff n) :=
        (FormalMultilinearSeries.mkPiRing_coeff_eq _ n).symm
      _ = ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (P.coeff n) := by
        simp only [FormalMultilinearSeries.coeff_ofScalars, q, PowerSeries.coeff_mk]
      _ = _ := FormalMultilinearSeries.mkPiRing_coeff_eq P n
  have hq : HasFPowerSeriesOnBall G
      (.ofScalars ℂ (fun n => PowerSeries.coeff n q)) 0 eta := by
    rw [he]
    exact hD.hasFPowerSeriesOnBall heta
  have hm := scalar_coefficients_mul period_coefficients_at hq.hasFPowerSeriesAt
  have hOne : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (.ofScalars ℂ (fun n => PowerSeries.coeff n (1 : PowerSeries ℂ))) 0 := by
    simpa only [map_one] using scalar_coefficients_const (1 : ℂ)
  have hfun : (fun x => D5.S3.Analytic.OriginalHalfBinomialPeriod.period x * G x) =ᶠ[𝓝 0]
      (fun _ => (1 : ℂ)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with x hx
    have hx1 : ‖x‖ < 1 := by simpa using hx
    exact mul_inv_cancel₀ (OriginalGaussianPeriodIdentity.period_ne_zero hx1)
  have hmul : periodSeries * q = 1 := scalar_coefficients_injective
    (hm.eq_formalMultilinearSeries_of_eventually hOne hfun)
  have hF : PowerSeries.constantCoeff periodSeries ≠ 0 := by
    simp [periodSeries, halfBinomial]
  have hqeq : q = periodSeries⁻¹ := by
    calc
      q = (periodSeries⁻¹ * periodSeries) * q := by
        rw [PowerSeries.inv_mul_cancel periodSeries hF, one_mul]
      _ = periodSeries⁻¹ := by rw [mul_assoc, hmul, mul_one]
  simpa only [hqeq] using hq

private lemma period_derivative_original_hasSum {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.derivative periodSeries) * x ^ n)
      (deriv D5.S3.Analytic.OriginalHalfBinomialPeriod.period x) := by
  convert (D5.S3.Analytic.OriginalHalfBinomialPeriod.period_derivative hx).1 using 1
  funext n
  simp only [PowerSeries.coeff_derivative, periodSeries, PowerSeries.coeff_mk]
  change halfBinomial (n + 1) ^ 2 * (n + 1 : ℂ) * x ^ n =
    ((n + 1 : ℂ) * halfBinomial (n + 1) ^ 2) * x ^ n
  ring

private lemma scalarC_coefficients_at :
    HasFPowerSeriesAt scalarC (.ofScalars ℂ (fun n => PowerSeries.coeff n scalarCSeries)) 0 := by
  have hF' : HasFPowerSeriesAt (deriv D5.S3.Analytic.OriginalHalfBinomialPeriod.period)
      (.ofScalars ℂ (fun n => PowerSeries.coeff n (PowerSeries.derivative periodSeries))) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1)] with x hx
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm] using
      period_derivative_original_hasSum (show ‖x‖ < 1 by simpa using hx)
  have hOne : HasFPowerSeriesAt (fun _ : ℂ => (1 : ℂ))
      (.ofScalars ℂ (fun n => PowerSeries.coeff n (1 : PowerSeries ℂ))) 0 := by
    simpa only [map_one] using scalar_coefficients_const (1 : ℂ)
  have hi := (period_inverse_powerSeries (eta := (1 / 2 : ℝ≥0))
    (by norm_num) (by norm_num)).hasFPowerSeriesAt
  have h := scalar_coefficients_sub
    (scalar_coefficients_mul (scalar_coefficients_const (1 / 2 : ℂ)) scalar_coefficients_X)
    (scalar_coefficients_mul
      (scalar_coefficients_mul
        (scalar_coefficients_mul scalar_coefficients_X (scalar_coefficients_sub hOne scalar_coefficients_X))
        hF') hi)
  change HasFPowerSeriesAt scalarC
    (.ofScalars ℂ (fun n => PowerSeries.coeff n
      (PowerSeries.C (1 / 2) * PowerSeries.X -
        PowerSeries.X * (1 - PowerSeries.X) * PowerSeries.derivative periodSeries * periodSeries⁻¹))) 0
  convert h using 1
  funext x
  unfold scalarC
  ring

/-- Taylor coefficients of the unchanged scalar, including the actual period
derivative and the formal inverse, agree on every strict disk. -/
theorem scalarC_powerSeries {eta : ℝ≥0} (heta : 0 < eta) (heta1 : (eta : ℝ) < 1) :
    HasFPowerSeriesOnBall scalarC
      (.ofScalars ℂ (fun n => PowerSeries.coeff n scalarCSeries)) 0 eta := by
  have hD : DifferentiableOn ℂ scalarC (closedBall (0 : ℂ) eta) := by
    intro x hx
    have hx1 : ‖x‖ < 1 := (show ‖x‖ ≤ eta by simpa using hx).trans_lt heta1
    obtain ⟨hF, hF', _⟩ := D5.S3.Analytic.OriginalHalfBinomialPeriod.picard_fuchs hx1
    have hn := OriginalGaussianPeriodIdentity.period_ne_zero hx1
    exact ((differentiableAt_id.div_const 2).sub
      (((differentiableAt_id.mul ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id)).mul
        hF').div hF hn)).differentiableWithinAt
  have hC := hD.hasFPowerSeriesOnBall heta
  have he := scalarC_coefficients_at.eq_formalMultilinearSeries hC.hasFPowerSeriesAt
  rwa [← he] at hC

private lemma C_continuousAt {x : ℂ} (hx : ‖x‖ < 1) :
    ContinuousAt scalarC x := by
  obtain ⟨eta, hxeta, heta1⟩ := exists_between hx
  have heta : 0 < eta := (norm_nonneg x).trans_lt hxeta
  have h := scalarC_powerSeries (eta := (⟨eta, heta.le⟩ : ℝ≥0)) heta heta1
  exact (h.analyticAt_of_mem ((mem_complex_eball (R := (⟨eta, heta.le⟩ : ℝ≥0))).mpr hxeta)).continuousAt

/-- The literal squared polar inverses have the expected convergent expansions. -/
theorem polar_inverse_hasSum {a b x : ℂ} (hb : b ≠ 0)
    (ha : ‖a‖ < ‖b‖) (hx : ‖x‖ < ‖a * b‖) :
    HasSum (fun n : ℕ => (b ^ (n + 2))⁻¹ * (n + 1 : ℂ) * a ^ n)
      ((a - b) ^ 2)⁻¹ ∧
    HasSum (fun n : ℕ => ((a * b) ^ (n + 2))⁻¹ * (n + 1 : ℂ) * x ^ n)
      ((a * b - x) ^ 2)⁻¹ := by
  have hab : a * b ≠ 0 := norm_pos_iff.mp ((norm_nonneg x).trans_lt hx)
  have hT := (Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero hb).hasSum
    (show a ∈ eball (0 : ℂ) ‖b‖ₑ from (mem_complex_eball (R := ‖b‖₊)).mpr ha)
  have hU := (Complex.one_div_sub_sq_hasFPowerSeriesOnBall_zero hab).hasSum
    (show x ∈ eball (0 : ℂ) ‖a * b‖ₑ from (mem_complex_eball (R := ‖a * b‖₊)).mpr hx)
  constructor
  · have he : (b - a) ^ 2 = (a - b) ^ 2 := by ring
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      zero_add, one_div, he] using hT
  · simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
      zero_add, one_div] using hU

/-- Literal convergent factors on the common annulus. No evaluation of H at
the external point, or choice of its root, is involved. -/
theorem literal_factor_hasSum {b a x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (ha : ‖a‖ < beta b) (hx : ‖x‖ < ‖a‖ * beta b) :
    HasSum (fun n : ℕ => halfBinomial n * a ^ n) (H a) ∧
    HasSum (fun n : ℕ => (halfBinomial n / a ^ n) * x ^ n) (H (x / a)) ∧
    HasSum (fun n : ℕ => (root * halfBinomial n / b ^ (n + 1)) * x ^ n)
      (externalOmega b root x) ∧
    HasSum (fun n : ℕ => (b ^ (n + 2))⁻¹ * (n + 1 : ℂ) * a ^ n) ((a - b) ^ 2)⁻¹ ∧
    HasSum (fun n : ℕ => ((a * b) ^ (n + 2))⁻¹ * (n + 1 : ℂ) * x ^ n)
      ((a * b - x) ^ 2)⁻¹ ∧
    HasSum (fun n : ℕ => PowerSeries.coeff n periodSeries * x ^ n)
      (D5.S3.Analytic.OriginalHalfBinomialPeriod.period x) ∧
    HasSum (fun n : ℕ => PowerSeries.coeff n (PowerSeries.derivative periodSeries) * x ^ n)
      (deriv D5.S3.Analytic.OriginalHalfBinomialPeriod.period x) ∧
    HasSum (fun n : ℕ => PowerSeries.coeff n (periodSeries⁻¹) * x ^ n)
      (D5.S3.Analytic.OriginalHalfBinomialPeriod.period x)⁻¹ ∧
    HasSum (fun n : ℕ => PowerSeries.coeff n scalarCSeries * x ^ n) (scalarC x) := by
  have ha0 : 0 < ‖a‖ := by
    by_contra hn
    have : ‖a‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg a)
    rw [this, zero_mul] at hx
    exact (not_lt_of_ge (norm_nonneg x)) hx
  have ha1 : ‖a‖ < 1 := ha.trans_le (min_le_left _ _)
  have hab : ‖a‖ < ‖b‖ := ha.trans_le (min_le_right _ _)
  have hxa : ‖x‖ < ‖a‖ := hx.trans_le
    (mul_le_of_le_one_right ha0.le (min_le_left _ _))
  have hxb : ‖x‖ < ‖b‖ := hxa.trans hab
  have hx1 : ‖x‖ < 1 := hxa.trans ha1
  have hxab : ‖x‖ < ‖a * b‖ := by
    rw [norm_mul]
    exact hx.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) ha0.le)
  have hHa := (H_hasSum ha1).1
  have hHxa := (H_hasSum (by rw [norm_div]; exact (div_lt_one ha0).mpr hxa)).1
  have hHxb := (H_hasSum (by rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hb)).mpr hxb)).1
  have hE := hHxb.mul_left (root / b)
  obtain ⟨hT, hU⟩ := polar_inverse_hasSum hb hab hxab
  obtain ⟨eta, hxeta, heta1⟩ := exists_between hx1
  have heta : 0 < eta := (norm_nonneg x).trans_lt hxeta
  have hmem : x ∈ eball (0 : ℂ) (ENNReal.ofReal eta) := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_ofReal_iff heta]
    exact hxeta
  rw [ENNReal.ofReal_eq_coe_nnreal heta.le] at hmem
  have hI := (period_inverse_powerSeries (eta := (⟨eta, heta.le⟩ : ℝ≥0)) heta heta1).hasSum hmem
  have hC := (scalarC_powerSeries (eta := (⟨eta, heta.le⟩ : ℝ≥0)) heta heta1).hasSum hmem
  refine ⟨hHa, ?_, ?_, hT, hU, period_original_hasSum hx1,
    period_derivative_original_hasSum hx1, ?_, ?_⟩
  · convert hHxa using 1
    funext n
    rw [div_pow]
    ring
  · convert hE using 1
    · funext n
      rw [div_pow, pow_succ]
      field_simp [hb]
      <;> ring
    · rfl
  · simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hI
  · simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hC

private lemma kernel_continuity {b a x : ℂ} (hb : b ≠ 0) (root : ℂ)
    (ha : ‖a‖ < beta b) (hx : ‖x‖ < ‖a‖ * beta b) :
    ContinuousAt (fun ax : ℂ × ℂ => TT b root ax.1 ax.2) (a, x) ∧
      ContinuousAt (fun ax : ℂ × ℂ => UT b root ax.1 ax.2) (a, x) := by
  have hB := beta_positive hb
  have ha0 : 0 < ‖a‖ := by
    by_contra hn
    have : ‖a‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg a)
    rw [this, zero_mul] at hx
    exact (not_lt_of_ge (norm_nonneg x)) hx
  have hane : a ≠ 0 := norm_pos_iff.mp ha0
  have ha1 : ‖a‖ < 1 := ha.trans_le (min_le_left _ _)
  have hab : ‖a‖ < ‖b‖ := ha.trans_le (min_le_right _ _)
  have hxa : ‖x‖ < ‖a‖ := hx.trans_le
    (mul_le_of_le_one_right ha0.le (min_le_left _ _))
  have hxb : ‖x‖ < ‖b‖ := hxa.trans hab
  have hx1 : ‖x‖ < 1 := hxa.trans ha1
  have hxab : ‖x‖ < ‖a * b‖ := by
    rw [norm_mul]
    exact hx.trans_le (mul_le_mul_of_nonneg_left (min_le_right _ _) ha0.le)
  have hTne : a - b ≠ 0 := sub_ne_zero.mpr (ne_of_apply_ne norm hab.ne)
  have hUne : a * b - x ≠ 0 := sub_ne_zero.mpr (ne_of_apply_ne norm hxab.ne')
  have hHa : ContinuousAt (fun ax : ℂ × ℂ => H ax.1) (a, x) :=
    (H_continuousAt ha1).comp'
      (f := fun ax : ℂ × ℂ => ax.1) (x := (a, x)) continuousAt_fst
  have hHxa : ContinuousAt (fun ax : ℂ × ℂ => H (ax.2 / ax.1)) (a, x) :=
    (H_continuousAt (by rw [norm_div]; exact (div_lt_one ha0).mpr hxa)).comp'
      (f := fun ax : ℂ × ℂ => ax.2 / ax.1) (x := (a, x))
      (continuousAt_snd.div continuousAt_fst hane)
  have hHxb : ContinuousAt (fun ax : ℂ × ℂ => H (ax.2 / b)) (a, x) :=
    (H_continuousAt (by rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hb)).mpr hxb)).comp'
      (f := fun ax : ℂ × ℂ => ax.2 / b) (x := (a, x)) (continuousAt_snd.div_const b)
  have hw : ContinuousAt (fun ax : ℂ × ℂ => omega ax.1 ax.2) (a, x) :=
    (hHa.div continuousAt_fst hane).mul hHxa
  have he : ContinuousAt (fun ax : ℂ × ℂ => externalOmega b root ax.2) (a, x) :=
    hHxb.const_mul _
  have hN : ContinuousAt (fun ax : ℂ × ℂ => polarNumerator ax.1 b ax.2) (a, x) := by
    unfold polarNumerator
    fun_prop
  have hC : ContinuousAt (fun ax : ℂ × ℂ => scalarC ax.2) (a, x) :=
    (C_continuousAt hx1).comp'
      (f := fun ax : ℂ × ℂ => ax.2) (x := (a, x)) continuousAt_snd
  have hT : ContinuousAt (fun ax : ℂ × ℂ => (2 * (ax.1 - b) ^ 2)⁻¹) (a, x) :=
    (by fun_prop : ContinuousAt (fun ax : ℂ × ℂ => 2 * (ax.1 - b) ^ 2) (a, x)).inv₀
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hTne))
  have hU : ContinuousAt (fun ax : ℂ × ℂ => (2 * (ax.1 * b - ax.2) ^ 2)⁻¹) (a, x) :=
    (by fun_prop : ContinuousAt (fun ax : ℂ × ℂ => 2 * (ax.1 * b - ax.2) ^ 2) (a, x)).inv₀
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hUne))
  have hTden : (2 * (a - b) ^ 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hTne)
  have hUden : (2 * (a * b - x) ^ 2 : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ hUne)
  exact ⟨(hw.mul he).mul ((hN.div (by fun_prop) hTden).add hC),
    (hw.mul he).neg.mul (((continuousAt_snd.mul hN).div (by fun_prop) hUden).add hC)⟩

private lemma kernels_continuousOn {b : ℂ} (hb : b ≠ 0) (root : ℂ)
    {r eta : ℝ} (hrb : r < beta b) (hetab : eta < r * beta b) :
    ContinuousOn (fun ax : ℂ × ℂ => TT b root ax.1 ax.2)
        (sphere (0 : ℂ) r ×ˢ closedBall (0 : ℂ) eta) ∧
    ContinuousOn (fun ax : ℂ × ℂ => UT b root ax.1 ax.2)
        (sphere (0 : ℂ) r ×ˢ closedBall (0 : ℂ) eta) := by
  have hc (ax : ℂ × ℂ) (hax : ax ∈ sphere (0 : ℂ) r ×ˢ closedBall (0 : ℂ) eta) :
      ContinuousAt (fun ax : ℂ × ℂ => TT b root ax.1 ax.2) ax ∧
        ContinuousAt (fun ax : ℂ × ℂ => UT b root ax.1 ax.2) ax := by
    have har : ‖ax.1‖ = r := by simpa using hax.1
    have hxeta : ‖ax.2‖ ≤ eta := by simpa using hax.2
    exact kernel_continuity hb root (by simpa [har] using hrb)
      (by simpa [har] using hxeta.trans_lt hetab)
  exact ⟨fun ax hax => (hc ax hax).1.continuousWithinAt,
    fun ax hax => (hc ax hax).2.continuousWithinAt⟩

private lemma negativeContour_continuousOn {K : ℂ → ℂ → ℂ} (s : ℕ)
    {r eta : ℝ} (hr : 0 ≤ r)
    (hK : ContinuousOn (fun ax : ℂ × ℂ => K ax.1 ax.2)
      (sphere (0 : ℂ) r ×ˢ closedBall (0 : ℂ) eta)) :
    ContinuousOn (fun x => negativeContour (fun a => K a x) s r) (closedBall 0 eta) := by
  let J : closedBall (0 : ℂ) eta → ℝ → ℂ := fun x t =>
    deriv (circleMap 0 r) t * (K (circleMap 0 r t) x * circleMap 0 r t ^ s)
  have hJ : Continuous J.uncurry := by
    have hk : Continuous (fun xt : closedBall (0 : ℂ) eta × ℝ =>
        K (circleMap 0 r xt.2) xt.1) :=
      hK.comp_continuous
        (f := fun xt : closedBall (0 : ℂ) eta × ℝ =>
          (circleMap 0 r xt.2, (xt.1 : ℂ))) (by fun_prop)
        (fun xt => ⟨circleMap_mem_sphere _ hr _, xt.1.2⟩)
    dsimp [J, Function.uncurry]
    have hd : Continuous (fun xt : closedBall (0 : ℂ) eta × ℝ =>
        deriv (circleMap 0 r) xt.2) := by
      simp only [deriv_circleMap]
      fun_prop
    exact hd.mul (hk.mul (by fun_prop))
  have hc : Continuous (fun x : closedBall (0 : ℂ) eta =>
      ∫ t in Icc 0 (2 * Real.pi), J x t) :=
    continuous_parametric_integral_of_continuous hJ isCompact_Icc
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun x : closedBall (0 : ℂ) eta =>
    negativeContour (fun a => K a x) s r)
  simpa only [negativeContour, circleIntegral_def_Icc, smul_eq_mul, J] using
    hc.const_mul ((2 * Real.pi * Complex.I)⁻¹)

/-- Fubini for continuous functions on the two actual oriented circles. -/
private lemma circleIntegral_swap {G : ℂ → ℂ → ℂ} {r eta : ℝ}
    (hr : 0 ≤ r) (heta : 0 ≤ eta)
    (hG : ContinuousOn (fun ax : ℂ × ℂ => G ax.1 ax.2)
      (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) eta)) :
    (∮ a in C(0, r), ∮ x in C(0, eta), G a x) =
      ∮ x in C(0, eta), ∮ a in C(0, r), G a x := by
  let J : ℝ × ℝ → ℂ := fun ts =>
    deriv (circleMap 0 r) ts.1 * deriv (circleMap 0 eta) ts.2 *
      G (circleMap 0 r ts.1) (circleMap 0 eta ts.2)
  have hJ : Continuous J := by
    have hg : Continuous (fun ts : ℝ × ℝ =>
        G (circleMap 0 r ts.1) (circleMap 0 eta ts.2)) :=
      hG.comp_continuous
        (f := fun ts : ℝ × ℝ => (circleMap 0 r ts.1, circleMap 0 eta ts.2))
        (by fun_prop)
        (fun _ => ⟨circleMap_mem_sphere _ hr _, circleMap_mem_sphere _ heta _⟩)
    dsimp [J]
    simp only [deriv_circleMap]
    exact (by fun_prop : Continuous (fun ts : ℝ × ℝ =>
      circleMap 0 r ts.1 * Complex.I * (circleMap 0 eta ts.2 * Complex.I))).mul hg
  have hi : Integrable J ((volume.restrict (Icc 0 (2 * Real.pi))).prod
      (volume.restrict (Icc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hJ.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hf := integral_integral_swap (f := fun t u : ℝ => J (t, u)) hi
  simp_rw [circleIntegral_def_Icc, smul_eq_mul]
  simp_rw [← integral_const_mul]
  convert hf using 1 <;> congr 1 <;> funext t <;> congr 1 <;> funext u <;>
    dsimp [J, Function.uncurry] <;> ring

private lemma negativeContour_cauchy {K : ℂ → ℂ → ℂ} (s : ℕ)
    {r eta : ℝ} (hr : 0 ≤ r) (heta : 0 < eta)
    (hK : ContinuousOn (fun ax : ℂ × ℂ => K ax.1 ax.2)
      (sphere (0 : ℂ) r ×ˢ closedBall (0 : ℂ) eta))
    (hD : ∀ a ∈ sphere (0 : ℂ) r,
      DifferentiableOn ℂ (K a) (closedBall (0 : ℂ) eta))
    {x : ℂ} (hx : ‖x‖ < eta) :
    (2 * Real.pi * Complex.I)⁻¹ *
        (∮ xi in C(0, eta), (xi - x)⁻¹ * negativeContour (fun a => K a xi) s r) =
      negativeContour (fun a => K a x) s r := by
  let c : ℂ := (2 * Real.pi * Complex.I)⁻¹
  let G : ℂ → ℂ → ℂ := fun a xi => K a xi * a ^ s / (xi - x)
  have hden (xi : ℂ) (hxi : xi ∈ sphere (0 : ℂ) eta) : xi - x ≠ 0 := by
    have hn : ‖xi‖ = eta := by simpa using hxi
    intro he
    have : xi = x := sub_eq_zero.mp he
    rw [this] at hn
    linarith
  have hG : ContinuousOn (fun ax : ℂ × ℂ => G ax.1 ax.2)
      (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) eta) := by
    apply ((hK.mono (prod_mono Subset.rfl sphere_subset_closedBall)).mul
      (continuousOn_fst.pow s)).div (continuousOn_snd.sub continuousOn_const)
    exact fun ax hax => hden ax.2 hax.2
  have hswap := circleIntegral_swap hr heta.le hG
  have hInner (xi : ℂ) :
      (xi - x)⁻¹ * negativeContour (fun a => K a xi) s r =
        c * ∮ a in C(0, r), G a xi := by
    unfold negativeContour
    change (xi - x)⁻¹ * (c * ∮ a in C(0, r), K a xi * a ^ s) = _
    calc
      _ = c * ((xi - x)⁻¹ * ∮ a in C(0, r), K a xi * a ^ s) := by ring
      _ = _ := by
        rw [← circleIntegral.integral_const_mul]
        congr 1
        apply circleIntegral.integral_congr hr
        intro a _
        dsimp [G]
        ring
  have hCauchy (a : ℂ) (ha : a ∈ sphere (0 : ℂ) r) :
      c * (∮ xi in C(0, eta), G a xi) = K a x * a ^ s := by
    have he : (∮ xi in C(0, eta), G a xi) =
        a ^ s * ∮ xi in C(0, eta), (xi - x)⁻¹ * K a xi := by
      rw [← circleIntegral.integral_const_mul]
      apply circleIntegral.integral_congr heta.le
      intro xi _
      dsimp [G]
      ring
    have hformula := (hD a ha).circleIntegral_sub_inv_smul (by simpa using hx)
    simp only [smul_eq_mul] at hformula
    rw [he, hformula]
    dsimp [c]
    field_simp [Complex.two_pi_I_ne_zero]
    <;> ring
  change c * (∮ xi in C(0, eta),
    (xi - x)⁻¹ * negativeContour (fun a => K a xi) s r) = _
  simp_rw [hInner, circleIntegral.integral_const_mul]
  rw [← hswap, ← circleIntegral.integral_const_mul]
  unfold negativeContour
  congr 1
  exact circleIntegral.integral_congr hr hCauchy

private lemma integrated_powerSeries {K : ℂ → ℂ → ℂ} (s : ℕ)
    {r eta : ℝ} (hr : 0 ≤ r) (heta : 0 < eta)
    (hK : ContinuousOn (fun ax : ℂ × ℂ => K ax.1 ax.2)
      (sphere (0 : ℂ) r ×ˢ closedBall (0 : ℂ) eta))
    (hD : ∀ a ∈ sphere (0 : ℂ) r,
      DifferentiableOn ℂ (K a) (closedBall (0 : ℂ) eta)) :
    HasFPowerSeriesOnBall (fun x => negativeContour (fun a => K a x) s r)
      (cauchyPowerSeries (fun x => negativeContour (fun a => K a x) s r) 0 eta)
      0 (ENNReal.ofReal eta) := by
  have hi : CircleIntegrable (fun x => negativeContour (fun a => K a x) s r) 0 eta :=
    ((negativeContour_continuousOn s hr hK).mono sphere_subset_closedBall).circleIntegrable heta.le
  have hp := hasFPowerSeriesOn_cauchy_integral (R := (⟨eta, heta.le⟩ : ℝ≥0)) hi
    (show (0 : ℝ≥0) < ⟨eta, heta.le⟩ from heta)
  have hp' : HasFPowerSeriesOnBall
      (fun x => (2 * Real.pi * Complex.I)⁻¹ •
        ∮ xi in C(0, eta), (xi - x)⁻¹ • negativeContour (fun a => K a xi) s r)
      (cauchyPowerSeries (fun x => negativeContour (fun a => K a x) s r) 0 eta)
      0 (ENNReal.ofReal eta) := by
    convert hp using 1 <;> first | rfl | exact ENNReal.ofReal_eq_coe_nnreal heta.le
  have hc := hp'.congr (fun x hx => by
    have hx' : ‖x‖ < eta := by
      rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_ofReal_iff heta] at hx
      exact hx
    simpa only [smul_eq_mul, NNReal.coe_mk] using negativeContour_cauchy s hr heta hK hD hx')
  exact hc

private lemma cauchy_coefficient_eq (f : ℂ → ℂ) (d : ℕ) (eta : ℝ) :
    (cauchyPowerSeries f 0 eta).coeff d =
      (2 * Real.pi * Complex.I)⁻¹ * ∮ xi in C(0, eta), f xi / xi ^ (d + 1) := by
  change cauchyPowerSeries f 0 eta d (fun _ => 1) = _
  rw [cauchyPowerSeries]
  simp only [ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const, sub_zero,
    smul_eq_mul, one_pow, one_mul]
  congr 1
  congr 1
  funext xi
  simp only [div_eq_mul_inv, pow_succ, mul_inv_rev, inv_pow]
  ring

private lemma cauchy_term_eq_doubleContour (K : ℂ → ℂ → ℂ)
    (s d : ℕ) (r eta : ℝ) (x : ℂ) :
    cauchyPowerSeries (fun xi => negativeContour (fun a => K a xi) s r) 0 eta d
        (fun _ => x) = doubleContour K s d r eta * x ^ d := by
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, cauchy_coefficient_eq]
  unfold doubleContour
  simp only [smul_eq_mul]
  ring

private lemma doubleContour_swap {K : ℂ → ℂ → ℂ} (s d : ℕ)
    {r eta : ℝ} (hr : 0 ≤ r) (heta : 0 < eta)
    (hK : ContinuousOn (fun ax : ℂ × ℂ => K ax.1 ax.2)
      (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) eta)) :
    doubleContour K s d r eta =
      negativeContour (fun a => (cauchyPowerSeries (K a) 0 eta).coeff d) s r := by
  let c : ℂ := (2 * Real.pi * Complex.I)⁻¹
  let G : ℂ → ℂ → ℂ := fun a xi => K a xi * a ^ s / xi ^ (d + 1)
  have hn (xi : ℂ) (hxi : xi ∈ sphere (0 : ℂ) eta) : xi ^ (d + 1) ≠ 0 := by
    apply pow_ne_zero
    apply norm_pos_iff.mp
    have he : ‖xi‖ = eta := by simpa using hxi
    linarith
  have hG : ContinuousOn (fun ax : ℂ × ℂ => G ax.1 ax.2)
      (sphere (0 : ℂ) r ×ˢ sphere (0 : ℂ) eta) :=
    (hK.mul (continuousOn_fst.pow s)).div (continuousOn_snd.pow _) (fun ax hax => hn _ hax.2)
  have hswap := circleIntegral_swap hr heta.le hG
  have hleft (xi : ℂ) :
      (c * ∮ a in C(0, r), K a xi * a ^ s) / xi ^ (d + 1) =
        c * ∮ a in C(0, r), G a xi := by
    have he := circleIntegral.integral_smul_const (fun a => K a xi * a ^ s)
      ((xi ^ (d + 1))⁻¹) 0 r
    simp only [smul_eq_mul] at he
    calc
      _ = c * ((∮ a in C(0, r), K a xi * a ^ s) * (xi ^ (d + 1))⁻¹) := by ring
      _ = _ := by rw [← he]; rfl
  have hright (a : ℂ) :
      (c * ∮ xi in C(0, eta), K a xi / xi ^ (d + 1)) * a ^ s =
        c * ∮ xi in C(0, eta), G a xi := by
    have he := circleIntegral.integral_smul_const (fun xi => K a xi / xi ^ (d + 1))
      (a ^ s) 0 eta
    simp only [smul_eq_mul] at he
    calc
      _ = c * ((∮ xi in C(0, eta), K a xi / xi ^ (d + 1)) * a ^ s) := by ring
      _ = c * ∮ xi in C(0, eta), (K a xi / xi ^ (d + 1)) * a ^ s := by rw [he]
      _ = _ := by
        congr 1
        congr 1
        funext xi
        dsimp [G]
        ring
  unfold doubleContour negativeContour
  simp_rw [cauchy_coefficient_eq]
  change c * (∮ xi in C(0, eta), (c * ∮ a in C(0, r), K a xi * a ^ s) / xi ^ (d + 1)) =
    c * ∮ a in C(0, r), (c * ∮ xi in C(0, eta), K a xi / xi ^ (d + 1)) * a ^ s
  simp_rw [hleft, hright, circleIntegral.integral_const_mul]
  rw [hswap]

private lemma literal_differentiable_closedBall {b a : ℂ} (hb : b ≠ 0) (root : ℂ)
    {r eta : ℝ} (har : a ∈ sphere (0 : ℂ) r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) :
    DifferentiableOn ℂ (fun x => TT b root a x) (closedBall (0 : ℂ) eta) ∧
      DifferentiableOn ℂ (fun x => UT b root a x) (closedBall (0 : ℂ) eta) := by
  obtain ⟨R, hetaR, hRb⟩ := exists_between hetab
  have hR : 0 < R := heta.trans hetaR
  have ha : ‖a‖ = r := by simpa using har
  obtain ⟨hT, hU⟩ := literal_modulus_series (a := a) hb root (by simpa [ha] using hrb)
    (eta := (⟨R, hR.le⟩ : ℝ≥0)) hR (by change R < ‖a‖ * beta b; simpa [ha] using hRb)
  have hmem (x : ℂ) (hx : x ∈ closedBall (0 : ℂ) eta) :
      x ∈ eball (0 : ℂ) (ENNReal.ofReal R) := by
    have hxeta : ‖x‖ ≤ eta := by simpa using hx
    have : ‖x‖ < R := hxeta.trans_lt hetaR
    rw [Metric.mem_eball, edist_dist, dist_zero_right, ENNReal.ofReal_lt_ofReal_iff hR]
    exact this
  constructor
  · intro x hx
    apply (hT.analyticAt_of_mem ?_).differentiableAt.differentiableWithinAt
    erw [← ENNReal.ofReal_coe_nnreal]
    change x ∈ eball (0 : ℂ) (ENNReal.ofReal R)
    exact hmem x hx
  · intro x hx
    apply (hU.analyticAt_of_mem ?_).differentiableAt.differentiableWithinAt
    erw [← ENNReal.ofReal_coe_nnreal]
    change x ∈ eball (0 : ℂ) (ENNReal.ofReal R)
    exact hmem x hx

/-- The parameterized inner integrals are continuous on every strict closed disk;
their outer coefficient integrals are genuine integrable circle integrals. -/
theorem integrated_contour_continuity {b : ℂ} (hb : b ≠ 0) (root : ℂ) (s d : ℕ)
    {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) :
    ContinuousOn (fun x => negativeContour (fun a => TT b root a x) s r)
        (closedBall (0 : ℂ) eta) ∧
    ContinuousOn (fun x => negativeContour (fun a => UT b root a x) s r)
        (closedBall (0 : ℂ) eta) ∧
    CircleIntegrable (fun x => negativeContour (fun a => TT b root a x) s r / x ^ (d + 1))
        0 eta ∧
    CircleIntegrable (fun x => negativeContour (fun a => UT b root a x) s r / x ^ (d + 1))
        0 eta := by
  obtain ⟨hT, hU⟩ := kernels_continuousOn hb root hrb hetab
  have hcT := negativeContour_continuousOn s hr.le hT
  have hcU := negativeContour_continuousOn s hr.le hU
  have hn (x : ℂ) (hx : x ∈ sphere (0 : ℂ) eta) : x ^ (d + 1) ≠ 0 := by
    apply pow_ne_zero
    apply norm_pos_iff.mp
    have : ‖x‖ = eta := by simpa using hx
    linarith
  exact ⟨hcT, hcU,
    ((hcT.mono sphere_subset_closedBall).div (continuousOn_id.pow _) hn).circleIntegrable heta.le,
    ((hcU.mono sphere_subset_closedBall).div (continuousOn_id.pow _) hn).circleIntegrable heta.le⟩

/-- Integration of the actual kernels has a Cauchy Taylor series on each fixed strict disk. -/
theorem integrated_literal_powerSeries {b : ℂ} (hb : b ≠ 0) (root : ℂ) (s : ℕ)
    {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) :
    HasFPowerSeriesOnBall (fun x => negativeContour (fun a => TT b root a x) s r)
      (cauchyPowerSeries (fun x => negativeContour (fun a => TT b root a x) s r) 0 eta)
      0 (ENNReal.ofReal eta) ∧
    HasFPowerSeriesOnBall (fun x => negativeContour (fun a => UT b root a x) s r)
      (cauchyPowerSeries (fun x => negativeContour (fun a => UT b root a x) s r) 0 eta)
      0 (ENNReal.ofReal eta) := by
  obtain ⟨hT, hU⟩ := kernels_continuousOn hb root hrb hetab
  exact ⟨integrated_powerSeries s hr.le heta hT
      (fun a ha => (literal_differentiable_closedBall hb root ha hrb heta hetab).1),
    integrated_powerSeries s hr.le heta hU
      (fun a ha => (literal_differentiable_closedBall hb root ha hrb heta hetab).2)⟩

/-- The Taylor coefficients here are the actual iterated contours, without a
formal coefficient-correspondence premise. -/
theorem integrated_literal_hasSum {b x : ℂ} (hb : b ≠ 0) (root : ℂ) (s : ℕ)
    {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) (hx : ‖x‖ < eta) :
    HasSum (fun d : ℕ => doubleContour (TT b root) s d r eta * x ^ d) (Tcoeff b root s x) ∧
    HasSum (fun d : ℕ => doubleContour (UT b root) s d r eta * x ^ d) (Ucoeff b root s x) := by
  obtain ⟨hT, hU⟩ := integrated_literal_powerSeries hb root s hr hrb heta hetab
  have hmem : x ∈ eball (0 : ℂ) (ENNReal.ofReal eta) := by
    rw [ENNReal.ofReal_eq_coe_nnreal heta.le]
    exact (mem_complex_eball (R := (⟨eta, heta.le⟩ : ℝ≥0))).mpr hx
  have hxB : ‖x‖ < beta b ^ 2 := by
    have hB := beta_positive hb
    have hprod : r * beta b < beta b ^ 2 := by nlinarith
    exact hx.trans (hetab.trans hprod)
  have hinner : ‖x‖ / beta b < r :=
    (div_lt_iff₀ (beta_positive hb)).mpr (hx.trans hetab)
  obtain ⟨hTc, hUc, _, _⟩ := coefficients_on_fixed_contour hb hxB root s hr hinner hrb
  constructor
  · simpa only [zero_add, cauchy_term_eq_doubleContour, ← hTc] using hT.hasSum hmem
  · simpa only [zero_add, cauchy_term_eq_doubleContour, ← hUc] using hU.hasSum hmem

/-- Each modulus coefficient can be computed by first taking the literal
fixed-a Taylor coefficient and then performing the annular mode integral. -/
theorem doubleContour_eq_integrated_cauchy {b : ℂ} (hb : b ≠ 0) (root : ℂ) (s d : ℕ)
    {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) :
    doubleContour (TT b root) s d r eta =
      negativeContour (fun a => (cauchyPowerSeries (TT b root a) 0 eta).coeff d) s r ∧
    doubleContour (UT b root) s d r eta =
      negativeContour (fun a => (cauchyPowerSeries (UT b root a) 0 eta).coeff d) s r := by
  obtain ⟨hT, hU⟩ := kernels_continuousOn hb root hrb hetab
  exact ⟨doubleContour_swap s d hr.le heta
      (hT.mono (prod_mono Subset.rfl sphere_subset_closedBall)),
    doubleContour_swap s d hr.le heta
      (hU.mono (prod_mono Subset.rfl sphere_subset_closedBall))⟩

/-- Termwise integration of the genuine Taylor series in the modulus. -/
theorem integrated_literal_termwise {b x : ℂ} (hb : b ≠ 0) (root : ℂ) (s : ℕ)
    {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) (hx : ‖x‖ < eta) :
    HasSum (fun d : ℕ =>
      negativeContour (fun a => (cauchyPowerSeries (TT b root a) 0 eta).coeff d) s r * x ^ d)
        (Tcoeff b root s x) ∧
    HasSum (fun d : ℕ =>
      negativeContour (fun a => (cauchyPowerSeries (UT b root a) 0 eta).coeff d) s r * x ^ d)
        (Ucoeff b root s x) := by
  have hc := integrated_literal_hasSum hb root s hr hrb heta hetab hx
  have hT (d : ℕ) := (doubleContour_eq_integrated_cauchy hb root s d hr hrb heta hetab).1
  have hU (d : ℕ) := (doubleContour_eq_integrated_cauchy hb root s d hr hrb heta hetab).2
  simpa only [hT, hU] using hc

private lemma integrated_coefficients_at {b : ℂ} (hb : b ≠ 0) (root : ℂ) (s : ℕ)
    {r eta : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) :
    HasFPowerSeriesAt (Tcoeff b root s)
      (.ofScalars ℂ (fun d => doubleContour (TT b root) s d r eta)) 0 ∧
    HasFPowerSeriesAt (Ucoeff b root s)
      (.ofScalars ℂ (fun d => doubleContour (UT b root) s d r eta)) 0 := by
  constructor
  · apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) heta] with x hx
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm] using
      (integrated_literal_hasSum hb root s hr hrb heta hetab (show ‖x‖ < eta by simpa using hx)).1
  · apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) heta] with x hx
    simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add, mul_comm] using
      (integrated_literal_hasSum hb root s hr hrb heta hetab (show ‖x‖ < eta by simpa using hx)).2

/-- Neither contour radius affects the actual mode/Taylor coefficients. -/
theorem double_contours_independent {b : ℂ} (hb : b ≠ 0) (root : ℂ) (s d : ℕ)
    {r eta R E : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b)
    (hR : 0 < R) (hRb : R < beta b) (hE : 0 < E) (hEb : E < R * beta b) :
    doubleContour (TT b root) s d r eta = doubleContour (TT b root) s d R E ∧
      doubleContour (UT b root) s d r eta = doubleContour (UT b root) s d R E := by
  obtain ⟨hT, hU⟩ := integrated_coefficients_at hb root s hr hrb heta hetab
  obtain ⟨hT', hU'⟩ := integrated_coefficients_at hb root s hR hRb hE hEb
  constructor
  · simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff d)
        (hT.eq_formalMultilinearSeries hT')
  · simpa only [FormalMultilinearSeries.coeff_ofScalars] using
      congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff d)
        (hU.eq_formalMultilinearSeries hU')

/-- The integrated Taylor series converge uniformly on every smaller closed
disk, by the actual two-index Cauchy majorant. -/
theorem integrated_literal_uniform {b : ℂ} (hb : b ≠ 0) (root : ℂ) (s : ℕ)
    {r eta R : ℝ} (hr : 0 < r) (hrb : r < beta b)
    (heta : 0 < eta) (hetab : eta < r * beta b) (hR : 0 ≤ R) (hReta : R < eta) :
    TendstoUniformlyOn
      (fun N x => ∑ d ∈ Finset.range N, doubleContour (TT b root) s d r eta * x ^ d)
      (Tcoeff b root s) atTop (closedBall (0 : ℂ) R) ∧
    TendstoUniformlyOn
      (fun N x => ∑ d ∈ Finset.range N, doubleContour (UT b root) s d r eta * x ^ d)
      (Ucoeff b root s) atTop (closedBall (0 : ℂ) R) := by
  obtain ⟨M, hM, hbound⟩ := double_contours_bound hb root hr hrb heta hetab
  have hs : Summable (fun d : ℕ => (M * r ^ (s + 1)) * (R / eta) ^ d) :=
    (summable_geometric_of_lt_one (div_nonneg hR heta.le)
      ((div_lt_one heta).mpr hReta)).mul_left _
  have hterm (c : ℂ) (d : ℕ) (hc : ‖c‖ ≤ M * r ^ (s + 1) / eta ^ d)
      (x : ℂ) (hx : x ∈ closedBall (0 : ℂ) R) :
      ‖c * x ^ d‖ ≤ (M * r ^ (s + 1)) * (R / eta) ^ d := by
    have hxR : ‖x‖ ≤ R := by simpa using hx
    rw [norm_mul, norm_pow, div_pow]
    calc
      _ ≤ (M * r ^ (s + 1) / eta ^ d) * R ^ d :=
        mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg x) hxR _)
          (pow_nonneg (norm_nonneg x) _) (by positivity)
      _ = _ := by ring
  have hTu := tendstoUniformlyOn_tsum_nat hs
    (fun d x hx => hterm _ d (hbound s d).1 x hx)
  have hUu := tendstoUniformlyOn_tsum_nat hs
    (fun d x hx => hterm _ d (hbound s d).2 x hx)
  constructor
  · apply hTu.congr_right
    intro x hx
    exact (integrated_literal_hasSum hb root s hr hrb heta hetab
      ((show ‖x‖ ≤ R by simpa using hx).trans_lt hReta)).1.tsum_eq
  · apply hUu.congr_right
    intro x hx
    exact (integrated_literal_hasSum hb root s hr hrb heta hetab
      ((show ‖x‖ ≤ R by simpa using hx).trans_lt hReta)).2.tsum_eq

/-- Actual scalar coefficient functions are analytic on the entire modulus
disk, using a locally fixed admissible contour at every point. -/
theorem original_coefficients_analytic {b x : ℂ} (hb : b ≠ 0) (root : ℂ) (s : ℕ)
    (hx : ‖x‖ < beta b ^ 2) :
    AnalyticAt ℂ (Tcoeff b root s) x ∧ AnalyticAt ℂ (Ucoeff b root s) x := by
  have hB := beta_positive hb
  have hinner : ‖x‖ / beta b < beta b := by
    apply (div_lt_iff₀ hB).mpr
    nlinarith
  obtain ⟨r, hxr, hrb⟩ := exists_between hinner
  have hr : 0 < r := (div_nonneg (norm_nonneg x) hB.le).trans_lt hxr
  have hxrb : ‖x‖ < r * beta b := (div_lt_iff₀ hB).mp hxr
  obtain ⟨eta, hxeta, hetab⟩ := exists_between hxrb
  have heta : 0 < eta := (norm_nonneg x).trans_lt hxeta
  obtain ⟨hT, hU⟩ := integrated_literal_powerSeries hb root s hr hrb heta hetab
  have hmem : x ∈ eball (0 : ℂ) (ENNReal.ofReal eta) := by
    rw [ENNReal.ofReal_eq_coe_nnreal heta.le]
    exact (mem_complex_eball (R := (⟨eta, heta.le⟩ : ℝ≥0))).mpr hxeta
  have heq : (fun w => negativeContour (fun a => TT b root a w) s r) =ᶠ[𝓝 x]
      Tcoeff b root s ∧
      (fun w => negativeContour (fun a => UT b root a w) s r) =ᶠ[𝓝 x]
        Ucoeff b root s := by
    have hall : ∀ᶠ w in 𝓝 x,
        Tcoeff b root s w = negativeContour (fun a => TT b root a w) s r ∧
        Ucoeff b root s w = negativeContour (fun a => UT b root a w) s r := by
      filter_upwards [isOpen_ball.mem_nhds (show x ∈ ball (0 : ℂ) eta by simpa using hxeta)]
        with w hw
      have hweta : ‖w‖ < eta := by simpa using hw
      have hwB : ‖w‖ < beta b ^ 2 := by
        have hprod : r * beta b < beta b ^ 2 := by nlinarith
        exact hweta.trans (hetab.trans hprod)
      have hwinner : ‖w‖ / beta b < r := (div_lt_iff₀ hB).mpr (hweta.trans hetab)
      have h := coefficients_on_fixed_contour hb hwB root s hr hwinner hrb
      exact ⟨h.1, h.2.1⟩
    exact ⟨hall.mono (fun _ h => h.1.symm), hall.mono (fun _ h => h.2.symm)⟩
  exact ⟨(hT.analyticAt_of_mem hmem).congr heq.1, (hU.analyticAt_of_mem hmem).congr heq.2⟩

end D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianCubicAnalyticCoefficientBridge
