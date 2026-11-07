/- GID: D5/S3/Analytic/Probability/GaussianPolynomialLog
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/GaussianPolynomialLog
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian polynomial logarithms and small-noise orders. -/
/-
admission_basis: escape-witness
escape_witness: D5.S3.Analytic.Probability.GaussianPolynomialLog.log_root_lower_point
Declaration proof shapes (names relative to this module):
  negLog_zero_of_one_le; proof_shape: bind-only; escape_witness: none; consumer: negLog_integrable
  negLog_integrable; proof_shape: bind-only; escape_witness: none; consumer: negLog_integrable_shift
  negLog_integrable_shift; proof_shape: bind-only; escape_witness: none; consumer: bounded_density_negLog
  bounded_density_negLog; proof_shape: bind-only; escape_witness: none; consumer: gaussian_negLog
  gaussian_negLog; proof_shape: bind-only; escape_witness: none; consumer: gaussian_root_log_integrable
  log_norm_sub_bound; proof_shape: bind-only; escape_witness: none; consumer: gaussian_root_log_integrable
  gaussian_root_log_integrable; proof_shape: bind-only; escape_witness: none; consumer: gaussian_product_log_integrable
  log_root_lower_point; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.GaussianPolynomialLog.log_root_lower_point; consumer: gaussian_root_log_lower
  gaussian_root_log_lower; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.GaussianPolynomialLog.log_root_lower_point; consumer: gaussian_polynomial_log_mahler_lower
  gaussian_roots_nonzero; proof_shape: bind-only; escape_witness: none; consumer: gaussian_polynomial_log_integrable
  gaussian_product_log_integrable; proof_shape: bind-only; escape_witness: none; consumer: gaussian_polynomial_log_integrable
  gaussian_polynomial_log_integrable; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower
  gaussian_product_log_integral; proof_shape: bind-only; escape_witness: none; consumer: gaussian_polynomial_log_integral
  gaussian_polynomial_log_integral; proof_shape: bind-only; escape_witness: none; consumer: gaussian_polynomial_log_mahler_lower
  rootLogCost; proof_shape: bind-only; escape_witness: none; consumer: gaussian_polynomial_log_coeff_lower
  rootLogCost_nonneg; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower
  gaussian_polynomial_log_mahler_lower; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.GaussianPolynomialLog.log_root_lower_point; consumer: gaussian_polynomial_log_coeff_lower
  gaussian_polynomial_log_coeff_lower; proof_shape: content; escape_witness: D5.S3.Analytic.Probability.GaussianPolynomialLog.log_root_lower_point; consumer: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower
  gaussian_complex_pow_integrable; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_eval_integrable
  norm_eq_two_pos_sub; proof_shape: bind-only; escape_witness: none; consumer: integrable_prod_of_pos_and_fiber_lower
  integrable_prod_of_pos_and_fiber_lower; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceSpectralAndSmooth.Gaussian.gaussian_mv_log_coeff_lower
  Covariance.X_pow_dvd_det_of_entry_weights; proof_shape: bind-only; escape_witness: none; consumer: Covariance.rankOne_order_lower
  Covariance.natDegree_det_le_of_entries; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_degree_le
  Covariance.affineGramPoly; proof_shape: bind-only; escape_witness: none; consumer: Covariance.affineGramPoly_coeff_two
  Covariance.pairDet; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_degree_le
  Covariance.rankOneGramPoly; proof_shape: bind-only; escape_witness: none; consumer: Covariance.affineGramPoly_rankOneBase
  Covariance.affineGramPoly_rankOneBase; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_rankOne_witness
  Covariance.rowWeight; proof_shape: bind-only; escape_witness: none; consumer: Covariance.rankOne_entry_divisibility
  Covariance.colWeight; proof_shape: bind-only; escape_witness: none; consumer: Covariance.colWeight_sum
  Covariance.rankOne_entry_divisibility; proof_shape: bind-only; escape_witness: none; consumer: Covariance.rankOne_order_lower
  Covariance.rowWeight_sum; proof_shape: bind-only; escape_witness: none; consumer: Covariance.rankOne_order_lower
  Covariance.colWeight_sum; proof_shape: bind-only; escape_witness: none; consumer: Covariance.rankOne_order_lower
  Covariance.rankOne_order_lower; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder.pairDet_common_lower
  Covariance.rankOneGramPoly_one; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_rankOne_witness
  Covariance.rankOneGramPoly_zero; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_rankOne_witness
  Covariance.pairDet_rankOne_witness; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_rankOne_witness_order
  Covariance.affineGramPoly_degree_le; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_degree_le
  Covariance.pairDet_degree_le; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.Noise.poly_degree_le
  Covariance.coeff_det_card_mul_of_entry_degree_le; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_identity_noise_topCoeff
  Covariance.affineGramPoly_coeff_two; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_identity_noise_topCoeff
  Covariance.pairDet_identity_noise_topCoeff; proof_shape: bind-only; escape_witness: none; consumer: Covariance.pairDet_identity_noise_ne_zero
  Covariance.pairDet_identity_noise_ne_zero; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder.poly_common_order
  Covariance.pairDet_rankOne_witness_order; proof_shape: bind-only; escape_witness: none; consumer: D5.S3.Analytic.Probability.SampleCovarianceBernoulliOrders.CommonOrder.diagonal_witness_order
Direct frozen dependencies:
  none
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/27612
-/
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Probability.Distributions.Gaussian.Real
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal NNReal
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace D5.S3.Analytic.Probability.GaussianPolynomialLog
noncomputable section

private lemma negLog_zero_of_one_le {x : ℝ} (hx : 1 ≤ |x|) : (fun t : ℝ => max (-Real.log |t|) 0) x = 0 := by
  exact max_eq_right (neg_nonpos.mpr (Real.log_nonneg hx))

private lemma negLog_integrable : Integrable (fun t : ℝ => max (-Real.log |t|) 0) (volume : Measure ℝ) := by
  have hi : IntegrableOn (fun t : ℝ => max (-Real.log |t|) 0) (Icc (-1) 1) := by
    have hlog : IntegrableOn Real.log (Icc (-1) 1) :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp
        intervalIntegral.intervalIntegrable_log'
    have hz : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Icc (-1) 1) := integrable_zero ℝ ℝ _
    have hh := hlog.neg.sup hz
    change IntegrableOn (fun x : ℝ => max (-Real.log x) 0) (Icc (-1) 1) at hh
    change Integrable (fun x : ℝ => max (-Real.log |x|) 0) (volume.restrict (Icc (-1) 1))
    change Integrable (fun x : ℝ => max (-Real.log x) 0) (volume.restrict (Icc (-1) 1)) at hh
    simpa only [Real.log_abs] using hh
  have hh := hi.integrable_indicator measurableSet_Icc
  apply hh.congr
  filter_upwards [] with x
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · simp [hx]
  · rw [indicator_of_notMem hx]
    exact (negLog_zero_of_one_le (by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · rw [abs_of_neg (by linarith)]; linarith
      · exact le_trans (by linarith) (le_abs_self x))).symm

private lemma negLog_integrable_shift (a : ℝ) :
    Integrable (fun x => (fun t : ℝ => max (-Real.log |t|) 0) (x-a)) (volume : Measure ℝ) :=
  negLog_integrable.comp_sub_right a

private lemma bounded_density_negLog (ρ : ℝ → ℝ≥0∞) (M : ℝ) (hM : 0 ≤ M)
    (hρ : ∀ x, ρ x ≤ ENNReal.ofReal M) (a : ℝ) :
    Integrable (fun x => (fun t : ℝ => max (-Real.log |t|) 0) (x-a)) (volume.withDensity ρ) ∧
      (∫ x, (fun t : ℝ => max (-Real.log |t|) 0) (x-a) ∂volume.withDensity ρ) ≤
        M * ∫ x, (fun t : ℝ => max (-Real.log |t|) 0) x := by
  have hle : (volume : Measure ℝ).withDensity ρ ≤ ENNReal.ofReal M • volume := by
    rw [← withDensity_const]
    exact withDensity_mono (Filter.Eventually.of_forall hρ)
  have hi : Integrable (fun x => (fun t : ℝ => max (-Real.log |t|) 0) (x-a)) (ENNReal.ofReal M • volume) :=
    (negLog_integrable_shift a).smul_measure (by simp)
  refine ⟨hi.mono_measure hle, ?_⟩
  calc
    _ ≤ ∫ x, (fun t : ℝ => max (-Real.log |t|) 0) (x-a) ∂(ENNReal.ofReal M • volume) :=
      integral_mono_measure hle (Filter.Eventually.of_forall (fun x => le_max_right _ _)) hi
    _ = _ := by
      simp only [integral_smul_measure, ENNReal.toReal_ofReal hM, smul_eq_mul]
      congr 1
      exact integral_sub_right_eq_self (fun t : ℝ => max (-Real.log |t|) 0) a

private lemma gaussian_negLog (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (a : ℝ) :
    Integrable (fun x => (fun t : ℝ => max (-Real.log |t|) 0) (x-a)) (gaussianReal m v) ∧
      (∫ x, (fun t : ℝ => max (-Real.log |t|) 0) (x-a) ∂gaussianReal m v) ≤
        (Real.sqrt (2 * Real.pi * v))⁻¹ * ∫ x, (fun t : ℝ => max (-Real.log |t|) 0) x := by
  rw [gaussianReal_of_var_ne_zero m hv]
  apply bounded_density_negLog
  · positivity
  · intro x
    apply ENNReal.ofReal_le_ofReal
    unfold gaussianPDFReal
    apply mul_le_of_le_one_right (by positivity)
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · exact neg_nonpos.mpr (sq_nonneg _)
    · positivity

private lemma log_norm_sub_bound (x : ℝ) (z : ℂ) (hx : x ≠ z.re) :
    |Real.log ‖(x : ℂ) - z‖| ≤ |x| + ‖z‖ + (fun t : ℝ => max (-Real.log |t|) 0) (x-z.re) := by
  have hp : 0 < |x-z.re| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hdist : |x-z.re| ≤ ‖(x : ℂ)-z‖ := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm ((x : ℂ)-z)
  have hdpos : 0 < ‖(x : ℂ)-z‖ := hp.trans_le hdist
  have hlog : Real.log |x-z.re| ≤ Real.log ‖(x : ℂ)-z‖ :=
    Real.log_le_log hp hdist
  have hupper : Real.log ‖(x : ℂ)-z‖ ≤ |x| + ‖z‖ := by
    have h := Real.log_le_sub_one_of_pos hdpos
    have hn := norm_sub_le (x : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs] at hn
    linarith
  have hneg : -Real.log ‖(x : ℂ)-z‖ ≤ (fun t : ℝ => max (-Real.log |t|) 0) (x-z.re) :=
    (neg_le_neg hlog).trans (le_max_left _ _)
  apply abs_le.mpr
  constructor
  · linarith [abs_nonneg x, norm_nonneg z]
  · linarith [le_max_right (-Real.log |x-z.re|) 0]

private lemma gaussian_root_log_integrable (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (z : ℂ) :
    Integrable (fun x : ℝ => Real.log ‖(x : ℂ)-z‖) (gaussianReal m v) := by
  letI := nullSingletonClass_gaussianReal (μ := m) hv
  have hid : Integrable (fun x : ℝ => |x|) (gaussianReal m v) := by
    simpa only [Real.norm_eq_abs, id_eq] using
      ((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable (by norm_num)).norm
  have hi := (hid.add (integrable_const ‖z‖)).add (gaussian_negLog m v hv z.re).1
  apply hi.mono' ((Real.measurable_log.comp
    (Complex.continuous_ofReal.sub continuous_const).norm.measurable).aestronglyMeasurable)
  filter_upwards [Measure.ae_ne (gaussianReal m v) z.re] with x hx
  exact log_norm_sub_bound x z hx

private lemma log_root_lower_point (x : ℝ) (z : ℂ) (hx : x ≠ z.re) :
    Real.log (max 1 ‖z‖) - |x| - (fun t : ℝ => max (-Real.log |t|) 0) (x-z.re) ≤
      Real.log ‖(x : ℂ)-z‖ := by
  let d := ‖(x : ℂ)-z‖
  have hp : 0 < |x-z.re| := abs_pos.mpr (sub_ne_zero.mpr hx)
  have hdist : |x-z.re| ≤ d := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using
      Complex.abs_re_le_norm ((x : ℂ)-z)
  have hd : 0 < d := hp.trans_le hdist
  have hzn : ‖z‖ ≤ |x| + d := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      norm_le_norm_add_norm_sub (x : ℂ) z
  have hm1 : 1 ≤ max 1 d := le_max_left _ _
  have hmd : d ≤ max 1 d := le_max_right _ _
  have hb : max 1 ‖z‖ ≤ max 1 d * (1+|x|) := by
    apply max_le
    · nlinarith [abs_nonneg x, mul_nonneg (sub_nonneg.mpr hm1) (abs_nonneg x)]
    · nlinarith [abs_nonneg x, mul_nonneg (sub_nonneg.mpr hm1) (abs_nonneg x)]
  have hlog := Real.log_le_log (by positivity : 0 < max 1 ‖z‖) hb
  rw [Real.log_mul (by positivity : max 1 d ≠ 0)
    (by positivity : 1+|x| ≠ 0)] at hlog
  have he : Real.log (max 1 d) = max (Real.log d) 0 := by
    by_cases hd1 : d ≤ 1
    · rw [max_eq_left hd1, Real.log_one,
        max_eq_right (Real.log_nonpos hd.le hd1)]
    · rw [max_eq_right (le_of_not_ge hd1),
        max_eq_left (Real.log_nonneg (le_of_not_ge hd1))]
  have hm : max (Real.log d) 0 ≤ Real.log d + (fun t : ℝ => max (-Real.log |t|) 0) (x-z.re) := by
    apply max_le
    · linarith [le_max_right (-Real.log |x-z.re|) 0]
    · have hh := Real.log_le_log hp hdist
      have hn : -Real.log |x-z.re| ≤ (fun t : ℝ => max (-Real.log |t|) 0) (x-z.re) := le_max_left _ _
      linarith
  have ht := Real.log_le_sub_one_of_pos (show 0 < 1+|x| by positivity)
  rw [he] at hlog
  dsimp only [d] at *
  linarith

private lemma gaussian_root_log_lower (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) (z : ℂ) :
    Real.log (max 1 ‖z‖) - (∫ x : ℝ, |x| ∂gaussianReal m v) -
      (Real.sqrt (2 * Real.pi * v))⁻¹ * (∫ x, (fun t : ℝ => max (-Real.log |t|) 0) x) ≤
        ∫ x : ℝ, Real.log ‖(x : ℂ)-z‖ ∂gaussianReal m v := by
  letI := nullSingletonClass_gaussianReal (μ := m) hv
  have hid : Integrable (fun x : ℝ => |x|) (gaussianReal m v) := by
    simpa only [Real.norm_eq_abs, id_eq] using
      ((memLp_id_gaussianReal (μ := m) (v := v) 1).integrable (by norm_num)).norm
  have hn := gaussian_negLog m v hv z.re
  have hi := ((integrable_const (Real.log (max 1 ‖z‖))).sub hid).sub hn.1
  have hb := integral_mono_ae hi (gaussian_root_log_integrable m v hv z) (by
    filter_upwards [Measure.ae_ne (gaussianReal m v) z.re] with x hx
    exact log_root_lower_point x z hx)
  have hconst : Integrable (fun _ : ℝ => Real.log (max 1 ‖z‖)) (gaussianReal m v) :=
    integrable_const _
  calc
    _ ≤ Real.log (max 1 ‖z‖) - (∫ x : ℝ, |x| ∂gaussianReal m v) -
        (∫ x : ℝ, (fun t : ℝ => max (-Real.log |t|) 0) (x-z.re) ∂gaussianReal m v) := sub_le_sub_left hn.2 _
    _ = ∫ x : ℝ, Real.log (max 1 ‖z‖) - |x| - (fun t : ℝ => max (-Real.log |t|) 0) (x-z.re) ∂gaussianReal m v := by
      symm
      calc
        _ = (∫ x : ℝ, Real.log (max 1 ‖z‖) - |x| ∂gaussianReal m v) -
            (∫ x : ℝ, (fun t : ℝ => max (-Real.log |t|) 0) (x-z.re) ∂gaussianReal m v) :=
          integral_sub (hconst.sub hid) hn.1
        _ = _ := by
          rw [integral_sub hconst hid, integral_const]
          simp only [probReal_univ, one_smul]
    _ ≤ _ := hb

lemma gaussian_roots_nonzero (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (s : Multiset ℂ) :
    ∀ᵐ x : ℝ ∂gaussianReal m v, (s.map (fun z => (x : ℂ)-z)).prod ≠ 0 := by
  letI := nullSingletonClass_gaussianReal (μ := m) hv
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    filter_upwards [Measure.ae_ne (gaussianReal m v) z.re, ih] with x hx hs
    simp only [Multiset.map_cons, Multiset.prod_cons, mul_ne_zero_iff]
    refine ⟨?_, hs⟩
    intro he
    apply hx
    have hre := congrArg Complex.re (sub_eq_zero.mp he)
    simpa using hre

private lemma gaussian_product_log_integrable (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (s : Multiset ℂ) :
    Integrable (fun x : ℝ => Real.log ‖(s.map (fun z => (x : ℂ)-z)).prod‖)
      (gaussianReal m v) := by
  letI := nullSingletonClass_gaussianReal (μ := m) hv
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    apply ((gaussian_root_log_integrable m v hv z).add ih).congr
    filter_upwards [Measure.ae_ne (gaussianReal m v) z.re,
      gaussian_roots_nonzero m v hv s] with x hx hs
    have hz : (x : ℂ)-z ≠ 0 := by
      intro he
      apply hx
      simpa using congrArg Complex.re (sub_eq_zero.mp he)
    simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul, Pi.add_apply]
    rw [Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hs)]

lemma gaussian_polynomial_log_integrable (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    Integrable (fun x : ℝ => Real.log ‖p.eval (x : ℂ)‖) (gaussianReal m v) := by
  have hf (x : ℝ) := (IsAlgClosed.splits p).eval_eq_prod_roots (x : ℂ)
  apply ((integrable_const (Real.log ‖p.leadingCoeff‖)).add
    (gaussian_product_log_integrable m v hv p.roots)).congr
  filter_upwards [gaussian_roots_nonzero m v hv p.roots] with x hx
  simp only [Pi.add_apply]
  rw [hf x, norm_mul, Real.log_mul
    (norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
    (norm_ne_zero_iff.mpr hx)]

private lemma gaussian_product_log_integral (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (s : Multiset ℂ) :
    (∫ x : ℝ, Real.log ‖(s.map (fun z => (x : ℂ)-z)).prod‖ ∂gaussianReal m v) =
      (s.map (fun z => ∫ x : ℝ, Real.log ‖(x : ℂ)-z‖ ∂gaussianReal m v)).sum := by
  letI := nullSingletonClass_gaussianReal (μ := m) hv
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih =>
    have he : (fun x : ℝ => Real.log ‖((z ::ₘ s).map (fun w => (x : ℂ)-w)).prod‖)
        =ᵐ[gaussianReal m v] (fun x => Real.log ‖(x : ℂ)-z‖ +
          Real.log ‖(s.map (fun w => (x : ℂ)-w)).prod‖) := by
      filter_upwards [Measure.ae_ne (gaussianReal m v) z.re,
        gaussian_roots_nonzero m v hv s] with x hx hs
      have hz : (x : ℂ)-z ≠ 0 := by
        intro he
        apply hx
        simpa using congrArg Complex.re (sub_eq_zero.mp he)
      simp only [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      rw [Real.log_mul (norm_ne_zero_iff.mpr hz) (norm_ne_zero_iff.mpr hs)]
    rw [integral_congr_ae he, integral_add (gaussian_root_log_integrable m v hv z)
      (gaussian_product_log_integrable m v hv s), ih]
    simp

private lemma gaussian_polynomial_log_integral (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    (∫ x : ℝ, Real.log ‖p.eval (x : ℂ)‖ ∂gaussianReal m v) =
      Real.log ‖p.leadingCoeff‖ +
        (p.roots.map (fun z => ∫ x : ℝ, Real.log ‖(x : ℂ)-z‖ ∂gaussianReal m v)).sum := by
  have he : (fun x : ℝ => Real.log ‖p.eval (x : ℂ)‖)
      =ᵐ[gaussianReal m v] (fun x => Real.log ‖p.leadingCoeff‖ +
        Real.log ‖(p.roots.map (fun z => (x : ℂ)-z)).prod‖) := by
    filter_upwards [gaussian_roots_nonzero m v hv p.roots] with x hx
    rw [(IsAlgClosed.splits p).eval_eq_prod_roots (x : ℂ), norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
        (norm_ne_zero_iff.mpr hx)]
  rw [integral_congr_ae he, integral_add (integrable_const _)
    (gaussian_product_log_integrable m v hv p.roots), integral_const,
    gaussian_product_log_integral m v hv p.roots]
  simp

noncomputable def rootLogCost (m : ℝ) (v : ℝ≥0) : ℝ :=
  (∫ x : ℝ, |x| ∂gaussianReal m v) +
    (Real.sqrt (2 * Real.pi * v))⁻¹ * (∫ x : ℝ, Real.posLog x⁻¹)

lemma rootLogCost_nonneg (m : ℝ) (v : ℝ≥0) : 0 ≤ rootLogCost m v := by
  unfold rootLogCost
  apply add_nonneg
  · exact integral_nonneg (fun x => abs_nonneg x)
  · apply mul_nonneg (by positivity)
    exact integral_nonneg (fun x => Real.posLog_nonneg)

private lemma gaussian_polynomial_log_mahler_lower (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    p.logMahlerMeasure - p.natDegree * rootLogCost m v ≤
      ∫ x : ℝ, Real.log ‖p.eval (x : ℂ)‖ ∂gaussianReal m v := by
  have hsum (s : Multiset ℂ) :
      (s.map (fun z => Real.log (max 1 ‖z‖))).sum -
        s.card * rootLogCost m v ≤
      (s.map (fun z => ∫ x : ℝ, Real.log ‖(x : ℂ)-z‖ ∂gaussianReal m v)).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons z s ih =>
      have hz := gaussian_root_log_lower m v hv z
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
        Nat.cast_add, Nat.cast_one]
      unfold rootLogCost at *
      simp only [Real.posLog, Real.log_inv, Real.log_abs, max_comm] at *
      linarith
  have hr := hsum p.roots
  rw [Polynomial.logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots,
    gaussian_polynomial_log_integral m v hv p hp,
    (IsAlgClosed.splits p).natDegree_eq_card_roots]
  have heq : p.roots.map (fun z => Real.log (max 1 ‖z‖)) =
      p.roots.map (fun z => Real.posLog ‖z‖) := by
    apply Multiset.map_congr rfl
    intro z hz
    exact (Real.posLog_eq_log_max_one (norm_nonneg z)).symm
  rw [heq] at hr
  linarith

lemma gaussian_polynomial_log_coeff_lower (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (p : Polynomial ℂ) (j : ℕ) (hj : p.coeff j ≠ 0) :
    Real.log ‖p.coeff j‖ - p.natDegree * (Real.log 2 + rootLogCost m v) ≤
      ∫ x : ℝ, Real.log ‖p.eval (x : ℂ)‖ ∂gaussianReal m v := by
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hj
  have hb := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure j p
  have hc : (p.natDegree.choose j : ℝ) ≤ (2 : ℝ)^p.natDegree := by
    exact_mod_cast Nat.choose_le_two_pow p.natDegree j
  have hm : 0 < p.mahlerMeasure := Polynomial.mahlerMeasure_pos_of_ne_zero hp
  have hb2 : ‖p.coeff j‖ ≤ (2 : ℝ)^p.natDegree * p.mahlerMeasure :=
    hb.trans (mul_le_mul_of_nonneg_right hc hm.le)
  have hl := Real.log_le_log (norm_pos_iff.mpr hj) hb2
  rw [Real.log_mul (by positivity) hm.ne', Real.log_pow,
    ← Polynomial.logMahlerMeasure_eq_log_MahlerMeasure] at hl
  have hlow := gaussian_polynomial_log_mahler_lower m v hv p hp
  nlinarith

lemma gaussian_complex_pow_integrable (m : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ)^k) (gaussianReal m v) := by
  have hi : Integrable (fun x : ℝ => ‖x‖^k) (gaussianReal m v) := by
    exact (memLp_id_gaussianReal (μ := m) (v := v) (k : ℝ≥0)).integrable_norm_pow' (p := k)
  apply hi.mono' (by fun_prop)
  filter_upwards [] with x
  simp only [norm_pow, Complex.norm_real]
  exact le_rfl

end
end D5.S3.Analytic.Probability.GaussianPolynomialLog

open MeasureTheory
namespace D5.S3.Analytic.Probability.GaussianPolynomialLog

lemma norm_eq_two_pos_sub (t : ℝ) : ‖t‖ = 2 * max t 0 - t := by
  simpa only [Real.norm_eq_abs, PosPart.posPart, nsmul_eq_mul, Nat.cast_ofNat] using
    (eq_sub_of_add_eq (abs_add_eq_two_nsmul_posPart t))

lemma integrable_prod_of_pos_and_fiber_lower
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ) (hf : AEStronglyMeasurable f (μ.prod ν))
    (hpos : Integrable (fun z => max (f z) 0) (μ.prod ν))
    (hsection : ∀ᵐ y ∂ν, Integrable (fun x => f (x,y)) μ)
    (g : β → ℝ) (hg : Integrable g ν)
    (hlower : ∀ᵐ y ∂ν, g y ≤ ∫ x, f (x,y) ∂μ) :
    Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff' hf).mpr
  refine ⟨hsection, ?_⟩
  have hmeas : AEStronglyMeasurable (fun y => ∫ x, ‖f (x,y)‖ ∂μ) ν :=
    hf.norm.prod_swap.integral_prod_right'
  apply ((hpos.integral_prod_right.const_mul 2).sub hg).mono' hmeas
  filter_upwards [hsection, hpos.prod_left_ae, hlower] with y hy hpy hly
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  have he : (∫ x, ‖f (x,y)‖ ∂μ) =
      2 * (∫ x, max (f (x,y)) 0 ∂μ) - ∫ x, f (x,y) ∂μ := by
    simpa only [Real.norm_eq_abs, PosPart.posPart] using
      integral_abs_eq_two_mul_integral_posPart_sub_integral hy
  rw [he]
  exact sub_le_sub_left hly _

end D5.S3.Analytic.Probability.GaussianPolynomialLog
open Matrix Polynomial
open scoped BigOperators Kronecker
namespace D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
noncomputable section
variable {R : Type*} [CommRing R] [StarRing R] [Nontrivial R]
private lemma X_pow_dvd_det_of_entry_weights {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (M : Matrix ι ι (Polynomial R)) (r c : ι → ℕ)
    (h : ∀ i j, (X : Polynomial R)^(r i+c j) ∣ M i j) :
    (X : Polynomial R)^((∑ i, r i)+(∑ j, c j)) ∣ Matrix.det M := by
  classical
  choose Q hQ using h
  let Qm : Matrix ι ι (Polynomial R) := Matrix.of Q
  refine ⟨Matrix.det Qm, ?_⟩
  have hm : M = Matrix.diagonal (fun i => (X : Polynomial R)^r i) * Qm *
      Matrix.diagonal (fun j => (X : Polynomial R)^c j) := by
    apply Matrix.ext
    intro i j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Qm, Matrix.of_apply]
    rw [hQ i j, pow_add]
    ring
  rw [hm, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum, pow_add]
  ring
private lemma natDegree_det_le_of_entries {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (M : Matrix ι ι (Polynomial R)) (D : ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ D) :
    (Matrix.det M).natDegree ≤ Fintype.card ι * D := by
  classical
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  have hp : (∏ i, M (σ i) i).natDegree ≤ Fintype.card ι * D := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc
      (∑ i, (M (σ i) i).natDegree) ≤ ∑ _i : ι, D := Finset.sum_le_sum (fun i hi => h _ _)
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa only [hs, one_smul] using hp
  · simpa only [hs, Units.neg_smul, one_smul, Polynomial.natDegree_neg] using hp
noncomputable def affineGramPoly {n : ℕ} (A G : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) (Polynomial R) :=
  (A * Aᴴ).map Polynomial.C + (Polynomial.X : Polynomial R) • (A * Gᴴ + G * Aᴴ).map Polynomial.C +
    (Polynomial.X : Polynomial R)^2 • (G * Gᴴ).map Polynomial.C
noncomputable def pairDet {n : ℕ} (A C G K : Matrix (Fin n) (Fin n) R) : Polynomial R :=
  Matrix.det (affineGramPoly A G ⊗ₖ (1 : Matrix (Fin n) (Fin n) (Polynomial R)) -
    (1 : Matrix (Fin n) (Fin n) (Polynomial R)) ⊗ₖ affineGramPoly C K)
private noncomputable def rankOneGramPoly {s : ℕ} (a : R)
    (G : Matrix (Fin (s+1)) (Fin (s+1)) R) :
    Matrix (Fin (s+1)) (Fin (s+1)) (Polynomial R) := fun i j =>
  Polynomial.C (if i=0 ∧ j=0 then a * star a else 0) +
    Polynomial.X * Polynomial.C ((if i=0 then a * star (G j 0) else 0) +
      (if j=0 then G i 0 * star a else 0)) +
    Polynomial.X^2 * Polynomial.C (∑ k, G i k * star (G j k))
private lemma affineGramPoly_rankOneBase {s : ℕ} (a : R)
    (G : Matrix (Fin (s+1)) (Fin (s+1)) R) :
    affineGramPoly (Matrix.single 0 0 a) G = rankOneGramPoly a G := by
  apply Matrix.ext
  intro i j
  simp only [affineGramPoly, ← Matrix.diagonal_single, Pi.single_apply, eq_comm, rankOneGramPoly,
    Matrix.add_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.conjTranspose_apply, Matrix.mul_apply]
  by_cases hi : i=0 <;> by_cases hj : j=0 <;>
    simp_all [Matrix.diagonal_apply, Pi.star_apply, Fin.sum_univ_succ]
private noncomputable def rowWeight {s : ℕ} (ij : Fin (s+1) × Fin (s+1)) : ℕ :=
  if (ij.1=0 ∧ ij.2=0) ∨ (ij.1≠0 ∧ ij.2≠0) then 1 else 0
private noncomputable def colWeight {s : ℕ} (ij : Fin (s+1) × Fin (s+1)) : ℕ :=
  if ij.1≠0 ∧ ij.2≠0 then 1 else 0
private lemma rankOne_entry_divisibility {s : ℕ} (a : R)
    (G K : Matrix (Fin (s+1)) (Fin (s+1)) R)
    (ij kl : Fin (s+1) × Fin (s+1)) :
    (Polynomial.X : Polynomial R)^(rowWeight ij + colWeight kl) ∣
      (rankOneGramPoly a G ⊗ₖ (1 : Matrix (Fin (s+1)) (Fin (s+1)) (Polynomial R)) -
        (1 : Matrix (Fin (s+1)) (Fin (s+1)) (Polynomial R)) ⊗ₖ rankOneGramPoly a K) ij kl := by
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  rcases ij with ⟨i,j⟩
  rcases kl with ⟨k,l⟩
  have hd2 : d < 2 := by
    have hr : rowWeight (i,j) ≤ 1 := by unfold rowWeight; split <;> omega
    have hc : colWeight (k,l) ≤ 1 := by unfold colWeight; split <;> omega
    omega
  by_cases hi : i=0 <;> by_cases hj : j=0 <;>
    by_cases hk : k=0 <;> by_cases hl : l=0 <;>
    simp_all only [rowWeight, colWeight, ne_eq, not_true_eq_false, not_false_eq_true,
      true_and, false_and, and_true, and_false, true_or, false_or, or_true, or_false,
      ite_true, ite_false, Prod.fst, Prod.snd] <;> try omega
  all_goals
    interval_cases d <;>
      simp_all [rankOneGramPoly, Matrix.kronecker_apply, Matrix.sub_apply,
        Matrix.one_apply, eq_comm, Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one] <;>
      split_ifs <;> simp [Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one]
private lemma rowWeight_sum (s : ℕ) : (∑ ij : Fin (s+1) × Fin (s+1), rowWeight ij) = 1+s*s := by
  simp only [Fintype.sum_prod_type, rowWeight, Fin.sum_univ_succ]
  simp
private lemma colWeight_sum (s : ℕ) : (∑ ij : Fin (s+1) × Fin (s+1), colWeight ij) = s*s := by
  simp only [Fintype.sum_prod_type, colWeight, Fin.sum_univ_succ]
  simp
lemma rankOne_order_lower {s : ℕ} (a : R)
    (G K : Matrix (Fin (s+1)) (Fin (s+1)) R) :
    (Polynomial.X : Polynomial R)^(2*s*s+1) ∣
      pairDet (Matrix.single 0 0 a) (Matrix.single 0 0 a) G K := by
  have h := X_pow_dvd_det_of_entry_weights
    (rankOneGramPoly a G ⊗ₖ (1 : Matrix (Fin (s+1)) (Fin (s+1)) (Polynomial R)) -
      (1 : Matrix (Fin (s+1)) (Fin (s+1)) (Polynomial R)) ⊗ₖ rankOneGramPoly a K)
    rowWeight colWeight (rankOne_entry_divisibility a G K)
  rw [rowWeight_sum, colWeight_sum] at h
  simpa only [pairDet, affineGramPoly_rankOneBase,
    show 1+s*s+s*s = 2*s*s+1 by ring] using h
end
end D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
namespace D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
noncomputable section
variable {R : Type*} [CommRing R] [StarRing R] [Nontrivial R]
private lemma rankOneGramPoly_one {s : ℕ} (a : R) :
    rankOneGramPoly a (1 : Matrix (Fin (s+1)) (Fin (s+1)) R) =
      Matrix.diagonal (fun i => if i=0 then
        Polynomial.C (a * star a) + Polynomial.X * Polynomial.C (a+star a) + Polynomial.X^2
        else Polynomial.X^2) := by
  rw [← affineGramPoly_rankOneBase]
  apply Matrix.ext
  intro i j
  simp only [affineGramPoly, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.one_mul,
    ← Matrix.diagonal_single, Pi.single_apply, eq_comm, Matrix.diagonal_conjTranspose, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply]
  by_cases hij : i=j <;> by_cases hi : i=0 <;> by_cases hj : j=0 <;>
    simp_all [Matrix.one_apply]
private lemma rankOneGramPoly_zero {s : ℕ} (a : R) :
    rankOneGramPoly a (0 : Matrix (Fin (s+1)) (Fin (s+1)) R) =
      Matrix.diagonal (fun i => if i=0 then Polynomial.C (a * star a) else 0) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i=j <;> by_cases hi : i=0 <;> by_cases hj : j=0 <;>
    simp_all [rankOneGramPoly, Matrix.diagonal_apply]
private lemma pairDet_rankOne_witness {s : ℕ} (a : R) :
    pairDet (Matrix.single 0 0 a) (Matrix.single 0 0 a)
      (1 : Matrix (Fin (s+1)) (Fin (s+1)) R) 0 =
      Polynomial.X^(2*s*s+1) *
        (Polynomial.C (a+star a)+Polynomial.X) *
        (Polynomial.C (a * star a) + Polynomial.X * Polynomial.C (a+star a) + Polynomial.X^2)^s *
        (Polynomial.X^2 - Polynomial.C (a*star a))^s := by
  unfold pairDet
  rw [affineGramPoly_rankOneBase, affineGramPoly_rankOneBase,
    rankOneGramPoly_one, rankOneGramPoly_zero]
  rw [← Matrix.diagonal_one, Matrix.diagonal_kronecker_diagonal,
    Matrix.diagonal_kronecker_diagonal, Matrix.diagonal_sub,
    Matrix.det_diagonal]
  simp only [Fintype.prod_prod_type, Fin.prod_univ_succ, Fin.zero_eta, ite_true,
    Fin.succ_ne_zero, ite_false, mul_one, one_mul]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, sub_zero]
  simp only [mul_pow, ← pow_mul]
  simp only [pow_add, pow_one, Nat.mul_assoc]
  ring

end
end D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
namespace D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
noncomputable section
variable {R : Type*} [CommRing R] [StarRing R] [Nontrivial R]
private lemma affineGramPoly_degree_le {n : ℕ} (A G : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (affineGramPoly A G i j).natDegree ≤ 2 := by
  simp only [affineGramPoly, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · simp
    · have h := Polynomial.natDegree_mul_le (p := (Polynomial.X : Polynomial R))
        (q := Polynomial.C ((A * Gᴴ + G * Aᴴ) i j))
      apply h.trans
      norm_num
  · have h := Polynomial.natDegree_mul_le (p := (Polynomial.X^2 : Polynomial R))
      (q := Polynomial.C ((G * Gᴴ) i j))
    simpa using h
lemma pairDet_degree_le {n : ℕ} (A C G K : Matrix (Fin n) (Fin n) R) :
    (pairDet A C G K).natDegree ≤ 2*n*n := by
  have h1 (i j : Fin n) : ((1 : Matrix (Fin n) (Fin n) (Polynomial R)) i j).natDegree = 0 := by
    by_cases hij : i=j <;> simp [Matrix.one_apply, hij]
  unfold pairDet
  have hd := natDegree_det_le_of_entries
    (affineGramPoly A G ⊗ₖ (1 : Matrix (Fin n) (Fin n) (Polynomial R)) -
      (1 : Matrix (Fin n) (Fin n) (Polynomial R)) ⊗ₖ affineGramPoly C K) 2
  have hEntries : ∀ ij kl, ((affineGramPoly A G ⊗ₖ
      (1 : Matrix (Fin n) (Fin n) (Polynomial R)) -
      (1 : Matrix (Fin n) (Fin n) (Polynomial R)) ⊗ₖ affineGramPoly C K) ij kl).natDegree ≤ 2 := by
    intro ij kl
    dsimp only [Matrix.sub_apply, Matrix.kronecker_apply]
    apply (Polynomial.natDegree_sub_le_of_le
      (Polynomial.natDegree_mul_le.trans (add_le_add (affineGramPoly_degree_le A G _ _)
        (le_of_eq (h1 _ _))))
      (Polynomial.natDegree_mul_le.trans (add_le_add (le_of_eq (h1 _ _))
        (affineGramPoly_degree_le C K _ _)))).trans
    norm_num
  exact (hd hEntries).trans_eq (by simp only [Fintype.card_prod, Fintype.card_fin]; ring)
end
end D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
namespace D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
noncomputable section
variable {R : Type*} [CommRing R] [StarRing R] [Nontrivial R]
private lemma coeff_det_card_mul_of_entry_degree_le {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] (M : Matrix ι ι (Polynomial R)) (D : ℕ)
    (h : ∀ i j, (M i j).natDegree ≤ D) :
    (Matrix.det M).coeff (Fintype.card ι * D) = Matrix.det (Matrix.of (fun i j => (M i j).coeff D)) := by
  classical
  rw [Matrix.det_apply, Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Polynomial.coeff_smul]
  congr 1
  exact Polynomial.coeff_prod_of_natDegree_le _ _ _ (fun i hi => h _ _)
end
end D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance

namespace D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
noncomputable section
variable {R : Type*} [CommRing R] [StarRing R] [Nontrivial R]
private lemma affineGramPoly_coeff_two {n : ℕ} (A G : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (affineGramPoly A G i j).coeff 2 = (G * Gᴴ) i j := by
  change (Polynomial.C ((A*Aᴴ) i j) + Polynomial.X * Polynomial.C ((A*Gᴴ+G*Aᴴ) i j) +
    Polynomial.X^2 * Polynomial.C ((G*Gᴴ) i j)).coeff 2 = _
  simp [Polynomial.coeff_mul_C]
private lemma pairDet_identity_noise_topCoeff {n : ℕ} (A C : Matrix (Fin n) (Fin n) R) :
    (pairDet A C 1 0).coeff (2*n*n) = 1 := by
  let M : Matrix (Fin n × Fin n) (Fin n × Fin n) (Polynomial R) :=
    affineGramPoly A 1 ⊗ₖ (1 : Matrix (Fin n) (Fin n) (Polynomial R)) -
      (1 : Matrix (Fin n) (Fin n) (Polynomial R)) ⊗ₖ affineGramPoly C 0
  have h1 (i j : Fin n) : ((1 : Matrix (Fin n) (Fin n) (Polynomial R)) i j).natDegree = 0 := by
    by_cases hij : i=j <;> simp [Matrix.one_apply, hij]
  have hEntries : ∀ ij kl, (M ij kl).natDegree ≤ 2 := by
    intro ij kl
    dsimp only [M, Matrix.sub_apply, Matrix.kronecker_apply]
    apply (Polynomial.natDegree_sub_le_of_le
      (Polynomial.natDegree_mul_le.trans (add_le_add (affineGramPoly_degree_le A 1 _ _)
        (le_of_eq (h1 _ _))))
      (Polynomial.natDegree_mul_le.trans (add_le_add (le_of_eq (h1 _ _))
        (affineGramPoly_degree_le C 0 _ _)))).trans
    norm_num
  have hcoeff := coeff_det_card_mul_of_entry_degree_le M 2 hEntries
  have hcard : Fintype.card (Fin n × Fin n) * 2 = 2*n*n := by
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  rw [hcard] at hcoeff
  change (Matrix.det M).coeff (2*n*n) = 1
  rw [hcoeff]
  have hI : Matrix.of (fun i j => (M i j).coeff 2) =
      (1 : Matrix (Fin n × Fin n) (Fin n × Fin n) R) := by
    apply Matrix.ext
    intro ij kl
    dsimp only [M, Matrix.of_apply, Matrix.sub_apply, Matrix.kronecker_apply]
    by_cases hi : ij.1=kl.1 <;> by_cases hj : ij.2=kl.2 <;>
      simp [Matrix.one_apply, hi, hj, affineGramPoly_coeff_two, Prod.ext_iff]
  rw [hI, Matrix.det_one]
lemma pairDet_identity_noise_ne_zero {n : ℕ} (A C : Matrix (Fin n) (Fin n) R) :
    pairDet A C 1 0 ≠ 0 := by
  intro h
  have hc := pairDet_identity_noise_topCoeff A C
  rw [h, Polynomial.coeff_zero] at hc
  exact zero_ne_one hc
end
end D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance

set_option maxHeartbeats 2500000
set_option linter.unusedSimpArgs false
namespace D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
noncomputable section

end
end D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
namespace D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
noncomputable section

lemma pairDet_rankOne_witness_order {s : ℕ} (a : ℝ) (ha : a ≠ 0) :
    (pairDet (Matrix.single 0 0 (a : ℂ)) (Matrix.single 0 0 (a : ℂ))
      (1 : Matrix (Fin (s+1)) (Fin (s+1)) ℂ) 0).natTrailingDegree = 2*s*s+1 := by
  rw [pairDet_rankOne_witness]
  let Q : Polynomial ℂ :=
    (Polynomial.C ((a : ℂ)+star (a : ℂ))+Polynomial.X) *
    (Polynomial.C ((a : ℂ) * star (a : ℂ)) +
      Polynomial.X * Polynomial.C ((a : ℂ)+star (a : ℂ)) + Polynomial.X^2)^s *
    (Polynomial.X^2 - Polynomial.C ((a : ℂ)*star (a : ℂ)))^s
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha
  have hq0 : Q.coeff 0 ≠ 0 := by
    change Polynomial.constantCoeff Q ≠ 0
    dsimp only [Q]
    simp only [map_mul, map_pow, map_add, map_sub, Polynomial.constantCoeff_apply,
      Polynomial.coeff_C_zero, Polynomial.coeff_X_zero,
      zero_pow (by norm_num : (2:ℕ) ≠ 0), mul_zero, zero_mul, add_zero, zero_add, zero_sub,
      Complex.star_def, Complex.conj_ofReal]
    apply mul_ne_zero
    · apply mul_ne_zero
      · simpa only [← two_mul] using (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0) haC)
      · exact pow_ne_zero _ (mul_ne_zero haC haC)
    · exact pow_ne_zero _ (neg_ne_zero.mpr (mul_ne_zero haC haC))
  have hq : Q ≠ 0 := by
    intro h
    apply hq0
    rw [h, Polynomial.coeff_zero]
  have heq : Polynomial.X^(2*s*s+1) *
        (Polynomial.C ((a : ℂ)+star (a : ℂ))+Polynomial.X) *
        (Polynomial.C ((a : ℂ) * star (a : ℂ)) +
          Polynomial.X * Polynomial.C ((a : ℂ)+star (a : ℂ)) + Polynomial.X^2)^s *
        (Polynomial.X^2 - Polynomial.C ((a : ℂ)*star (a : ℂ)))^s =
      Q * Polynomial.X^(2*s*s+1) := by dsimp [Q]; ring
  rw [heq, Polynomial.natTrailingDegree_mul_X_pow hq,
    Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hq0), zero_add]

end
end D5.S3.Analytic.Probability.GaussianPolynomialLog.Covariance
set_option maxRecDepth 2048
