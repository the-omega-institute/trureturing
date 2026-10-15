/- GID: D5/S3/Analytic/Probability/BernoulliTriangularLimits
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/BernoulliTriangularLimits
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Variance divergence gives uniform central and local limits for Bernoulli polynomials. -/

/- admission_basis: escape-witness
   Direct frozen dependencies (declaration GID and declaration statement_id):
   F0: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance sha256:acf3515171050627eccee903208eb3f1d603d5d3ff4cc74a94c0c95259871d6f
   F1: D5/S3/Zeros/Endpoints/BernoulliBridgeVariance.bernoulli_bridge_variance_le_quarter sha256:d26843918e966727ef778f8c78682791d54fdc06c6a8b7c77e5a9601dd05c43e
   F2: D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalCDF sha256:bedd42e0116dd2f043fdce1b697eb76e39eb075a733900543f5071ddb4405a7c
   F3: D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalPDF sha256:09ec747bd067dc23f72a70f43c419879f8a0a5eaceb77360e81137c6bcbaec5f
   F4: D5/S3/TotalVariation/Asymptotics/StatLeanFourierSuppliers.stdNormalPDF_eq_gaussianPDFReal sha256:58d494ec9f13bfb185d13aed064fce12d7eae49cef3f5b9932af21926e310c11
   Module escape_witness: uniform_lattice_limit_to_floor; monotone_cdf_pointwise_to_uniform (same-delivery content)
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/15743
   Template gap: No triangular-array realization or uniform CDF/lattice/floor readout is supplied.
   Four-slot evidence missing: source-specific arenas and observation/readout maps,
     exact reconstruction and realization bridges, E1–E8, variation and sensitivity.
   CLT and LLT use StatLean.HypothesisTesting.stdNormalCDF and stdNormalPDF;
   claim states the source integral and density literally, with the correspondence
   established inside result.
   rowMean: proof_shape: bind-only; escape_witness: none;
     consumers: centered_rowPhi, scaled_lattice_fourier_inversion, cutoff_lattice_fourier_inversion, uniform_lattice_error_bound, bernoulli_array_uniform_lattice_limit, standardizedRow, standardizedRow_charFun, factorization_moments, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits, result.
   rowVariance: proof_shape: bind-only; escape_witness: none;
     consumers: uniform_lattice_error_bound, bernoulli_array_uniform_lattice_limit, bernoulli_array_uniform_gaussian_cdf, factorization_moments, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits, result.
   rowMass: proof_shape: bind-only; escape_witness: none;
     consumers: finite_lattice_fourier_inversion, scaled_lattice_fourier_inversion, cutoff_lattice_fourier_inversion, uniform_lattice_error_bound, bernoulli_array_uniform_lattice_limit, factorization_integer_mass, bernoulli_polynomial_uniform_limits.
   rowPhi: proof_shape: bind-only; escape_witness: none;
     consumers: rowPhi_expansion, finite_lattice_fourier_inversion, centered_rowPhi, scaled_lattice_fourier_inversion.
   rowPhi_expansion: proof_shape: bind-only; escape_witness: none;
     consumers: finite_lattice_fourier_inversion.
   integer_harmonic_integral: proof_shape: bind-only; escape_witness: none;
     consumers: finite_lattice_fourier_inversion.
   finite_lattice_fourier_inversion: proof_shape: bind-only; escape_witness: none;
     consumers: scaled_lattice_fourier_inversion.
   rowFourierCutoff: proof_shape: bind-only; escape_witness: none;
     consumers: measurable_rowFourierCutoff, cutoff_bernoulli_gaussian_envelope, rowFourierCutoff_tendsto, bernoulli_array_fourier_L1_gaussian_limit, cutoff_lattice_fourier_inversion, integrable_rowFourierCutoff, uniform_lattice_error_bound, bernoulli_array_uniform_lattice_limit.
   measurable_rowFourierCutoff: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_array_fourier_L1_gaussian_limit, integrable_rowFourierCutoff.
   cutoff_bernoulli_gaussian_envelope: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_array_fourier_L1_gaussian_limit, integrable_rowFourierCutoff.
   rowFourierCutoff_tendsto: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: bernoulli_array_fourier_L1_gaussian_limit.
   bernoulli_array_fourier_L1_gaussian_limit: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: bernoulli_array_uniform_lattice_limit.
   normalPDF_fourier_integral: proof_shape: bind-only; escape_witness: none;
     consumers: uniform_lattice_error_bound.
   normalPDF_uniformContinuous: proof_shape: bind-only; escape_witness: none;
     consumers: uniform_lattice_limit_to_floor.
   centered_rowPhi: proof_shape: bind-only; escape_witness: none;
     consumers: scaled_lattice_fourier_inversion.
   scaled_lattice_fourier_inversion: proof_shape: bind-only; escape_witness: none;
     consumers: cutoff_lattice_fourier_inversion.
   cutoff_lattice_fourier_inversion: proof_shape: bind-only; escape_witness: none;
     consumers: uniform_lattice_error_bound.
   phase_norm: proof_shape: bind-only; escape_witness: none;
     consumers: integrable_phase_mul, uniform_lattice_error_bound.
   integrable_phase_mul: proof_shape: bind-only; escape_witness: none;
     consumers: uniform_lattice_error_bound.
   integrable_rowFourierCutoff: proof_shape: bind-only; escape_witness: none;
     consumers: uniform_lattice_error_bound.
   integrable_gaussian_kernel: proof_shape: bind-only; escape_witness: none;
     consumers: uniform_lattice_error_bound.
   uniform_lattice_error_bound: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_array_uniform_lattice_limit.
   bernoulli_array_uniform_lattice_limit: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F0, F1.
     consumers: bernoulli_polynomial_uniform_limits.
   standardized_floor_error: proof_shape: bind-only; escape_witness: none;
     consumers: uniform_lattice_limit_to_floor.
   uniform_lattice_limit_to_floor: proof_shape: content; escape_witness: uniform_lattice_limit_to_floor;
     consumers: bernoulli_polynomial_uniform_limits.
   mu: proof_shape: bind-only; escape_witness: none;
     consumers: sigmaSq, CLT, LLT, sigmaSq_mul, sigmaSq_C, sigmaSq_X, mu_mul, mu_bernoulliPGF, sigmaSq_bernoulliPGF, bernoulli_product_mu, bernoulli_product_sigmaSq, mu_normalized, factorization_moments, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits, sigmaSq_X_sub_C, sigmaSq_root_prod, result.
   sigmaSq: proof_shape: bind-only; escape_witness: none;
     consumers: sigma, sigmaSq_mul, sigmaSq_C, sigmaSq_X, sigmaSq_bernoulliPGF, bernoulli_product_sigmaSq, sigmaSq_normalized, factorization_moments, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits, sigmaSq_X_sub_C, sigmaSq_root_prod, sigmaSq_splits, sigmaSq_ge_logderivative, speyer_variance_bound, speyer_variance_bound_eighth, speyer_variance_eighth_unconditional, speyer_variance_tendsto, result.
   sigma: proof_shape: bind-only; escape_witness: none;
     consumers: CLT, LLT, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits.
   prob: proof_shape: bind-only; escape_witness: none;
     consumers: CLT, LLT, factorization_integer_mass, factorization_finite_cdf, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits.
   normalCDF_eq_gaussian: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F2.
     consumers: bernoulli_polynomial_uniform_limits.
   normalPDF_eq_gaussian: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F4.
     consumers: bernoulli_polynomial_uniform_limits.
   CLT: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F2.
     consumers: bernoulli_polynomial_uniform_limits, result.
   LLT: proof_shape: bind-only; escape_witness: none;
     frozen_dependencies: F3.
     consumers: bernoulli_polynomial_uniform_limits, result.
   bernoulliPGF: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_pgf_expansion, bernoulli_coefficient_law, bernoulliPGF_eval_one, mu_bernoulliPGF, sigmaSq_bernoulliPGF, bernoulli_product_eval_one, bernoulli_product_mu, bernoulli_product_sigmaSq, factorization_moments, factorization_integer_mass, factorization_finite_cdf, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits, normalized_linear, normalized_root_prod, normalized_splits, g_normalized_bernoulli_multiset, g_bernoulli_factorization, result.
   normalized: proof_shape: bind-only; escape_witness: none;
     consumers: mu_normalized, sigmaSq_normalized, factorization_moments, factorization_integer_mass, factorization_finite_cdf, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits, normalized_mul, normalized_C, normalized_X, normalized_linear, normalized_root_prod, normalized_splits, g_normalized_bernoulli_multiset, g_bernoulli_factorization, result.
   sigmaSq_mul: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_product_sigmaSq, sigmaSq_normalized, factorization_moments, sigmaSq_root_prod, sigmaSq_splits, speyer_variance_bound.
   sigmaSq_C: proof_shape: bind-only; escape_witness: none;
     consumers: sigmaSq_normalized, sigmaSq_splits.
   sigmaSq_X: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_moments, speyer_variance_bound.
   bernoulli_event_mass: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_coefficient_law, factorization_integer_mass, factorization_finite_cdf.
   bernoulli_pgf_expansion: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_coefficient_law.
   bernoulli_coefficient_law: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_integer_mass, factorization_finite_cdf.
   standardizedRow: proof_shape: bind-only; escape_witness: none;
     consumers: standardizedRow_charFun, bernoulli_array_uniform_gaussian_cdf, factorization_standardized_cdf, bernoulli_polynomial_uniform_limits.
   standardizedRow_charFun: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_array_uniform_gaussian_cdf.
   bernoulli_array_uniform_gaussian_cdf: proof_shape: content; escape_witness: monotone_cdf_pointwise_to_uniform;
     frozen_dependencies: F0, F1.
     consumers: bernoulli_polynomial_uniform_limits.
   bernoulliPGF_eval_one: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_product_eval_one, bernoulli_product_mu, bernoulli_product_sigmaSq.
   mu_mul: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_product_mu, mu_normalized, factorization_moments.
   mu_bernoulliPGF: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_product_mu.
   sigmaSq_bernoulliPGF: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_product_sigmaSq.
   bernoulli_product_eval_one: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_product_mu, bernoulli_product_sigmaSq, factorization_moments.
   bernoulli_product_mu: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_moments.
   bernoulli_product_sigmaSq: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_moments.
   mu_normalized: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_moments.
   sigmaSq_normalized: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_moments.
   factorization_moments: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_standardized_cdf, bernoulli_polynomial_uniform_limits, result.
   factorization_integer_mass: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_polynomial_uniform_limits.
   bit_sum_le: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_finite_cdf.
   bernoulli_real_event: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_event_mass, factorization_finite_cdf.
   factorization_finite_cdf: proof_shape: bind-only; escape_witness: none;
     consumers: factorization_standardized_cdf.
   factorization_standardized_cdf: proof_shape: bind-only; escape_witness: none;
     consumers: bernoulli_polynomial_uniform_limits.
   bernoulli_polynomial_uniform_limits: proof_shape: content; escape_witness: monotone_cdf_pointwise_to_uniform;
     frozen_dependencies: F0, F1, F2, F3, F4.
     consumers: result.
-/


import D5.S3.Analytic.Probability.UniformCDFConvergence
import D5.S3.TotalVariation.Asymptotics.StatLeanFourierSuppliers

noncomputable section
open Polynomial Finset Filter Real Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval Interval
namespace D5.S3.Analytic.Probability.BernoulliTriangularLimits

open D5.S3.Analytic.Probability.UniformCDFConvergence
def rowMean {m : ℕ} (p : Fin m → unitInterval) : ℝ := ∑ i, (p i:ℝ)

def rowVariance {m : ℕ} (p : Fin m → unitInterval) : ℝ := ∑ i, ((p i:ℝ) * (1 - (p i:ℝ)))
open Polynomial Finset Filter Real MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

def rowMass {m : ℕ} (p : Fin m → unitInterval) (k : ℤ) : ℝ :=
  ∑ x : Fin m → Bool, if ((∑ i, Bool.toNat (x i) : ℕ) : ℤ) = k then bernoulliWeight p x else 0

private def rowPhi {m : ℕ} (p : Fin m → unitInterval) (s : ℝ) : ℂ :=
  ∏ i, (((1-(p i:ℝ)):ℂ) + (p i:ℝ)*Complex.exp ((s:ℂ)*Complex.I))

private lemma rowPhi_expansion {m : ℕ} (p : Fin m → unitInterval) (s : ℝ) :
    rowPhi p s = ∑ x : Fin m → Bool, (bernoulliWeight p x : ℂ) *
      Complex.exp (((∑ i, Bool.toNat (x i) : ℕ) : ℂ)*(s:ℂ)*Complex.I) := by
  have he (i : Fin m) : (((1-(p i:ℝ)):ℂ)+(p i:ℝ)*Complex.exp ((s:ℂ)*Complex.I)) =
      ∑ b : Bool, ((if b then (p i:ℝ) else 1-(p i:ℝ)):ℂ) *
        Complex.exp (((Bool.toNat b):ℂ)*(s:ℂ)*Complex.I) := by
    simp [Fintype.sum_bool,Bool.toNat,add_comm]
  unfold rowPhi
  simp_rw [he]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x hx
  rw [prod_mul_distrib,←Complex.exp_sum]
  simp only [bernoulliWeight,Complex.ofReal_prod,Complex.ofReal_sub,
    Complex.ofReal_one,Nat.cast_sum,sum_mul]
  congr 1
  apply prod_congr rfl
  intro i hi
  cases x i <;> simp

private lemma integer_harmonic_integral (j : ℤ) :
    (∫ s in -Real.pi..Real.pi, Complex.exp ((j:ℂ)*(s:ℂ)*Complex.I)) =
      if j=0 then ((2*Real.pi:ℝ):ℂ) else (0:ℂ) := by
  by_cases hj : j=0
  · simp [hj,intervalIntegral.integral_const]
    push_cast
    ring
  · rw [if_neg hj]
    have hc : (j:ℂ)*Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
    have he (s : ℝ) : (j:ℂ)*(s:ℂ)*Complex.I = ((j:ℂ)*Complex.I)*(s:ℂ) := by ring
    simp_rw [he]
    rw [integral_exp_mul_complex hc]
    have hends : Complex.exp (((j:ℂ)*Complex.I)*(Real.pi:ℂ)) =
        Complex.exp (((j:ℂ)*Complex.I)*(-Real.pi:ℝ)) := by
      have he1 : ((j:ℂ)*Complex.I)*(Real.pi:ℂ) = (((j:ℝ)*Real.pi:ℝ):ℂ)*Complex.I := by push_cast; ring
      have he2 : ((j:ℂ)*Complex.I)*(-Real.pi:ℝ) = (-(((j:ℝ)*Real.pi:ℝ):ℂ))*Complex.I := by push_cast; ring
      rw [he1,he2,Complex.exp_mul_I,Complex.exp_mul_I]
      simp only [Complex.cos_neg,Complex.sin_neg]
      have hsin : Complex.sin (((j:ℝ)*Real.pi:ℝ):ℂ) = 0 := by
        rw [←Complex.ofReal_sin,Real.sin_int_mul_pi,Complex.ofReal_zero]
      have hsin2 : Complex.sin ((j:ℂ)*(Real.pi:ℂ)) = 0 := by
        simpa only [Complex.ofReal_mul,Complex.ofReal_intCast] using hsin
      simp [hsin2]
    rw [hends,sub_self,zero_div]

private lemma finite_lattice_fourier_inversion {m : ℕ} (p : Fin m → unitInterval) (k : ℤ) :
    (rowMass p k : ℂ) = (2*Real.pi:ℝ)⁻¹ *
      ∫ s in -Real.pi..Real.pi, rowPhi p s * Complex.exp (-(k:ℂ)*(s:ℂ)*Complex.I) := by
  have hint (x : Fin m → Bool) : IntervalIntegrable
      (fun s : ℝ => (bernoulliWeight p x:ℂ)*
        Complex.exp (((((∑ i, Bool.toNat (x i):ℕ):ℤ)-k):ℂ)*(s:ℂ)*Complex.I)) volume (-Real.pi) Real.pi :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hex (s : ℝ) : rowPhi p s * Complex.exp (-(k:ℂ)*(s:ℂ)*Complex.I) =
      ∑ x : Fin m → Bool, (bernoulliWeight p x:ℂ)*
        Complex.exp (((((∑ i, Bool.toNat (x i):ℕ):ℤ)-k):ℂ)*(s:ℂ)*Complex.I) := by
    rw [rowPhi_expansion,sum_mul]
    apply sum_congr rfl
    intro x hx
    rw [mul_assoc,←Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hex]
  rw [intervalIntegral.integral_finsetSum (by intro x hx; exact hint x)]
  unfold rowMass
  rw [Complex.ofReal_sum,mul_sum]
  apply sum_congr rfl
  intro x hx
  rw [intervalIntegral.integral_const_mul]
  rw [←Int.cast_sub,integer_harmonic_integral]
  by_cases hk : ((∑ i, Bool.toNat (x i):ℕ):ℤ)=k
  · simp only [hk,ite_true,sub_self,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
    <;> ring
  · have hk2 : (∑ i, (Bool.toNat (x i):ℤ)) ≠ k := by simpa only [Nat.cast_sum] using hk
    simp [hk,hk2,sub_ne_zero.mpr hk2]
open Filter Real MeasureTheory Topology Finset
open scoped BigOperators

private def rowFourierCutoff {m : ℕ} (p : Fin m → ℝ) (V u : ℝ) : ℂ :=
  ({u : ℝ | |u| ≤ Real.pi*Real.sqrt V}).indicator
    (fun u => ∏ i, centeredBernoulli (p i) (u/Real.sqrt V)) u

private lemma measurable_rowFourierCutoff {m : ℕ} (p : Fin m → ℝ) (V : ℝ) :
    Measurable (rowFourierCutoff p V) := by
  unfold rowFourierCutoff
  apply Measurable.indicator
  · apply Continuous.measurable
    unfold centeredBernoulli
    fun_prop
  · exact measurableSet_le continuous_abs.measurable measurable_const

private lemma cutoff_bernoulli_gaussian_envelope {m : ℕ} (p : Fin m → ℝ) (V u : ℝ)
    (hV : 0 < V) (hVeq : V = ∑ i, (p i * (1 - p i))) :
    ‖rowFourierCutoff p V u‖ ≤ Real.exp (-2*u^2/Real.pi^2) := by
  simp only [rowFourierCutoff, Set.indicator_apply, Set.mem_ofPred_eq]
  split_ifs with hu
  · exact normalized_bernoulli_product_envelope p V u hV hVeq hu
  · simp only [norm_zero]
    exact (Real.exp_pos _).le

private lemma rowFourierCutoff_tendsto {m : ℕ → ℕ} (p : ∀ n, Fin (m n) → ℝ) (V : ℕ → ℝ)
    (hvalid : ∀ᶠ n in atTop, (∀ i, 0 ≤ p n i ∧ p n i ≤ 1) ∧
      V n = ∑ i, (p n i * (1 - p n i)) ∧ 0 < V n)
    (hV : Tendsto V atTop atTop)
    (hVeq : ∀ n, V n = ∑ i, (p n i * (1 - p n i))) (u : ℝ) :
    Tendsto (fun n => rowFourierCutoff (p n) (V n) u) atTop
      (𝓝 (Real.exp (-u^2/2):ℂ)) := by
  have hcf := centered_bernoulli_charFun_tendsto p V u hvalid hV hVeq
  have hsqrt := Real.tendsto_sqrt_atTop.comp hV
  apply hcf.congr'
  filter_upwards [hsqrt.eventually_ge_atTop (|u|/Real.pi)] with n hn
  have hu : |u| ≤ Real.pi*Real.sqrt (V n) := by
    have hh := (div_le_iff₀ Real.pi_pos).1 hn
    simpa [mul_comm] using hh
  simp [rowFourierCutoff, Set.indicator_apply, hu]

private lemma bernoulli_array_fourier_L1_gaussian_limit {m : ℕ → ℕ}
    (p : ∀ n, Fin (m n) → ℝ) (V : ℕ → ℝ)
    (hvalid : ∀ᶠ n in atTop, (∀ i, 0 ≤ p n i ∧ p n i ≤ 1) ∧
      V n = ∑ i, (p n i * (1 - p n i)) ∧ 0 < V n)
    (hV : Tendsto V atTop atTop)
    (hVeq : ∀ n, V n = ∑ i, (p n i * (1 - p n i))) :
    Tendsto (fun n => ∫ u : ℝ,
      ‖rowFourierCutoff (p n) (V n) u - (Real.exp (-u^2/2):ℂ)‖) atTop (𝓝 0) := by
  have hboundInt : Integrable (fun u : ℝ =>
      Real.exp (-2*u^2/Real.pi^2)+Real.exp (-u^2/2)) := by
    have h1 : Integrable (fun u : ℝ => Real.exp (-2*u^2/Real.pi^2)) := by
      convert integrable_exp_neg_mul_sq (by positivity : 0<(2:ℝ)/Real.pi^2) using 1
      ext u
      congr 1
      ring
    have h2 : Integrable (fun u : ℝ => Real.exp (-u^2/2)) := by
      convert integrable_exp_neg_mul_sq (by norm_num : 0<(1:ℝ)/2) using 1
      ext u
      congr 1
      ring
    exact h1.add h2
  have hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable
      (fun u : ℝ => ‖rowFourierCutoff (p n) (V n) u - (Real.exp (-u^2/2):ℂ)‖) volume := by
    apply Eventually.of_forall
    intro n
    have hm := measurable_rowFourierCutoff (p n) (V n)
    exact (hm.sub (by fun_prop)).norm.aestronglyMeasurable
  have hbound : ∀ᶠ n in atTop, ∀ᵐ u : ℝ,
      ‖‖rowFourierCutoff (p n) (V n) u - (Real.exp (-u^2/2):ℂ)‖‖ ≤
        Real.exp (-2*u^2/Real.pi^2)+Real.exp (-u^2/2) := by
    filter_upwards [hvalid] with n hn
    apply ae_of_all
    intro u
    rw [norm_norm]
    calc
      _ ≤ ‖rowFourierCutoff (p n) (V n) u‖ + ‖(Real.exp (-u^2/2):ℂ)‖ := norm_sub_le _ _
      _ ≤ _ := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
        exact add_le_add (cutoff_bernoulli_gaussian_envelope (p n) (V n) u hn.2.2 hn.2.1) le_rfl
  have hlim : ∀ᵐ u : ℝ, Tendsto
      (fun n => ‖rowFourierCutoff (p n) (V n) u - (Real.exp (-u^2/2):ℂ)‖) atTop (𝓝 (0:ℝ)) := by
    apply ae_of_all
    intro u
    exact tendsto_iff_norm_sub_tendsto_zero.1 (rowFourierCutoff_tendsto p V hvalid hV hVeq u)
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun u : ℝ => Real.exp (-2*u^2/Real.pi^2)+Real.exp (-u^2/2))
    hmeas hbound hboundInt hlim
  simpa using h
open MeasureTheory Real Filter Topology

private lemma normalPDF_fourier_integral (t : ℝ) :
    ((ProbabilityTheory.gaussianPDFReal 0 1) t : ℂ) = (2*Real.pi:ℝ)⁻¹ * ∫ u : ℝ,
      Complex.exp (-(t:ℂ)*(u:ℂ)*Complex.I) * (Real.exp (-u^2/2):ℂ) := by
  have h := fourierIntegral_gaussian (b := (1:ℂ)/2) (by norm_num) (-(t:ℂ))
  have hfun (u : ℝ) : Complex.exp (Complex.I * (-(t:ℂ)) * (u:ℂ)) *
      Complex.exp (-((1:ℂ)/2)*(u:ℂ)^2) =
      Complex.exp (-(t:ℂ)*(u:ℂ)*Complex.I) * (Real.exp (-u^2/2):ℂ) := by
    rw [Complex.ofReal_exp]
    congr 2 <;> push_cast <;> ring
  simp_rw [hfun] at h
  have hr : ((Real.pi:ℂ)/((1:ℂ)/2))^((1:ℂ)/2) = (Real.sqrt (2*Real.pi):ℂ) := by
    have hb : (Real.pi:ℂ)/((1:ℂ)/2) = ((2*Real.pi:ℝ):ℂ) := by push_cast; ring
    rw [hb]
    have hp := Complex.ofReal_cpow (by positivity : 0≤(2*Real.pi:ℝ)) ((1:ℝ)/2)
    rw [←Real.sqrt_eq_rpow] at hp
    simpa using hp.symm
  rw [hr] at h
  have he : -(-(t:ℂ))^2/(4*((1:ℂ)/2)) = ((-t^2/2:ℝ):ℂ) := by push_cast; ring
  rw [he,←Complex.ofReal_exp] at h
  rw [h]
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one]
  push_cast
  have hsq := Real.sq_sqrt (by positivity : 0≤(2*Real.pi:ℝ))
  have hs : Real.sqrt (2*Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hc : (Real.sqrt (2*Real.pi):ℂ)^2 = (2:ℂ)*(Real.pi:ℂ) := by exact_mod_cast hsq
  rw [←hc]
  field_simp

private lemma normalPDF_uniformContinuous : UniformContinuous (ProbabilityTheory.gaussianPDFReal 0 1) := by
  have hcont : Continuous (ProbabilityTheory.gaussianPDFReal 0 1) := by unfold gaussianPDFReal; fun_prop
  apply hcont.uniformContinuous_of_tendsto_cocompact
  have htop : Tendsto (ProbabilityTheory.gaussianPDFReal 0 1) atTop (𝓝 0) := by
    have hsq : Tendsto (fun t : ℝ => t^2) atTop atTop := tendsto_pow_atTop (by norm_num)
    have hn : Tendsto (fun t : ℝ => -(t^2)/2) atTop atBot :=
      (tendsto_neg_atTop_atBot.comp hsq).atBot_div_const (by norm_num)
    have he := Real.tendsto_exp_atBot.comp hn
    rw [gaussianPDFReal_def]
    simp only [NNReal.coe_one, sub_zero, mul_one]
    simpa only [mul_zero,Function.comp_def] using he.const_mul (Real.sqrt (2*Real.pi))⁻¹
  have hbot : Tendsto (ProbabilityTheory.gaussianPDFReal 0 1) atBot (𝓝 0) := by
    have hh := htop.comp tendsto_neg_atBot_atTop
    convert hh using 1
    ext t
    simp [gaussianPDFReal,Function.comp_def]
  rw [cocompact_eq_atBot_atTop]
  exact tendsto_sup.2 ⟨hbot,htop⟩
open Polynomial Finset Real MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators unitInterval

private lemma centered_rowPhi {m : ℕ} (p : Fin m → unitInterval) (s : ℝ) :
    (∏ i, centeredBernoulli (p i:ℝ) s) =
      Complex.exp ((-s*rowMean p:ℝ)*Complex.I) * rowPhi p s := by
  simp_rw [centeredBernoulli_eq_phase]
  rw [prod_mul_distrib,←Complex.exp_sum]
  unfold rowPhi
  simp only [Complex.ofReal_sub,Complex.ofReal_one]
  congr 1
  congr 1
  simp only [rowMean,Complex.ofReal_mul,Complex.ofReal_neg,Complex.ofReal_sum,Finset.mul_sum,Finset.sum_mul]

private lemma scaled_lattice_fourier_inversion {m : ℕ} (p : Fin m → unitInterval) (V : ℝ)
    (hV : 0 < V) (k : ℤ) :
    ((Real.sqrt V * rowMass p k:ℝ):ℂ) = (2*Real.pi:ℝ)⁻¹ *
      ∫ u in (-Real.pi*Real.sqrt V)..(Real.pi*Real.sqrt V),
        (∏ i, centeredBernoulli (p i:ℝ) (u/Real.sqrt V)) *
          Complex.exp (-(((k:ℝ)-rowMean p)/Real.sqrt V:ℝ)*(u:ℂ)*Complex.I) := by
  have hs : Real.sqrt V ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hV)
  let H : ℝ → ℂ := fun u => (∏ i, centeredBernoulli (p i:ℝ) (u/Real.sqrt V)) *
    Complex.exp (-(((k:ℝ)-rowMean p)/Real.sqrt V:ℝ)*(u:ℂ)*Complex.I)
  have hcomp (s : ℝ) : H (s*Real.sqrt V) = rowPhi p s *
      Complex.exp (-(k:ℂ)*(s:ℂ)*Complex.I) := by
    dsimp [H]
    rw [mul_div_cancel_right₀ _ hs,centered_rowPhi]
    rw [show Complex.exp ((-s*rowMean p:ℝ)*Complex.I) * rowPhi p s *
        Complex.exp (-(((k:ℝ)-rowMean p)/Real.sqrt V:ℝ)*(s*Real.sqrt V:ℝ)*Complex.I) =
      rowPhi p s * (Complex.exp ((-s*rowMean p:ℝ)*Complex.I) *
        Complex.exp (-(((k:ℝ)-rowMean p)/Real.sqrt V:ℝ)*(s*Real.sqrt V:ℝ)*Complex.I)) by ring]
    rw [←Complex.exp_add]
    congr 2
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hs]
    <;> ring
  have hscale := intervalIntegral.smul_integral_comp_mul_right (f := H)
    (a := -Real.pi) (b := Real.pi) (Real.sqrt V)
  simp_rw [hcomp] at hscale
  rw [Complex.real_smul] at hscale
  have hinv := finite_lattice_fourier_inversion p k
  have h := congrArg (fun z : ℂ => (Real.sqrt V:ℂ)*z) hinv
  push_cast at h
  rw [←mul_assoc,mul_comm (Real.sqrt V:ℂ) ((2:ℂ)*(Real.pi:ℂ))⁻¹,mul_assoc,hscale] at h
  simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_ofNat] using h

private lemma cutoff_lattice_fourier_inversion {m : ℕ} (p : Fin m → unitInterval) (V : ℝ)
    (hV : 0 < V) (k : ℤ) :
    ((Real.sqrt V * rowMass p k:ℝ):ℂ) = (2*Real.pi:ℝ)⁻¹ * ∫ u : ℝ,
      rowFourierCutoff (fun i => (p i:ℝ)) V u *
        Complex.exp (-(((k:ℝ)-rowMean p)/Real.sqrt V:ℝ)*(u:ℂ)*Complex.I) := by
  have hR : 0 ≤ Real.pi*Real.sqrt V := by positivity
  have he : (fun u : ℝ => rowFourierCutoff (fun i => (p i:ℝ)) V u *
      Complex.exp (-(((k:ℝ)-rowMean p)/Real.sqrt V:ℝ)*(u:ℂ)*Complex.I)) =
    (Icc (-Real.pi*Real.sqrt V) (Real.pi*Real.sqrt V)).indicator
      (fun u => (∏ i, centeredBernoulli (p i:ℝ) (u/Real.sqrt V)) *
        Complex.exp (-(((k:ℝ)-rowMean p)/Real.sqrt V:ℝ)*(u:ℂ)*Complex.I)) := by
    funext u
    simp only [rowFourierCutoff,indicator_apply,Set.mem_Icc,Set.mem_ofPred_eq]
    have hh : |u| ≤ Real.pi*Real.sqrt V ↔ -Real.pi*Real.sqrt V ≤ u ∧ u ≤ Real.pi*Real.sqrt V := by
      rw [abs_le]; congr 1 <;> ring
    simp only [hh]
    split_ifs <;> simp
  rw [he,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le (by linarith : -Real.pi*Real.sqrt V ≤ Real.pi*Real.sqrt V)]
  exact scaled_lattice_fourier_inversion p V hV k

private lemma phase_norm (t u : ℝ) :
    ‖Complex.exp (-(t:ℂ)*(u:ℂ)*Complex.I)‖ = 1 := by
  rw [show -(t:ℂ)*(u:ℂ)*Complex.I = ((-t*u:ℝ):ℂ)*Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

private lemma integrable_phase_mul {f : ℝ → ℂ} (hf : Integrable f) (t : ℝ) :
    Integrable (fun u => f u * Complex.exp (-(t:ℂ)*(u:ℂ)*Complex.I)) := by
  apply hf.norm.mono' (hf.aestronglyMeasurable.mul (by fun_prop))
  exact ae_of_all _ (fun u => by
    change ‖f u*Complex.exp (-(t:ℂ)*(u:ℂ)*Complex.I)‖ ≤ ‖f u‖
    rw [norm_mul,phase_norm,mul_one])

private lemma integrable_rowFourierCutoff {m : ℕ} (p : Fin m → ℝ) (V : ℝ)
    (hV : 0<V) (hVeq : V=∑ i, (p i * (1 - p i))) :
    Integrable (rowFourierCutoff p V) := by
  have hg : Integrable (fun u : ℝ => Real.exp (-2*u^2/Real.pi^2)) := by
    convert integrable_exp_neg_mul_sq (by positivity : 0<(2:ℝ)/Real.pi^2) using 1
    ext u; congr 1; ring
  apply hg.mono' (measurable_rowFourierCutoff p V).aestronglyMeasurable
  exact ae_of_all _ (fun u => cutoff_bernoulli_gaussian_envelope p V u hV hVeq)

private lemma integrable_gaussian_kernel : Integrable (fun u : ℝ => (Real.exp (-u^2/2):ℂ)) := by
  have hg : Integrable (fun u : ℝ => Real.exp (-u^2/2)) := by
    convert integrable_exp_neg_mul_sq (by norm_num : 0<(1:ℝ)/2) using 1
    ext u; congr 1; ring
  exact hg.ofReal

private lemma uniform_lattice_error_bound {m : ℕ} (p : Fin m → unitInterval) (V : ℝ)
    (hV : 0<V) (hVeq : V=rowVariance p) (k : ℤ) :
    |Real.sqrt V*rowMass p k-(ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-rowMean p)/Real.sqrt V)| ≤
      (2*Real.pi)⁻¹ * ∫ u : ℝ,
        ‖rowFourierCutoff (fun i => (p i:ℝ)) V u - (Real.exp (-u^2/2):ℂ)‖ := by
  let t : ℝ := ((k:ℝ)-rowMean p)/Real.sqrt V
  let A : ℝ → ℂ := rowFourierCutoff (fun i => (p i:ℝ)) V
  let B : ℝ → ℂ := fun u => (Real.exp (-u^2/2):ℂ)
  let E : ℝ → ℂ := fun u => Complex.exp (-(t:ℂ)*(u:ℂ)*Complex.I)
  have hA : Integrable A := integrable_rowFourierCutoff _ V hV hVeq
  have hB : Integrable B := integrable_gaussian_kernel
  have hAE : Integrable (fun u => A u*E u) := integrable_phase_mul hA t
  have hBE : Integrable (fun u => B u*E u) := integrable_phase_mul hB t
  have hmass := cutoff_lattice_fourier_inversion p V hV k
  have hnorm := normalPDF_fourier_integral t
  have he : ((Real.sqrt V*rowMass p k-(ProbabilityTheory.gaussianPDFReal 0 1) t:ℝ):ℂ) =
      ((2*Real.pi)⁻¹:ℝ)*(∫ u : ℝ, (A u-B u)*E u) := by
    rw [Complex.ofReal_sub,hmass,hnorm,←mul_sub]
    congr 1
    simp only [A,B,E]
    simp_rw [mul_comm (Complex.exp _) (Real.exp _:ℂ)]
    rw [←integral_sub hAE hBE]
    apply integral_congr_ae
    exact ae_of_all _ (fun u => by dsimp [A,B,E]; ring)
  have h := norm_integral_le_integral_norm (μ := volume) (fun u : ℝ => (A u-B u)*E u)
  have hn (u : ℝ) : ‖(A u-B u)*E u‖ = ‖A u-B u‖ := by
    rw [norm_mul]; dsimp [E]; rw [phase_norm,mul_one]
  simp_rw [hn] at h
  have hc : 0≤(2*Real.pi)⁻¹ := by positivity
  have hh := mul_le_mul_of_nonneg_left h hc
  have hleft : ‖((Real.sqrt V*rowMass p k-(ProbabilityTheory.gaussianPDFReal 0 1) t:ℝ):ℂ)‖ =
      (2*Real.pi)⁻¹ * ‖∫ u : ℝ, (A u-B u)*E u‖ := by
    rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
  rw [←hleft,Complex.norm_real,Real.norm_eq_abs] at hh
  exact hh

lemma bernoulli_array_uniform_lattice_limit {m : ℕ → ℕ}
    (p : ∀ n, Fin (m n) → unitInterval)
    (hV : Tendsto (fun n => rowVariance (p n)) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ k : ℤ,
      |Real.sqrt (rowVariance (p n))*rowMass (p n) k -
        (ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-rowMean (p n))/Real.sqrt (rowVariance (p n)))| < ε := by
  have hvalid : ∀ᶠ n in atTop,
      (∀ i, 0≤(p n i:ℝ) ∧ (p n i:ℝ)≤1) ∧
      rowVariance (p n)=∑ i, ((p n i:ℝ) * (1 - (p n i:ℝ))) ∧ 0<rowVariance (p n) := by
    filter_upwards [hV.eventually_gt_atTop 0] with n hn
    exact ⟨fun i => ⟨(p n i).2.1,(p n i).2.2⟩,rfl,hn⟩
  have hL1 := bernoulli_array_fourier_L1_gaussian_limit
    (fun n i => (p n i:ℝ)) (fun n => rowVariance (p n)) hvalid hV (fun n => rfl)
  have herr := hL1.const_mul ((2*Real.pi)⁻¹)
  simp only [mul_zero] at herr
  intro ε hε
  have he := (tendsto_order.1 herr).2 ε hε
  filter_upwards [he,hV.eventually_gt_atTop 0] with n hn hpos
  intro k
  exact lt_of_le_of_lt (uniform_lattice_error_bound (p n) _ hpos rfl k) hn
open Real Filter Topology

private lemma standardized_floor_error (a s t : ℝ) (hs : 0<s) :
    |(((⌊a+t*s⌋:ℤ):ℝ)-a)/s-t| < s⁻¹ := by
  have hlo := Int.floor_le (a+t*s)
  have hhi := Int.lt_floor_add_one (a+t*s)
  have he : (((⌊a+t*s⌋:ℤ):ℝ)-a)/s-t =
      (((⌊a+t*s⌋:ℤ):ℝ)-(a+t*s))/s := by field_simp; ring
  rw [he,abs_div,abs_of_pos hs,abs_of_nonpos (by linarith)]
  rw [inv_eq_one_div]
  exact (div_lt_div_iff_of_pos_right hs).2 (by linarith)

lemma uniform_lattice_limit_to_floor (a : ℕ → ℤ → ℝ) (M S : ℕ → ℝ)
    (hS : Tendsto S atTop atTop)
    (hlattice : ∀ ε>0, ∀ᶠ n in atTop, ∀ k : ℤ,
      |S n*a n k-(ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-M n)/S n)| < ε) :
    ∀ ε>0, ∀ᶠ n in atTop, ∀ t : ℝ,
      |S n*a n ⌊M n+t*S n⌋-(ProbabilityTheory.gaussianPDFReal 0 1) t| < ε := by
  intro ε hε
  have hε2 : 0<ε/2 := by positivity
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuous_iff.1 normalPDF_uniformContinuous (ε/2) hε2
  have hinv : Tendsto (fun n => (S n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hS
  have hsmall := (tendsto_order.1 hinv).2 δ hδ
  filter_upwards [hlattice (ε/2) hε2,hS.eventually_gt_atTop 0,hsmall] with n hn hs hns
  intro t
  let k : ℤ := ⌊M n+t*S n⌋
  change |S n*a n k-(ProbabilityTheory.gaussianPDFReal 0 1) t|<ε
  have hk : |((k:ℝ)-M n)/S n-t| < δ :=
    lt_trans (standardized_floor_error (M n) (S n) t hs) hns
  have hc := hclose (by simpa only [Real.dist_eq] using hk)
  rw [Real.dist_eq] at hc
  calc
    _ ≤ |S n*a n k-(ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-M n)/S n)| +
      |(ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-M n)/S n)-(ProbabilityTheory.gaussianPDFReal 0 1) t| := by
        have hh := abs_add_le (S n*a n k-(ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-M n)/S n))
          ((ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-M n)/S n)-(ProbabilityTheory.gaussianPDFReal 0 1) t)
        have he : (S n*a n k-(ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-M n)/S n)) +
            ((ProbabilityTheory.gaussianPDFReal 0 1) (((k:ℝ)-M n)/S n)-(ProbabilityTheory.gaussianPDFReal 0 1) t) = S n*a n k-(ProbabilityTheory.gaussianPDFReal 0 1) t := by ring
        rw [he] at hh
        exact hh
    _ < ε := by linarith [hn k]

def mu (f : ℝ[X]) : ℝ := (derivative f).eval 1 / f.eval 1


def sigmaSq (f : ℝ[X]) : ℝ :=
  (derivative (derivative f)).eval 1 / f.eval 1 + mu f - mu f ^ 2


def sigma (f : ℝ[X]) : ℝ := √(sigmaSq f)


def prob (f : ℝ[X]) (k : ℤ) : ℝ :=
  if 0 ≤ k then f.coeff k.toNat / f.eval 1 else 0


private lemma normalCDF_eq_gaussian (t : ℝ) :
    StatLean.HypothesisTesting.stdNormalCDF t =
      ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1) t := by
  rw [ProbabilityTheory.cdf_eq_real]
  rfl

private lemma normalPDF_eq_gaussian (t : ℝ) :
    StatLean.HypothesisTesting.stdNormalPDF t = ProbabilityTheory.gaussianPDFReal 0 1 t := by
  exact StatLean.HypothesisTesting.stdNormalPDF_eq_gaussianPDFReal t

def CLT (f : ℕ → ℝ[X]) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
  |(∑ k ∈ (range ((f n).natDegree + 1)).filter
     (fun k : ℕ => (k : ℝ) ≤ mu (f n) + t * sigma (f n)), prob (f n) k) - StatLean.HypothesisTesting.stdNormalCDF t| < ε


def LLT (f : ℕ → ℝ[X]) : Prop := ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
  |sigma (f n) * prob (f n) ⌊mu (f n) + t * sigma (f n)⌋ - StatLean.HypothesisTesting.stdNormalPDF t| < ε

def bernoulliPGF (p : ℝ) : ℝ[X] := C (1-p) + C p * X


def normalized (f : ℝ[X]) : ℝ[X] := C (f.eval 1)⁻¹ * f

lemma sigmaSq_mul (f h : ℝ[X]) (hf : f.eval 1 ≠ 0) (hh : h.eval 1 ≠ 0) :
    sigmaSq (f*h) = sigmaSq f + sigmaSq h := by
  simp only [sigmaSq, mu, derivative_mul, derivative_add, eval_add, eval_mul]
  field_simp
  <;> ring


lemma sigmaSq_C (c : ℝ) : sigmaSq (C c) = 0 := by
  simp [sigmaSq, mu]


lemma sigmaSq_X : sigmaSq (X : ℝ[X]) = 0 := by
  simp [sigmaSq, mu]

open scoped Classical in
private lemma bernoulli_real_event {m : ℕ} (p : Fin m → unitInterval) (s : Set (Fin m → Bool)) :
    (bernoulliSpace p).real s = ∑ x : Fin m → Bool, if x∈s then bernoulliWeight p x else 0 := by
  classical
  have he : s = (univ.filter fun x => x∈s : Finset (Fin m → Bool)) := by ext; simp
  rw [he,←sum_measureReal_singleton,sum_filter]
  simp [bernoulli_atom]

private lemma bernoulli_event_mass {m : ℕ} (p : Fin m → unitInterval) (k : ℕ) :
    (bernoulliSpace p).real {x | 1+∑ i, Bool.toNat (x i) = k} =
      ∑ x : Fin m → Bool, if 1+∑ i, Bool.toNat (x i) = k then bernoulliWeight p x else 0 := by
  classical
  simpa only [Set.mem_setOf_eq] using
    bernoulli_real_event p {x | 1 + ∑ i, Bool.toNat (x i) = k}


private lemma bernoulli_pgf_expansion {m : ℕ} (p : Fin m → unitInterval) :
    (∏ i, bernoulliPGF (p i:ℝ)) =
      ∑ x : Fin m → Bool, C (bernoulliWeight p x) * X^(∑ i, Bool.toNat (x i)) := by
  have hlin (i : Fin m) : bernoulliPGF (p i:ℝ) =
      ∑ b : Bool, C (if b then (p i:ℝ) else 1-(p i:ℝ)) * X^(Bool.toNat b) := by
    simp [bernoulliPGF, Bool.toNat, Fintype.sum_bool, add_comm]
  simp_rw [hlin]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro x hx
  rw [prod_mul_distrib, ← map_prod, prod_pow_eq_pow_sum]
  rfl


private lemma bernoulli_coefficient_law {m : ℕ} (p : Fin m → unitInterval) (k : ℕ) :
    (X * ∏ i, bernoulliPGF (p i:ℝ) : ℝ[X]).coeff k =
      (bernoulliSpace p).real {x | 1+∑ i, Bool.toNat (x i) = k} := by
  rw [bernoulli_pgf_expansion, mul_sum, finsetSum_coeff, bernoulli_event_mass]
  apply sum_congr rfl
  intro x hx
  rw [show (X:ℝ[X]) * (C (bernoulliWeight p x)*X^(∑ i, Bool.toNat (x i))) =
    C (bernoulliWeight p x)*X^(1+∑ i, Bool.toNat (x i)) by rw [pow_add]; ring]
  simp only [coeff_C_mul_X_pow]
  split_ifs <;> simp_all [eq_comm]

open Polynomial Finset Filter Real MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval

private def standardizedRow {m : ℕ} (p : Fin m → unitInterval) (V : ℝ) : ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map
    (⟨bernoulliSpace p, inferInstance⟩ : ProbabilityMeasure (Fin m → Bool))
    (f := fun x => ((∑ i, (Bool.toNat (x i):ℝ)) - rowMean p)/Real.sqrt V)

private lemma standardizedRow_charFun {m : ℕ} (p : Fin m → unitInterval) (V u : ℝ) :
    charFun (standardizedRow p V : Measure ℝ) u =
      ∏ i, centeredBernoulli (p i:ℝ) (u/Real.sqrt V) := by
  change charFun ((bernoulliSpace p).map _) u = _
  rw [charFun_apply_real,integral_map (measurable_of_finite _).aemeasurable (by fun_prop)]
  have he (x : Fin m → Bool) :
      Complex.exp ((u:ℂ)*(((∑ i, (Bool.toNat (x i):ℝ))-rowMean p)/Real.sqrt V:ℝ)*Complex.I) =
      ∏ i, Complex.exp ((((Bool.toNat (x i):ℝ)-(p i:ℝ))*(u/Real.sqrt V):ℝ)*Complex.I) := by
    rw [←Complex.exp_sum]
    congr 1
    simp only [rowMean,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_sum,
      Complex.ofReal_mul]
    rw [←sum_sub_distrib,Finset.sum_div,Finset.mul_sum,Finset.sum_mul]
    apply sum_congr rfl
    intro i hi
    ring
  simp_rw [he]
  unfold bernoulliSpace
  rw [integral_fintype_prod_eq_prod
    (fun (i : Fin m) (b : Bool) => Complex.exp ((((Bool.toNat b:ℝ)-(p i:ℝ))*(u/Real.sqrt V):ℝ)*Complex.I))]
  apply prod_congr rfl
  intro i hi
  rw [integral_bernoulliMeasure]
  simp only [Bool.toNat_false,Bool.toNat_true,Nat.cast_one,Nat.cast_zero,Complex.real_smul]
  unfold centeredBernoulli
  conv_lhs => rw [add_comm]
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    push_cast
    ring

private lemma bernoulli_array_uniform_gaussian_cdf {m : ℕ → ℕ}
    (p : ∀ n, Fin (m n) → unitInterval) (hV : Tendsto (fun n => rowVariance (p n)) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
      |cdf (standardizedRow (p n) (rowVariance (p n)):Measure ℝ) t - (ProbabilityTheory.cdf (ProbabilityTheory.gaussianReal 0 1)) t| < ε := by
  apply charFun_limit_uniform_gaussian_cdf
  intro u
  simp only [standardizedRow_charFun]
  apply centered_bernoulli_charFun_tendsto (fun n i => (p n i:ℝ)) (fun n => rowVariance (p n)) u
  · filter_upwards [hV.eventually_gt_atTop 0] with n hn
    exact ⟨fun i => ⟨(p n i).2.1,(p n i).2.2⟩,rfl,hn⟩
  · exact hV
  · intro n; rfl
open Polynomial Finset Real Filter MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval

private lemma bernoulliPGF_eval_one (p : ℝ) : (bernoulliPGF p).eval 1 = 1 := by
  simp [bernoulliPGF]

private lemma mu_mul (f h : ℝ[X]) (hf : f.eval 1 ≠ 0) (hh : h.eval 1 ≠ 0) :
    mu (f*h) = mu f+mu h := by
  unfold mu
  rw [derivative_mul,eval_add,eval_mul,eval_mul,eval_mul]
  field_simp
  <;> ring

private lemma mu_bernoulliPGF (p : ℝ) : mu (bernoulliPGF p) = p := by
  simp [mu,bernoulliPGF]

private lemma sigmaSq_bernoulliPGF (p : ℝ) : sigmaSq (bernoulliPGF p) = (p * (1 - p)) := by
  simp [sigmaSq,mu,bernoulliPGF]
  ring

private lemma bernoulli_product_eval_one {ι : Type*} (s : Finset ι) (p : ι → ℝ) :
    (∏ i ∈ s, bernoulliPGF (p i)).eval 1 = 1 := by
  simp [eval_prod,bernoulliPGF_eval_one]

private lemma bernoulli_product_mu {ι : Type*} (s : Finset ι) (p : ι → ℝ) :
    mu (∏ i ∈ s, bernoulliPGF (p i)) = ∑ i ∈ s, p i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu]
  | @insert a s ha ih =>
    rw [prod_insert ha,sum_insert ha,mu_mul _ _
      (by rw [bernoulliPGF_eval_one]; norm_num)
      (by rw [bernoulli_product_eval_one]; norm_num),mu_bernoulliPGF,ih]

private lemma bernoulli_product_sigmaSq {ι : Type*} (s : Finset ι) (p : ι → ℝ) :
    sigmaSq (∏ i ∈ s, bernoulliPGF (p i)) = ∑ i ∈ s, (p i * (1 - p i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sigmaSq,mu]
  | @insert a s ha ih =>
    rw [prod_insert ha,sum_insert ha,sigmaSq_mul _ _
      (by rw [bernoulliPGF_eval_one]; norm_num)
      (by rw [bernoulli_product_eval_one]; norm_num),sigmaSq_bernoulliPGF,ih]

private lemma mu_normalized (f : ℝ[X]) (hf : f.eval 1 ≠ 0) : mu (normalized f) = mu f := by
  rw [normalized, mu_mul _ _ (by simpa using inv_ne_zero hf) hf]
  simp [mu]

private lemma sigmaSq_normalized (f : ℝ[X]) (hf : f.eval 1 ≠ 0) :
    sigmaSq (normalized f) = sigmaSq f := by
  rw [normalized,sigmaSq_mul _ _ (by simpa using inv_ne_zero hf) hf,sigmaSq_C,zero_add]

lemma factorization_moments {f : ℝ[X]} {m : ℕ} (p : Fin m → unitInterval)
    (hpgf : normalized f = X*∏ i, bernoulliPGF (p i:ℝ)) :
    f.eval 1 ≠ 0 ∧ mu f = 1+rowMean p ∧ sigmaSq f = rowVariance p := by
  have he := congrArg (fun h : ℝ[X] => h.eval 1) hpgf
  simp only [normalized,eval_mul,eval_C,eval_X,one_mul,bernoulli_product_eval_one] at he
  have hf : f.eval 1 ≠ 0 := by intro hf; simp [hf] at he
  refine ⟨hf,?_,?_⟩
  · rw [←mu_normalized f hf,hpgf,mu_mul _ _ (by simp)
      (by rw [bernoulli_product_eval_one]; norm_num),bernoulli_product_mu]
    simp [mu,rowMean]
  · rw [←sigmaSq_normalized f hf,hpgf,sigmaSq_mul _ _ (by simp)
      (by rw [bernoulli_product_eval_one]; norm_num),sigmaSq_X,zero_add,bernoulli_product_sigmaSq]
    rfl

private lemma factorization_integer_mass {f : ℝ[X]} {m : ℕ} (p : Fin m → unitInterval)
    (hpgf : normalized f = X*∏ i, bernoulliPGF (p i:ℝ)) (k : ℤ) :
    prob f k = rowMass p (k-1) := by
  classical
  have hnat (j : ℕ) : prob f j = (bernoulliSpace p).real {x | 1+∑ i, Bool.toNat (x i)=j} := by
    rw [←bernoulli_coefficient_law,←hpgf]
    simp [prob,normalized,coeff_C_mul,div_eq_mul_inv,mul_comm]
  by_cases hk : 0≤k
  · have hc : (k.toNat:ℤ)=k := Int.toNat_of_nonneg hk
    rw [←hc,hnat,bernoulli_event_mass]
    unfold rowMass
    apply sum_congr rfl
    intro x hx
    have hh : 1+∑ i, Bool.toNat (x i)=k.toNat ↔ ((∑ i, Bool.toNat (x i):ℕ):ℤ)=(k.toNat:ℤ)-1 := by omega
    simp only [hh]
  · simp only [prob,if_neg hk]
    unfold rowMass
    apply Eq.symm
    apply sum_eq_zero
    intro x hx
    have hh : ¬((∑ i, Bool.toNat (x i):ℕ):ℤ)=k-1 := by omega
    simp only [if_neg hh]
open Polynomial Finset Real MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators unitInterval Classical

private lemma bit_sum_le {m : ℕ} (x : Fin m → Bool) : ∑ i, Bool.toNat (x i) ≤ m := by
  calc
    _ ≤ ∑ i : Fin m, 1 := sum_le_sum (fun i hi => by cases x i <;> simp [Bool.toNat])
    _ = _ := by simp

private lemma factorization_finite_cdf {f : ℝ[X]} {m : ℕ} (p : Fin m → unitInterval)
    (hpgf : normalized f = X*∏ i, bernoulliPGF (p i:ℝ)) (y : ℝ) :
    (∑ k ∈ (range (f.natDegree+1)).filter (fun k : ℕ => (k:ℝ)≤y), prob f k) =
      (bernoulliSpace p).real {x | (1+∑ i, Bool.toNat (x i):ℕ) ≤ y} := by
  classical
  let N := max (f.natDegree+1) (m+2)
  have hn : f.natDegree+1 ≤ N := le_max_left _ _
  have hm : m+2 ≤ N := le_max_right _ _
  have hext : (∑ k ∈ (range (f.natDegree+1)).filter (fun k : ℕ => (k:ℝ)≤y), prob f k) =
      ∑ k ∈ (range N).filter (fun k : ℕ => (k:ℝ)≤y), prob f k := by
    apply sum_subset (filter_subset_filter _ (range_mono hn))
    intro k hk hnot
    have hkN := (mem_filter.1 hk).1
    have hky := (mem_filter.1 hk).2
    have hd : f.natDegree<k := by
      have hnotrange : ¬k<f.natDegree+1 := by
        intro hlt; apply hnot; exact mem_filter.2 ⟨mem_range.2 hlt,hky⟩
      omega
    simp [prob,coeff_eq_zero_of_natDegree_lt hd]
  have hnat (j : ℕ) : prob f j = ∑ x : Fin m → Bool,
      if 1+∑ i, Bool.toNat (x i)=j then bernoulliWeight p x else 0 := by
    rw [←bernoulli_event_mass,←bernoulli_coefficient_law,←hpgf]
    simp [prob,normalized,div_eq_mul_inv,mul_comm]
  rw [hext,bernoulli_real_event,sum_filter]
  simp_rw [hnat]
  simp only [Set.mem_ofPred_eq]
  have hswitch : (∑ k ∈ range N, if (k:ℝ)≤y then
      ∑ x : Fin m → Bool, if 1+∑ i, Bool.toNat (x i)=k then bernoulliWeight p x else 0 else 0) =
      ∑ x : Fin m → Bool, ∑ k ∈ range N,
        if (k:ℝ)≤y then (if 1+∑ i, Bool.toNat (x i)=k then bernoulliWeight p x else 0) else 0 := by
    rw [←sum_comm]
    apply sum_congr rfl
    intro k hk
    split_ifs <;> simp
  rw [hswitch]
  apply sum_congr rfl
  intro x hx
  have hxN : 1+∑ i, Bool.toNat (x i) ∈ range N := mem_range.2 (by have := bit_sum_le x; omega)
  have hterm (k : ℕ) : (if (k:ℝ)≤y then
      (if 1+∑ i, Bool.toNat (x i)=k then bernoulliWeight p x else 0) else 0) =
      if 1+∑ i, Bool.toNat (x i)=k then
        (if ((1+∑ i, Bool.toNat (x i):ℕ):ℝ)≤y then bernoulliWeight p x else 0) else 0 := by
    by_cases hk : 1+∑ i, Bool.toNat (x i)=k
    · subst k; simp
    · simp [hk]
  simp_rw [hterm]
  simp [hxN]

private lemma factorization_standardized_cdf {f : ℝ[X]} {m : ℕ} (p : Fin m → unitInterval)
    (hpgf : normalized f = X*∏ i, bernoulliPGF (p i:ℝ)) (hV : 0<rowVariance p) (t : ℝ) :
    (∑ k ∈ (range (f.natDegree+1)).filter (fun k : ℕ => (k:ℝ)≤mu f+t*sigma f), prob f k) =
      cdf (standardizedRow p (rowVariance p):Measure ℝ) t := by
  obtain ⟨hf,hmu,hvar⟩ := factorization_moments p hpgf
  rw [factorization_finite_cdf p hpgf,cdf_eq_real]
  change (bernoulliSpace p).real _ = ((bernoulliSpace p).map _).real (Set.Iic t)
  rw [map_measureReal_apply (measurable_of_finite _) measurableSet_Iic]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_ofPred_eq,hmu,sigma,hvar,Nat.cast_add,Nat.cast_one,Nat.cast_sum]
  have hs : 0<Real.sqrt (rowVariance p) := Real.sqrt_pos.2 hV
  rw [div_le_iff₀ hs]
  constructor <;> intro h <;> linarith
open Polynomial Finset Real MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators unitInterval

lemma bernoulli_polynomial_uniform_limits (f : ℕ → ℝ[X]) {m : ℕ → ℕ}
    (p : ∀ n, Fin (m n) → unitInterval)
    (hfac : ∀ᶠ n in atTop, normalized (f n) = X*∏ i, bernoulliPGF (p n i:ℝ))
    (hV : Tendsto (fun n => rowVariance (p n)) atTop atTop) : CLT f ∧ LLT f := by
  constructor
  · intro ε hε
    filter_upwards [bernoulli_array_uniform_gaussian_cdf p hV ε hε,
      hfac,hV.eventually_gt_atTop 0] with n hn hpgf hpos
    intro t
    rw [factorization_standardized_cdf (p n) hpgf hpos]
    simpa only [normalCDF_eq_gaussian] using hn t
  · have hS : Tendsto (fun n => sigma (f n)) atTop atTop := by
      apply (Real.tendsto_sqrt_atTop.comp hV).congr'
      filter_upwards [hfac] with n hpgf
      simp only [sigma,(factorization_moments (p n) hpgf).2.2,Function.comp_def]
    have hll := uniform_lattice_limit_to_floor (fun n k => prob (f n) k) (fun n => mu (f n))
      (fun n => sigma (f n)) hS (by
        intro ε hε
        filter_upwards [bernoulli_array_uniform_lattice_limit p hV ε hε,hfac] with n hn hpgf
        intro k
        obtain ⟨hf,hmu,hvar⟩ := factorization_moments (p n) hpgf
        rw [factorization_integer_mass (p n) hpgf,sigma,hvar,hmu]
        have hk : (((k-1:ℤ):ℝ)-rowMean (p n)) = (k:ℝ)-(1+rowMean (p n)) := by push_cast; ring
        simpa only [hk] using hn (k-1))
    change ∀ ε > 0, ∀ᶠ n in atTop, ∀ t : ℝ,
      |sigma (f n) * prob (f n) ⌊mu (f n) + t * sigma (f n)⌋ - StatLean.HypothesisTesting.stdNormalPDF t| < ε
    simpa only [normalPDF_eq_gaussian] using hll

end D5.S3.Analytic.Probability.BernoulliTriangularLimits
