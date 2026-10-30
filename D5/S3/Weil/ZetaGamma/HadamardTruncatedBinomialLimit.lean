/- GID: D5/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaGamma/HadamardTruncatedBinomialLimit
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The truncated binomial sums converge to the entire Hadamard factorial function. -/

/- Mathematical classification:
   IsHadamard: proof_shape: bind-only (definition); escape_witness: none; consumers: claim, hadamard_candidate_exists, hadamard_unique, result; Direct frozen dependencies: none
   truncation: proof_shape: bind-only (definition); escape_witness: none; consumers: candidate_left_limit, claim, result, truncation_as_cpow, truncation_global_of_left, truncation_left_integral_limit, truncation_limit_step, truncation_riemann_decomposition, truncation_shift_identity; Direct frozen dependencies: none
   claim: proof_shape: bind-only (definition); escape_witness: none; consumers: result; Direct frozen dependencies: none
   leftKernel: proof_shape: bind-only (definition); escape_witness: none; consumers: candidate_left_limit, left_kernel_continuous, scaled_term_kernel, truncation_left_integral_limit, truncation_riemann_decomposition; Direct frozen dependencies: none
   reciprocalGamma: proof_shape: bind-only (definition); escape_witness: none; consumers: hadamardCandidate, hadamard_candidate_differentiable, hadamard_candidate_factorial, hadamard_candidate_one, hadamard_candidate_quotient, hadamard_candidate_shift, reciprocal_gamma_deriv_regular, reciprocal_gamma_deriv_shift, reciprocal_gamma_deriv_zero, reciprocal_gamma_differentiable, reciprocal_gamma_duplication, reciprocal_gamma_shift, truncation_limit_step; Direct frozen dependencies: none
   hadamardCandidate: proof_shape: bind-only (definition); escape_witness: none; consumers: candidate_left_limit, hadamard_candidate_differentiable, hadamard_candidate_exists, hadamard_candidate_factorial, hadamard_candidate_one, hadamard_candidate_quotient, hadamard_candidate_shift, result, truncation_global_of_left, truncation_limit_step; Direct frozen dependencies: none
   nielsenBeta: proof_shape: bind-only (definition); escape_witness: none; consumers: beta_integral_identification, beta_integral_nat, candidate_left_limit, nielsen_beta_one, nielsen_beta_shift, nielsen_paired_hasSum; Direct frozen dependencies: none
   betaIntegral: proof_shape: bind-only (definition); escape_witness: none; consumers: beta_integral_identification, beta_integral_nat, beta_integral_one, beta_integral_shift, candidate_left_limit, paired_integrals_hasSum; Direct frozen dependencies: none
   coefficient_product: proof_shape: bind-only; escape_witness: none; consumers: coefficient_scaled_eq; Direct frozen dependencies: F1, F4
   coefficient_scaled_eq: proof_shape: bind-only; escape_witness: none; consumers: coefficient_scaled_tendsto; Direct frozen dependencies: F1, F4
   coefficient_scaled_tendsto: proof_shape: bind-only; escape_witness: none; consumers: coefficient_scaled_tendsto_all; Direct frozen dependencies: F1, F4
   coefficient_scaled_tendsto_all: proof_shape: bind-only; escape_witness: none; consumers: truncation_left_integral_limit, truncation_limit_step; Direct frozen dependencies: F1, F4
   alternating_choose_sum: proof_shape: bind-only; escape_witness: none; consumers: finite_sum_shift; Direct frozen dependencies: none
   choose_shift_mul: proof_shape: bind-only; escape_witness: none; consumers: finite_sum_shift; Direct frozen dependencies: none
   finite_sum_shift: proof_shape: bind-only; escape_witness: none; consumers: truncation_shift_identity; Direct frozen dependencies: none
   complex_left_riemann: proof_shape: bind-only; escape_witness: none; consumers: weighted_left_riemann; Direct frozen dependencies: F2
   weighted_left_riemann: proof_shape: bind-only; escape_witness: none; consumers: truncation_left_integral_limit; Direct frozen dependencies: F2, F3
   left_kernel_continuous: proof_shape: bind-only; escape_witness: none; consumers: truncation_left_integral_limit; Direct frozen dependencies: none
   nat_cpow_tendsto_zero: proof_shape: bind-only; escape_witness: none; consumers: truncation_left_integral_limit; Direct frozen dependencies: F6
   scaled_term_kernel: proof_shape: bind-only; escape_witness: none; consumers: truncation_riemann_decomposition; Direct frozen dependencies: none
   truncation_riemann_decomposition: proof_shape: bind-only; escape_witness: none; consumers: truncation_left_integral_limit; Direct frozen dependencies: none
   truncation_left_integral_limit: proof_shape: bind-only; escape_witness: none; consumers: candidate_left_limit; Direct frozen dependencies: F6, F2, F3, F1, F4
   reciprocal_gamma_differentiable: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_differentiable, reciprocal_gamma_deriv_shift; Direct frozen dependencies: none
   reciprocal_gamma_shift: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_shift, reciprocal_gamma_deriv_shift; Direct frozen dependencies: none
   reciprocal_gamma_deriv_shift: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_shift, reciprocal_gamma_deriv_zero; Direct frozen dependencies: none
   reciprocal_gamma_deriv_zero: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_one; Direct frozen dependencies: none
   reciprocal_gamma_duplication: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_quotient, hadamard_candidate_shift; Direct frozen dependencies: none
   hadamard_candidate_differentiable: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_exists, result; Direct frozen dependencies: none
   hadamard_candidate_shift: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_factorial, truncation_limit_step; Direct frozen dependencies: none
   hadamard_candidate_one: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_factorial; Direct frozen dependencies: none
   hadamard_candidate_factorial: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_exists, result; Direct frozen dependencies: none
   reciprocal_gamma_deriv_regular: proof_shape: bind-only; escape_witness: none; consumers: hadamard_candidate_quotient; Direct frozen dependencies: none
   hadamard_candidate_quotient: proof_shape: bind-only; escape_witness: none; consumers: candidate_left_limit, hadamard_candidate_exists, result; Direct frozen dependencies: none
   hadamard_candidate_exists: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none
   nielsen_paired_hasSum: proof_shape: bind-only; escape_witness: none; consumers: beta_integral_identification; Direct frozen dependencies: F5
   paired_integral: proof_shape: bind-only; escape_witness: none; consumers: paired_integrals_hasSum; Direct frozen dependencies: none
   paired_pointwise: proof_shape: bind-only; escape_witness: none; consumers: paired_integrals_hasSum; Direct frozen dependencies: none
   paired_integrals_hasSum: proof_shape: bind-only; escape_witness: none; consumers: beta_integral_identification; Direct frozen dependencies: none
   beta_kernel_integrable: proof_shape: bind-only; escape_witness: none; consumers: beta_integral_shift; Direct frozen dependencies: none
   beta_integral_shift: proof_shape: bind-only; escape_witness: none; consumers: beta_integral_nat; Direct frozen dependencies: none
   nielsen_beta_shift: proof_shape: bind-only; escape_witness: none; consumers: beta_integral_nat; Direct frozen dependencies: none
   beta_integral_one: proof_shape: bind-only; escape_witness: none; consumers: beta_integral_nat; Direct frozen dependencies: none
   nielsen_beta_one: proof_shape: bind-only; escape_witness: none; consumers: beta_integral_nat; Direct frozen dependencies: none
   beta_integral_nat: proof_shape: bind-only; escape_witness: none; consumers: beta_integral_identification; Direct frozen dependencies: none
   beta_integral_identification: proof_shape: bind-only; escape_witness: none; consumers: candidate_left_limit; Direct frozen dependencies: F5
   hadamard_unique: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: none
   truncation_as_cpow: proof_shape: bind-only; escape_witness: none; consumers: truncation_riemann_decomposition, truncation_shift_identity; Direct frozen dependencies: none
   truncation_shift_identity: proof_shape: bind-only; escape_witness: none; consumers: truncation_limit_step; Direct frozen dependencies: none
   truncation_limit_step: proof_shape: bind-only; escape_witness: none; consumers: truncation_global_of_left; Direct frozen dependencies: F1, F4
   truncation_global_of_left: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F1, F4
   candidate_left_limit: proof_shape: bind-only; escape_witness: none; consumers: result; Direct frozen dependencies: F6, F2, F3, F1, F4, F5
   result: proof_shape: bind-only; escape_witness: none; consumers: terminal settlement; Direct frozen dependencies: F6, F2, F3, F1, F4, F5
   admission_basis: open-problem-resolution (#22706; Proved)
   Direct frozen dependencies (immutable origin/dev declaration identities):
   F1: D5/S3/Analytic/SeriesInequalities/NormalizedPochhammerBounds.normalizedPochhammer; sha256:8028e63b4ee628208efd8d2dedc9f19e81071e44c05813cdd7fe42d943262562
   F2: D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.continuous_leftRiemann_tendsto; sha256:40aa63d616ac365dcfcc289a313be239d3bd822f580e416d3c31a988b8b2da08
   F3: D5/S3/Combinatorics/Permanental/CycleGeodesic/CycleGeodesicScaling.fin_fraction_mem_Icc; sha256:a78783227a0421f245b22d7e1800dad597d562309666ec8c118cc8c5d32cdcb2
   F4: D5/S3/Weil/Analytic/BaezDuarteNewton.signed_choose; sha256:d97a115905058d6924416ed70b70bd4d535d1973e7aa1d64ccc3bfd69dcc2d0b
   F5: D5/S3/Weil/ZetaGamma/GammaSeries.hasSum_digamma_series; sha256:420185419ae9805e6ebe2adf9effe6e6cbcea49ba1532a5ce1d523493152df4b
   F6: D5/S3/Weil/ZetaPntBounds/ZetaBoundsUpper.cpow_tendsto; sha256:3b6c7a329d1153738908031f0a2c2f2edc6bb1d34a0db80a9c0f02bede21f999
   Utility none: the declarations concern arbitrary complex parameters and analytic functions;
   no finite enumeration, checker, numeric reduction or isolated certified instance is delivered.
   The source definitions of IsHadamard and truncation retain their displayed expressions.
   The omitted infinite-tail limit is not asserted here.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/22862
-/
import D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
import D5.S3.Weil.Analytic.BaezDuarteNewton
import D5.S3.Combinatorics.Permanental.CycleGeodesic.CycleGeodesicScaling
import D5.S3.Weil.ZetaGamma.GammaSeries
import D5.S3.Weil.ZetaPntBounds.ZetaBoundsUpper

noncomputable section

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

open Filter Topology

/-- The classical entire Hadamard function, with the source's factorial interpolation
and its digamma quotient away from the removable positive-integer singularities. -/
def IsHadamard (H : ℂ → ℂ) : Prop :=
  Differentiable ℂ H ∧
    (∀ m : ℕ, H ((m : ℂ) + 1) = (m.factorial : ℂ)) ∧
    ∀ y : ℂ, (∀ m : ℕ, y ≠ (m : ℂ) + 1) →
      H y = (Complex.digamma (1 - y / 2) - Complex.digamma ((1 - y) / 2)) /
        (2 * Complex.Gamma (1 - y))

/-- The displayed finite sum. Only positive n matter for the limit. Powers of positive
integers use their real logarithm; Ring.choose owns generalized binomial coefficients. -/
def truncation (x : ℂ) (n : ℕ) : ℂ :=
  Complex.exp ((x + 1) * (Real.log (n : ℝ) : ℂ)) *
    ∑ k ∈ Finset.range (n + 1),
      ((-1 : ℂ) ^ k / ((n : ℂ) + (k : ℂ))) * Ring.choose x k

/-- OEIS A398064, the FORMULA line beginning "Conjecture: H(x+1)".
The source gives no parameter restriction; this binding reading is over all complex x.
Existence of the source's entire function is part of the assertion. -/
def claim : Prop :=
  (∃ H : ℂ → ℂ, IsHadamard H) ∧
    ∀ H : ℂ → ℂ, IsHadamard H →
      ∀ x : ℂ, Tendsto (truncation x) atTop (𝓝 (H (x + 1)))

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology Polynomial
open D5.S3.Analytic.SeriesInequalities.NormalizedPochhammerBounds
open D5.S3.Weil.Analytic.BaezDuarteNewton

-- Euler coefficient product identity.
private theorem coefficient_product (x : ℂ) (k : ℕ) :
    (∏ j ∈ Finset.range (k + 1), (-x + (j : ℂ))) =
      ((k : ℂ) - x) * (k.factorial : ℂ) * ((-1 : ℂ)^k * Ring.choose x k) := by
  have hc : (-1 : ℂ)^k * Ring.choose x k = normalizedPochhammer k (x + 1) := by
    simpa using (signed_choose k (x+1)).symm
  rw [hc, normalizedPochhammer, descPochhammer_eval_eq_prod_range]
  simp only [add_sub_cancel_right]
  rw [Finset.prod_range_succ]
  have hp : (∏ j ∈ Finset.range k, (-x + (j : ℂ))) =
      (-1 : ℂ)^k * ∏ j ∈ Finset.range k, (x - (j : ℂ)) := by
    rw [show (-1 : ℂ)^k = ∏ _j ∈ Finset.range k, (-1 : ℂ) by simp,
      ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hp]
  field_simp [show (k.factorial : ℂ) ≠ 0 by exact_mod_cast k.factorial_ne_zero]
  ring

private theorem coefficient_scaled_eq (x : ℂ) (hx : ∀ m : ℕ, x ≠ (m : ℂ))
    (k : ℕ) (hk : k ≠ 0) :
    (k : ℂ)^(x+1) * ((-1 : ℂ)^k * Ring.choose x k) =
      ((k : ℂ) / ((k : ℂ) - x)) / Complex.GammaSeq (-x) k := by
  have hn : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hp : (∏ j ∈ Finset.range (k + 1), (-x + (j : ℂ))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _ h
    exact hx j (by linear_combination -h)
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hprod := coefficient_product x k
  have hc : ((-1 : ℂ)^k * Ring.choose x k) ≠ 0 := by
    intro h
    rw [h, mul_zero] at hprod
    exact hp hprod
  have hkx : (k : ℂ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm (hx k))
  rw [Complex.GammaSeq, coefficient_product, Complex.cpow_neg,
    Complex.cpow_add _ _ hn, Complex.cpow_one]
  have hpow : (k : ℂ)^x ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn)
  field_simp

set_option maxHeartbeats 800000 in
private theorem coefficient_scaled_tendsto (x : ℂ) (hx : ∀ m : ℕ, x ≠ (m : ℂ)) :
    Tendsto (fun k : ℕ => (k : ℂ)^(x+1) * ((-1 : ℂ)^k * Ring.choose x k))
      atTop (𝓝 ((Complex.Gamma (-x))⁻¹)) := by
  have hg : Complex.Gamma (-x) ≠ 0 := Complex.Gamma_ne_zero (by
    intro m h
    exact hx m (neg_injective h))
  have ht := (tendsto_natCast_div_add_atTop (-x)).div
    (Complex.GammaSeq_tendsto_Gamma (-x)) hg
  simp only [one_div] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with k hk
  change (k : ℂ) / ((k : ℂ) + -x) / Complex.GammaSeq (-x) k = _
  simpa only [sub_eq_add_neg] using (coefficient_scaled_eq x hx k hk).symm

private theorem coefficient_scaled_tendsto_all (x : ℂ) :
    Tendsto (fun k : ℕ => (k : ℂ)^(x+1) * ((-1 : ℂ)^k * Ring.choose x k))
      atTop (𝓝 ((Complex.Gamma (-x))⁻¹)) := by
  by_cases hx : ∃ m : ℕ, x = (m : ℂ)
  · obtain ⟨m, rfl⟩ := hx
    simp only [Complex.Gamma_neg_nat_eq_zero, inv_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop m] with k hk
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hk, Nat.cast_zero, mul_zero, mul_zero]
  · exact coefficient_scaled_tendsto x (by simpa only [not_exists] using hx)

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology

-- Algebraic recurrence for the moving finite sum, without analytic assumptions.
private theorem alternating_choose_sum (x : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), (-1 : ℂ)^k * Ring.choose (x+1) k) =
      (-1 : ℂ)^n * Ring.choose x n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Ring.choose_succ_succ, pow_succ]
    ring

private theorem choose_shift_mul (x : ℂ) (k : ℕ) :
    (x+1-(k : ℂ)) * Ring.choose (x+1) k = (x+1) * Ring.choose x k := by
  cases k with
  | zero => simp
  | succ k =>
    have h := Ring.choose_smul_choose (R := ℂ) (x+1) (n := k+1) (k := 1) (by omega)
    simp only [Nat.choose_one_right, nsmul_eq_mul, Ring.choose_one_right,
      Nat.add_sub_cancel] at h
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at h ⊢
    have hp := Ring.choose_succ_succ x k
    linear_combination (x+1)*hp - h

private theorem finite_sum_shift (x : ℂ) (n : ℕ) (hn : n ≠ 0) :
    ((n : ℂ)+x+1) *
      (∑ k ∈ Finset.range (n+1), ((-1 : ℂ)^k / ((n : ℂ)+(k : ℂ))) * Ring.choose (x+1) k) =
    (x+1) *
      (∑ k ∈ Finset.range (n+1), ((-1 : ℂ)^k / ((n : ℂ)+(k : ℂ))) * Ring.choose x k) +
      (-1 : ℂ)^n * Ring.choose x n := by
  rw [← alternating_choose_sum x n, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (n : ℂ)+(k : ℂ) ≠ 0 := by
    exact_mod_cast (show n+k ≠ 0 by omega)
  have h := choose_shift_mul x k
  field_simp [hk]
  linear_combination h

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology MeasureTheory
open CycleGeodesic

private theorem complex_left_riemann {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℂ) * ∑ k : Fin n, f ((k : ℝ) / n))
      atTop (𝓝 (∫ t in (0 : ℝ)..1, f t)) := by
  have hr := continuous_leftRiemann_tendsto (Complex.continuous_re.comp_continuousOn hf)
  have hi := continuous_leftRiemann_tendsto (Complex.continuous_im.comp_continuousOn hf)
  have ht := hr.ofReal.add (hi.ofReal.mul_const Complex.I)
  convert ht using 1
  · ext n
    simp only [one_div, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sum]
    rw [mul_assoc, ← mul_add, Finset.sum_mul, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact (Complex.re_add_im (f ((k : ℝ) / n))).symm
  · congr 1
    have hr : (∫t in (0:ℝ)..1, (f t).re) = (∫t in (0:ℝ)..1, f t).re :=
      intervalIntegral.intervalIntegral_re (ContinuousOn.intervalIntegrable_of_Icc zero_le_one hf)
    have hi : (∫t in (0:ℝ)..1, (f t).im) = (∫t in (0:ℝ)..1, f t).im :=
      intervalIntegral.intervalIntegral_im (ContinuousOn.intervalIntegrable_of_Icc zero_le_one hf)
    change (∫t in (0:ℝ)..1,f t) = ↑(∫t in (0:ℝ)..1,(f t).re)+↑(∫t in (0:ℝ)..1,(f t).im)*Complex.I
    rw [hr, hi, Complex.re_add_im]

private theorem weighted_left_riemann {f : ℝ → ℂ} (hf : ContinuousOn f (Set.Icc 0 1))
    {d : ℕ → ℂ} {g : ℂ} (hd : Tendsto d atTop (𝓝 g)) :
    Tendsto (fun n : ℕ => ((n : ℝ)⁻¹ : ℂ) * ∑ k : Fin n, d k * f ((k : ℝ) / n))
      atTop (𝓝 (g * ∫ t in (0 : ℝ)..1, f t)) := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have he : Tendsto (fun k => ‖d k - g‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp hd
  have hm := he.cesaro.mul_const B
  simp only [zero_mul] at hm
  have herror : Tendsto (fun n : ℕ =>
      ((n : ℝ)⁻¹ : ℂ) * ∑ k : Fin n, (d k - g) * f ((k : ℝ) / n))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hm
    filter_upwards [eventually_ne_atTop 0] with n hn
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, ‖(d k - g) * f ((k : ℝ) / n)‖ := by
        gcongr
        exact norm_sum_le _ _
      _ ≤ (n : ℝ)⁻¹ * ∑ k : Fin n, ‖d k - g‖ * B := by
        gcongr with k
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hB _ (fin_fraction_mem_Icc hn k)) (norm_nonneg _)
      _ = _ := by
        rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun k:ℕ => ‖d k-g‖)]
        ring
  have ht := (complex_left_riemann hf).const_mul g
  convert ht.add herror using 1
  · ext n
    have hs : (∑k:Fin n, d k*f ((k:ℝ)/n)) =
        g*(∑k:Fin n,f ((k:ℝ)/n)) + ∑k:Fin n,(d k-g)*f ((k:ℝ)/n) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hs]
    ring
  · simp

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology MeasureTheory

private def leftKernel (x : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ)^(-x-1) / (1+(t : ℂ))

private theorem left_kernel_continuous (x : ℂ) (hx : x.re < -1) :
    ContinuousOn (leftKernel x) (Set.Icc 0 1) := by
  have he : 0 < (-x-1).re := by simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]; linarith
  have h : ContinuousOn (fun t:ℝ => (t:ℂ)^(-x-1)) (Set.Icc 0 1) :=
    (Complex.continuous_ofReal_cpow_const he).continuousOn
  apply h.div
  · fun_prop
  · intro t ht h0
    have hr := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.zero_re] at hr
    linarith [ht.1]

private theorem nat_cpow_tendsto_zero (x : ℂ) (hx : x.re < 0) :
    Tendsto (fun n : ℕ => (n : ℂ)^x) atTop (𝓝 0) := by
  simpa only [show (1 : ℂ) - (1 - x) = x by ring] using
    (Complex.cpow_tendsto (s := 1 - x) (by
      simp only [Complex.sub_re, Complex.one_re]
      linarith))

private theorem scaled_term_kernel (x : ℂ) (n k : ℕ) (hn : n ≠ 0) (hk : k ≠ 0) :
    (n : ℂ)^(x+1) * (((-1 : ℂ)^k / ((n : ℂ)+(k : ℂ))) * Ring.choose x k) =
      (1/(n : ℂ)) * ((k : ℂ)^(x+1) * ((-1 : ℂ)^k * Ring.choose x k)) *
        leftKernel x ((k : ℝ)/n) := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have hnk : (n : ℂ)+(k : ℂ) ≠ 0 := by exact_mod_cast (show n+k ≠ 0 by omega)
  have hp : (k : ℂ)^(x+1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hk')
  have hq : (n : ℂ)^(x+1) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hn')
  unfold leftKernel
  have hd := Complex.div_cpow_ofReal_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg n) (-x-1)
  simp only [Complex.ofReal_natCast] at hd
  rw [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_natCast, hd]
  rw [show -x-1 = -(x+1) by ring, Complex.cpow_neg, Complex.cpow_neg]
  field_simp

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology MeasureTheory

private theorem truncation_as_cpow (x:ℂ) (n:ℕ) (hn:n≠0) :
    truncation x n = (n:ℂ)^(x+1) *
      ∑k∈Finset.range (n+1), ((-1:ℂ)^k/((n:ℂ)+(k:ℂ)))*Ring.choose x k := by
  unfold truncation
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), Complex.natCast_log, mul_comm (x+1)]

private theorem truncation_riemann_decomposition (x:ℂ) (hx:x.re < -1) (n:ℕ) (hn:n≠0) :
    truncation x n = (n:ℂ)^x +
      ((n:ℝ)⁻¹:ℂ) * (∑ k:Fin n, ((k:ℂ)^(x+1)*((-1:ℂ)^(k:ℕ)*Ring.choose x k)) *
        leftKernel x ((k:ℝ)/n)) +
      ((n:ℝ)⁻¹:ℂ) * ((n:ℂ)^(x+1)*((-1:ℂ)^n*Ring.choose x n)) * leftKernel x 1 := by
  have hn0 : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn
  have he : -x-1≠0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hzero : leftKernel x 0=0 := by simp only [leftKernel,Complex.ofReal_zero,
    Complex.zero_cpow he,add_zero,div_one]
  have h0 : (n:ℂ)^(x+1)*(((-1:ℂ)^0/((n:ℂ)+(0:ℂ)))*Ring.choose x 0) = (n:ℂ)^x := by
    rw [Complex.cpow_add _ _ hn0,Complex.cpow_one]
    simp only [pow_zero,Ring.choose_zero_right,add_zero,mul_one]
    field_simp
  rw [truncation_as_cpow x n hn, Finset.mul_sum]
  let b : ℕ→ℂ := fun k => ((k:ℂ)^(x+1)*((-1:ℂ)^k*Ring.choose x k))*leftKernel x ((k:ℝ)/n)
  have hsum : (∑k∈Finset.range (n+1),
      (n:ℂ)^(x+1)*(((-1:ℂ)^k/((n:ℂ)+(k:ℂ)))*Ring.choose x k)) =
      (∑k∈Finset.range (n+1), (1/(n:ℂ))*b k) + (n:ℂ)^x := by
    have hs : (∑k∈Finset.range (n+1),
        ((1/(n:ℂ))*b k + if k=0 then (n:ℂ)^x else 0)) =
        (∑k∈Finset.range (n+1),(1/(n:ℂ))*b k)+(n:ℂ)^x := by simp [Finset.sum_add_distrib]
    rw [←hs]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hk0:k=0
    · subst k
      simp only [h0,b,hzero,Nat.cast_zero,zero_div,mul_zero,zero_add]
      simp
    · rw [ite_eq_right hk0,add_zero]
      simpa only [b,mul_assoc] using scaled_term_kernel x n k hn hk0
  rw [hsum,Finset.sum_range_succ,←Finset.mul_sum,←Fin.sum_univ_eq_sum_range]
  simp only [b,Complex.ofReal_natCast,one_div]
  have hr : ((n:ℝ)/(n:ℝ))=1 := div_self (Nat.cast_ne_zero.mpr hn)
  rw [hr]
  ring

private theorem truncation_left_integral_limit (x:ℂ) (hx:x.re < -1) :
    Tendsto (truncation x) atTop
      (𝓝 ((Complex.Gamma (-x))⁻¹ * ∫t in (0:ℝ)..1,leftKernel x t)) := by
  have hcoeff := coefficient_scaled_tendsto_all x
  have hr := weighted_left_riemann (left_kernel_continuous x hx) hcoeff
  have hnx := nat_cpow_tendsto_zero x (by linarith)
  have hni : Tendsto (fun n:ℕ => ((n:ℝ)⁻¹:ℂ)) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have he := (hni.mul hcoeff).mul_const (leftKernel x 1)
  have ht := (hnx.add hr).add he
  simp only [zero_add,zero_mul,add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact (truncation_riemann_decomposition x hx n hn).symm

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology

private def reciprocalGamma (z : ℂ) : ℂ := (Complex.Gamma z)⁻¹

private def hadamardCandidate (y : ℂ) : ℂ :=
  (Real.sqrt Real.pi : ℂ) / 2 * Complex.exp (y * Complex.log 2) *
    (reciprocalGamma (1-y/2) * deriv reciprocalGamma ((1-y)/2) -
      deriv reciprocalGamma (1-y/2) * reciprocalGamma ((1-y)/2))

private theorem reciprocal_gamma_differentiable : Differentiable ℂ reciprocalGamma :=
  Complex.differentiable_one_div_Gamma

private theorem reciprocal_gamma_shift (z : ℂ) :
    reciprocalGamma (z-1) = (z-1) * reciprocalGamma z := by
  simpa only [reciprocalGamma, sub_add_cancel] using
    Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z-1)

private theorem reciprocal_gamma_deriv_shift (z : ℂ) :
    deriv reciprocalGamma (z-1) = reciprocalGamma z + (z-1) * deriv reciprocalGamma z := by
  have hleft := (reciprocal_gamma_differentiable (z-1)).hasDerivAt.comp z
    ((hasDerivAt_id z).sub_const 1)
  have hright := ((hasDerivAt_id z).sub_const 1).mul
    (reciprocal_gamma_differentiable z).hasDerivAt
  have h := congrArg (fun f : ℂ → ℂ => deriv f z) (funext reciprocal_gamma_shift)
  change HasDerivAt (fun x => reciprocalGamma (x-1)) _ z at hleft
  change HasDerivAt (fun x => (x-1)*reciprocalGamma x) _ z at hright
  rw [hleft.deriv, hright.deriv] at h
  simpa only [mul_one, one_mul, id_eq] using h

private theorem reciprocal_gamma_deriv_zero : deriv reciprocalGamma 0 = 1 := by
  simpa [reciprocalGamma] using reciprocal_gamma_deriv_shift 1

private theorem reciprocal_gamma_duplication (y : ℂ) :
    Complex.exp (y * Complex.log 2) * reciprocalGamma (1-y/2) *
      reciprocalGamma ((1-y)/2) = reciprocalGamma (1-y) / (Real.sqrt Real.pi : ℂ) := by
  have h := congrArg Inv.inv (Complex.Gamma_mul_Gamma_add_half ((1-y)/2))
  have ha : (1-y)/2+1/2 = 1-y/2 := by ring
  have hb : 2*((1-y)/2) = 1-y := by ring
  rw [ha, hb, show (1:ℂ)-(1-y)=y by ring, Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)] at h
  simp only [mul_inv] at h
  dsimp only [reciprocalGamma]
  rw [mul_comm (Complex.log 2) y] at h
  have he := Complex.exp_ne_zero (y * Complex.log 2)
  calc
    _ = Complex.exp (y * Complex.log 2) *
        ((Complex.Gamma ((1-y)/2))⁻¹ * (Complex.Gamma (1-y/2))⁻¹) := by ring
    _ = _ := by rw [h]; field_simp

private theorem hadamard_candidate_differentiable : Differentiable ℂ hadamardCandidate := by
  have hr := reciprocal_gamma_differentiable
  have hd := hr.deriv
  unfold hadamardCandidate
  fun_prop

private theorem hadamard_candidate_shift (y : ℂ) :
    hadamardCandidate (y+1) = y * hadamardCandidate y + reciprocalGamma (1-y) := by
  have ha : 1-(y+1)/2 = (1-y)/2 := by ring
  have hb : (1-(y+1))/2 = (1-y/2)-1 := by ring
  have he : Complex.exp ((y+1) * Complex.log 2) = 2 * Complex.exp (y * Complex.log 2) := by
    rw [add_mul, Complex.exp_add, one_mul, Complex.exp_log (by norm_num : (2 : ℂ) ≠ 0)]
    ring
  have hp := reciprocal_gamma_duplication y
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  simp only [hadamardCandidate, ha, hb, reciprocal_gamma_shift,
    reciprocal_gamma_deriv_shift, he]
  have hn : 1-y/2 = (2-y)/2 := by ring
  simp only [hn] at hp ⊢
  field_simp at hp ⊢
  linear_combination 2*hp

private theorem hadamard_candidate_one : hadamardCandidate 1 = 1 := by
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  norm_num only [hadamardCandidate, reciprocal_gamma_deriv_zero, sub_self,
    one_div, one_mul, zero_div, reciprocalGamma, Complex.Gamma_zero, inv_zero, mul_zero, sub_zero]
  rw [Complex.exp_log (by norm_num : (2:ℂ) ≠ 0)]
  norm_num [Complex.Gamma_one_half_eq, Complex.ofReal_cpow Real.pi_pos.le]
  have he : (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1/2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_nonneg]
    norm_num
  rw [← he, mul_inv_cancel₀ hs]

private theorem hadamard_candidate_factorial (m : ℕ) :
    hadamardCandidate ((m : ℂ)+1) = (m.factorial : ℂ) := by
  induction m with
  | zero => simpa using hadamard_candidate_one
  | succ m ih =>
    have h := hadamard_candidate_shift ((m : ℂ)+1)
    have hz : reciprocalGamma (1-((m : ℂ)+1)) = 0 := by
      rw [show 1-((m:ℂ)+1) = -(m:ℂ) by ring]
      simp only [reciprocalGamma, Complex.Gamma_neg_nat_eq_zero, inv_zero]
    rw [hz, ih, add_zero] at h
    simpa [Nat.factorial_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_one, add_assoc] using h

private theorem reciprocal_gamma_deriv_regular (z : ℂ) (hz : ∀ m : ℕ, z ≠ -(m : ℂ)) :
    deriv reciprocalGamma z = -Complex.digamma z * reciprocalGamma z := by
  have h := ((Complex.differentiableAt_Gamma z hz).hasDerivAt.inv
    (Complex.Gamma_ne_zero hz)).deriv
  change deriv reciprocalGamma z = _ at h
  rw [h, Complex.digamma_def, logDeriv_apply]
  unfold reciprocalGamma
  ring

private theorem hadamard_candidate_quotient (y : ℂ) (hy : ∀ m : ℕ, y ≠ (m : ℂ)+1) :
    hadamardCandidate y =
      (Complex.digamma (1-y/2) - Complex.digamma ((1-y)/2)) /
        (2 * Complex.Gamma (1-y)) := by
  have ha : ∀ m : ℕ, 1-y/2 ≠ -(m : ℂ) := by
    intro m h
    apply hy (2*m+1)
    push_cast
    linear_combination -2*h
  have hb : ∀ m : ℕ, (1-y)/2 ≠ -(m : ℂ) := by
    intro m h
    apply hy (2*m)
    push_cast
    linear_combination -2*h
  have hp := reciprocal_gamma_duplication y
  have hs : (Real.sqrt Real.pi : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  rw [hadamardCandidate, reciprocal_gamma_deriv_regular _ ha,
    reciprocal_gamma_deriv_regular _ hb]
  dsimp only [reciprocalGamma] at hp ⊢
  have hn : 1-y/2 = (2-y)/2 := by ring
  simp only [hn] at hp ⊢
  field_simp at hp ⊢
  linear_combination (Complex.digamma ((2-y)/2) - Complex.digamma ((1-y)/2))*hp

private theorem hadamard_candidate_exists : ∃ H : ℂ → ℂ, IsHadamard H :=
  ⟨hadamardCandidate, hadamard_candidate_differentiable,
    hadamard_candidate_factorial, hadamard_candidate_quotient⟩

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology MeasureTheory
private def nielsenBeta (z : ℂ) : ℂ :=
  (Complex.digamma ((z+1)/2) - Complex.digamma (z/2))/2
private def betaIntegral (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..1, (t:ℂ)^(z-1)/(1+t)

private theorem nielsen_paired_hasSum (z : ℂ)
    (ha : z/2 ∈ Complex.integerComplement)
    (hb : (z+1)/2 ∈ Complex.integerComplement) :
    HasSum (fun k : ℕ => 1/(z+2*(k:ℂ)) - 1/(z+2*(k:ℂ)+1)) (nielsenBeta z) := by
  have hs := (Zeta23.DigammaSeries.hasSum_digamma_series hb).sub
    (Zeta23.DigammaSeries.hasSum_digamma_series ha)
  have ht := hs.div_const 2
  rw [← hasSum_nat_add_iff' 1]
  convert ht using 1
  · ext k
    push_cast
    rw [show z/2+(k:ℂ)+1=(z+2*k+2)/2 by ring,
      show (z+1)/2+(k:ℂ)+1=(z+2*k+3)/2 by ring]
    simp only [one_div_div]
    ring_nf
  · unfold nielsenBeta
    simp only [Finset.sum_range_one, Nat.cast_zero, mul_zero, add_zero]
    rw [one_div_div, one_div_div]
    ring

private theorem paired_integral (z : ℂ) (hz : 1 < z.re) (k : ℕ) :
    (∫ t in (0:ℝ)..1, ((t:ℂ)^(z+2*(k:ℂ)-1) - (t:ℂ)^(z+2*(k:ℂ)))) =
      1/(z+2*(k:ℂ))-1/(z+2*(k:ℂ)+1) := by
  have h1 : -1 < (z+2*(k:ℂ)-1).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    norm_num
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  have h2 : -1 < (z+2*(k:ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
    norm_num
    linarith [Nat.cast_nonneg (α:=ℝ) k]
  rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_cpow' h1)
    (intervalIntegral.intervalIntegrable_cpow' h2), integral_cpow (Or.inl h1), integral_cpow (Or.inl h2)]
  have he1 : z+2*(k:ℂ)-1+1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α:=ℝ) k]
  have he2 : z+2*(k:ℂ)+1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [Nat.cast_nonneg (α:=ℝ) k]
  have he0 : z+2*(k:ℂ) ≠ 0 := by simpa only [sub_add_cancel] using he1
  simp only [Complex.ofReal_one, Complex.ofReal_zero, Complex.one_cpow, Complex.zero_cpow he0,
    Complex.zero_cpow he2, sub_zero, sub_add_cancel]

private theorem paired_pointwise (z : ℂ) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    (t:ℂ)^(z+2*(k:ℂ)-1)-(t:ℂ)^(z+2*(k:ℂ)) =
      (t:ℂ)^(z-1) * ((t:ℂ)^2)^k * (1-(t:ℂ)) := by
  have ht0 : (t:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  rw [show z+2*(k:ℂ)-1=(z-1)+(2*k:ℕ) by push_cast; ring,
    show z+2*(k:ℂ)=(z-1)+(2*k:ℕ)+1 by push_cast; ring,
    Complex.cpow_add _ _ ht0, Complex.cpow_add _ _ ht0,
    Complex.cpow_add _ _ ht0, Complex.cpow_natCast, Complex.cpow_one]
  rw [pow_mul]
  ring

private theorem paired_integrals_hasSum (z : ℂ) (hz : 1 < z.re) :
    HasSum (fun k:ℕ => 1/(z+2*(k:ℂ))-1/(z+2*(k:ℂ)+1)) (betaIntegral z) := by
  let F : ℕ → ℝ → ℂ := fun k t =>
    (t:ℂ)^(z+2*(k:ℂ)-1)-(t:ℂ)^(z+2*(k:ℂ))
  let bound : ℕ → ℝ → ℝ := fun k t => (t^2)^k*(1-t)
  have hgeom {t:ℝ} (ht:0<t) (ht1:t<1) :
      HasSum (fun k:ℕ => bound k t) (1/(1+t)) := by
    have hnorm : ‖t^2‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg t)]; nlinarith
    have h := (hasSum_geometric_of_norm_lt_one hnorm).mul_right (1-t)
    convert h using 1
    have hs : 1-t^2 ≠ 0 := by nlinarith
    have hp : 1+t ≠ 0 := by linarith
    field_simp [hs, hp]
    ring
  have hpoint {t:ℝ} (ht:0<t) (ht1:t<1) :
      HasSum (fun k:ℕ => F k t) ((t:ℂ)^(z-1)/(1+t)) := by
    have hnorm : ‖(t:ℂ)^2‖ < 1 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
      nlinarith
    have h := ((hasSum_geometric_of_norm_lt_one hnorm).mul_left ((t:ℂ)^(z-1))).mul_right (1-(t:ℂ))
    convert h using 1
    · ext k; exact paired_pointwise z ht k
    · have hne : 1-(t:ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1:ℝ)-t≠0)
      have hp : 1+(t:ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1:ℝ)+t≠0)
      have hs : 1-(t:ℂ)^2 ≠ 0 := by exact_mod_cast (by nlinarith : (1:ℝ)-t^2≠0)
      field_simp
      ring
  have hbound {t:ℝ} (ht:0<t) (ht1:t<1) (k:ℕ) : ‖F k t‖ ≤ bound k t := by
    rw [show F k t = (t:ℂ)^(z-1)*((t:ℂ)^2)^k*(1-(t:ℂ)) from paired_pointwise z ht k,
      norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, norm_pow, norm_pow]
    have hnorm : ‖(t:ℂ)‖ = t := by simp [abs_of_pos ht]
    have hsub : ‖1-(t:ℂ)‖ = 1-t := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith)]
    rw [hnorm, hsub]
    have hpow : t^(z-1).re ≤ 1 := by
      apply Real.rpow_le_one ht.le ht1.le
      simpa only [Complex.sub_re, Complex.one_re] using (sub_pos.mpr hz).le
    dsimp [bound]
    simpa only [one_mul, Complex.sub_re, Complex.one_re] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpow (show (0:ℝ) ≤ (t^2)^k by positivity)) (show 0 ≤ 1-t by linarith)
  have hd := intervalIntegral.hasSum_integral_of_dominated_convergence bound
    (fun k => by
      have h1 : 0 < (z+2*(k:ℂ)-1).re := by simp; linarith [Nat.cast_nonneg (α:=ℝ) k]
      have h2 : 0 < (z+2*(k:ℂ)).re := by simp; linarith [Nat.cast_nonneg (α:=ℝ) k]
      exact ((Complex.continuous_ofReal_cpow_const h1).sub
        (Complex.continuous_ofReal_cpow_const h2)).aestronglyMeasurable)
    (fun k => by
      filter_upwards [volume.ae_ne (1:ℝ)] with t ht hmem
      rw [Set.uIoc_of_le zero_le_one] at hmem
      exact hbound hmem.1 (lt_of_le_of_ne hmem.2 ht) k)
    (by
      filter_upwards [volume.ae_ne (1:ℝ)] with t ht hmem
      rw [Set.uIoc_of_le zero_le_one] at hmem
      exact (hgeom hmem.1 (lt_of_le_of_ne hmem.2 ht)).summable)
    (by
      have hc : ContinuousOn (fun t:ℝ => 1/(1+t)) (Set.Icc 0 1) :=
        ContinuousOn.div continuousOn_const (by fun_prop) (by intro t ht; linarith [ht.1])
      apply IntervalIntegrable.congr_ae (ContinuousOn.intervalIntegrable_of_Icc zero_le_one hc)
      change ∀ᵐt ∂volume.restrict (Set.uIoc 0 1), (1/(1+t):ℝ)=∑'n,bound n t
      rw [ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [volume.ae_ne (1:ℝ)] with t ht hmem
      rw [Set.uIoc_of_le zero_le_one] at hmem
      exact (hgeom hmem.1 (lt_of_le_of_ne hmem.2 ht)).tsum_eq.symm)
    (by
      filter_upwards [volume.ae_ne (1:ℝ)] with t ht hmem
      rw [Set.uIoc_of_le zero_le_one] at hmem
      exact hpoint hmem.1 (lt_of_le_of_ne hmem.2 ht))
  simpa only [F, Pi.sub_apply, paired_integral z hz, betaIntegral] using hd

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology MeasureTheory

private theorem beta_kernel_integrable (z:ℂ) (hz:0<z.re) :
    IntervalIntegrable (fun t:ℝ => (t:ℂ)^(z-1)/(1+t)) volume 0 1 := by
  have hc : ContinuousOn (fun t:ℝ => (1+(t:ℂ))⁻¹) (Set.uIcc 0 1) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht h
    have := congrArg Complex.re h
    rw [Set.uIcc_of_le zero_le_one] at ht
    simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.zero_re] at this
    linarith [ht.1]
  have hi := (intervalIntegral.intervalIntegrable_cpow' (r:=z-1) (by simp; linarith)).mul_continuousOn hc
  simpa only [div_eq_mul_inv] using hi

private theorem beta_integral_shift (z:ℂ) (hz:0<z.re) :
    betaIntegral (z+1)+betaIntegral z = 1/z := by
  have hz1 : 0<(z+1).re := by simp; linarith
  unfold betaIntegral
  rw [← intervalIntegral.integral_add (beta_kernel_integrable (z+1) hz1) (beta_kernel_integrable z hz)]
  calc
    _ = ∫t in (0:ℝ)..1,(t:ℂ)^(z-1) := by
      apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
      intro t ht
      have ht0 : (t:ℂ)≠0 := Complex.ofReal_ne_zero.mpr ht.1.ne'
      have hd : 1+(t:ℂ)≠0 := by
        intro h; have := congrArg Complex.re h; simp at this; linarith [ht.1]
      change (t:ℂ)^(z+1-1)/(1+t)+(t:ℂ)^(z-1)/(1+t)=(t:ℂ)^(z-1)
      rw [show z+1-1=(z-1)+1 by ring,Complex.cpow_add _ _ ht0,Complex.cpow_one]
      field_simp
      ring
    _ = _ := by
      have he : z≠0 := Complex.ne_zero_of_re_pos hz
      rw [integral_cpow (Or.inl (by simp; linarith : -1 < (z-1).re))]
      simp only [sub_add_cancel,Complex.ofReal_one,Complex.ofReal_zero,Complex.one_cpow,
        Complex.zero_cpow he,sub_zero]

private theorem nielsen_beta_shift (z:ℂ) (hz:0<z.re) :
    nielsenBeta (z+1)+nielsenBeta z=1/z := by
  have ha : ∀m:ℕ,z/2≠-(m:ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [Nat.cast_nonneg (α:=ℝ) m]
  unfold nielsenBeta
  rw [show (z+1+1)/2=z/2+1 by ring,Complex.digamma_apply_add_one _ ha]
  simp only [inv_div]
  ring

private theorem beta_integral_one : betaIntegral 1 = Complex.log 2 := by
  unfold betaIntegral
  simp only [sub_self,Complex.cpow_zero,one_div]
  have he : (fun t:ℝ => (1+(t:ℂ))⁻¹) = fun t:ℝ => (((1+t)⁻¹:ℝ):ℂ) := by
    ext t
    push_cast
    rfl
  rw [he,intervalIntegral.integral_ofReal,intervalIntegral.integral_comp_add_left (fun t:ℝ=>t⁻¹) 1]
  norm_num [integral_inv_of_pos,←Complex.natCast_log]

private theorem nielsen_beta_one : nielsenBeta 1 = Complex.log 2 := by
  norm_num [nielsenBeta,Complex.digamma_one,Complex.digamma_one_half]
  ring

private theorem beta_integral_nat (m:ℕ) : betaIntegral ((m:ℂ)+1) = nielsenBeta ((m:ℂ)+1) := by
  induction m with
  | zero => simpa only [Nat.cast_zero,zero_add] using beta_integral_one.trans nielsen_beta_one.symm
  | succ m ih =>
    have hz : 0<((m:ℂ)+1).re := by simp; positivity
    have hi := beta_integral_shift ((m:ℂ)+1) hz
    have hb := nielsen_beta_shift ((m:ℂ)+1) hz
    rw [ih] at hi
    have h := add_right_cancel (hi.trans hb.symm)
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc] using h

private theorem beta_integral_identification (z:ℂ) (hz:1<z.re) : betaIntegral z=nielsenBeta z := by
  by_cases hi : ∃m:ℤ,z=(m:ℂ)
  · obtain ⟨m,rfl⟩ := hi
    have hm : (0:ℤ)<m := by exact_mod_cast (show (0:ℝ)<(m:ℝ) by simpa using lt_trans zero_lt_one hz)
    obtain ⟨k,hk⟩ := Int.eq_ofNat_of_zero_le hm.le
    subst m
    have hk0 : k≠0 := by intro h; subst k; norm_num at hz
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    simpa using beta_integral_nat l
  · have ha : z/2∈Complex.integerComplement := by
      intro h
      obtain ⟨m,hm⟩ := h
      apply hi
      refine ⟨2*m,?_⟩
      push_cast
      linear_combination -2*hm
    have hb : (z+1)/2∈Complex.integerComplement := by
      intro h
      obtain ⟨m,hm⟩ := h
      apply hi
      refine ⟨2*m-1,?_⟩
      push_cast
      linear_combination -2*hm
    exact (paired_integrals_hasSum z hz).unique (nielsen_paired_hasSum z ha hb)

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology

private theorem hadamard_unique {H J : ℂ → ℂ} (hH : IsHadamard H) (hJ : IsHadamard J) : H=J := by
  funext y
  by_cases hy : ∃ m:ℕ, y=(m:ℂ)+1
  · obtain ⟨m,rfl⟩ := hy
    rw [hH.2.1,hJ.2.1]
  · have hn : ∀m:ℕ,y≠(m:ℂ)+1 := by simpa only [not_exists] using hy
    rw [hH.2.2 y hn,hJ.2.2 y hn]

private theorem truncation_shift_identity (x:ℂ) (n:ℕ) (hn:n≠0) :
    ((n:ℂ)+x+1)*truncation (x+1) n =
      (n:ℂ)*((x+1)*truncation x n + (n:ℂ)^(x+1)*((-1:ℂ)^n*Ring.choose x n)) := by
  rw [truncation_as_cpow _ _ hn,truncation_as_cpow _ _ hn,
    Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn),Complex.cpow_one]
  have h := finite_sum_shift x n hn
  linear_combination (n:ℂ)^(x+1)*(n:ℂ)*h

private theorem truncation_limit_step (x:ℂ)
    (hx:Tendsto (truncation x) atTop (𝓝 (hadamardCandidate (x+1)))) :
    Tendsto (truncation (x+1)) atTop (𝓝 (hadamardCandidate (x+1+1))) := by
  have ht := (tendsto_natCast_div_add_atTop (x+1)).mul
    ((hx.const_mul (x+1)).add (coefficient_scaled_tendsto_all x))
  simp only [one_mul] at ht
  rw [hadamard_candidate_shift (x+1)]
  have he : reciprocalGamma (1-(x+1)) = (Complex.Gamma (-x))⁻¹ := by
    unfold reciprocalGamma
    congr 2
    ring
  rw [he]
  apply ht.congr'
  have hden : ∀ᶠ n:ℕ in atTop, (n:ℂ)+(x+1)≠0 := by
    filter_upwards [eventually_gt_atTop ⌈‖x+1‖⌉₊] with n hn
    intro h
    have heq : (n:ℂ)=-(x+1) := eq_neg_of_add_eq_zero_left h
    have hnorm : (n:ℝ)=‖x+1‖ := by simpa only [Complex.norm_natCast, norm_neg] using congrArg norm heq
    have hh : (⌈‖x+1‖⌉₊:ℝ)<n := Nat.cast_lt.mpr hn
    linarith [Nat.le_ceil ‖x+1‖]
  filter_upwards [eventually_ne_atTop 0,hden] with n hn hd
  change (n:ℂ)/((n:ℂ)+(x+1))*((x+1)*truncation x n+
    (n:ℂ)^(x+1)*((-1:ℂ)^n*Ring.choose x n)) = truncation (x+1) n
  apply mul_left_cancel₀ hd
  have hs := truncation_shift_identity x n hn
  calc
    _ = (n:ℂ)*((x+1)*truncation x n+(n:ℂ)^(x+1)*((-1:ℂ)^n*Ring.choose x n)) := by field_simp
    _ = _ := by simpa only [add_assoc] using hs.symm

private theorem truncation_global_of_left
    (hl : ∀x:ℂ,x.re < -1 → Tendsto (truncation x) atTop (𝓝 (hadamardCandidate (x+1)))) :
    ∀x:ℂ,Tendsto (truncation x) atTop (𝓝 (hadamardCandidate (x+1))) := by
  intro x
  obtain ⟨N,hN⟩ := exists_nat_gt (x.re+1)
  have hb : (x-(N:ℂ)).re < -1 := by simp only [Complex.sub_re,Complex.natCast_re]; linarith
  have hi : ∀k:ℕ,Tendsto (truncation (x-(N:ℂ)+(k:ℂ))) atTop
      (𝓝 (hadamardCandidate (x-(N:ℂ)+(k:ℂ)+1))) := by
    intro k
    induction k with
    | zero => simpa only [Nat.cast_zero,add_zero] using hl (x-N) hb
    | succ k ih =>
      simpa only [Nat.cast_add,Nat.cast_one,←add_assoc] using
        truncation_limit_step (x-N+k) ih
  simpa only [sub_add_cancel] using hi N

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit

namespace D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
open Filter Topology MeasureTheory

private theorem candidate_left_limit (x:ℂ) (hx:x.re < -1) :
    Tendsto (truncation x) atTop (𝓝 (hadamardCandidate (x+1))) := by
  have ht := truncation_left_integral_limit x hx
  have hz : 1<(-x).re := by simp only [Complex.neg_re]; linarith
  have he : (∫t in (0:ℝ)..1,leftKernel x t)=betaIntegral (-x) := rfl
  rw [he,beta_integral_identification (-x) hz] at ht
  have hy : ∀m:ℕ,x+1≠(m:ℂ)+1 := by
    intro m hm
    have := congrArg Complex.re hm
    simp only [Complex.add_re,Complex.one_re,Complex.natCast_re] at this
    linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hh := hadamard_candidate_quotient (x+1) hy
  rw [show 1-(x+1)/2=((-x)+1)/2 by ring,
    show (1-(x+1))/2=(-x)/2 by ring] at hh
  have hh' : hadamardCandidate (x+1)=(Complex.Gamma (-x))⁻¹*nielsenBeta (-x) := by
    rw [hh]
    unfold nielsenBeta
    rw [show 1-(x+1)=-x by ring]
    ring
  rwa [←hh'] at ht

theorem result : claim := by
  refine ⟨hadamard_candidate_exists,?_⟩
  intro H hH x
  have hc : IsHadamard hadamardCandidate := ⟨hadamard_candidate_differentiable,
    hadamard_candidate_factorial,hadamard_candidate_quotient⟩
  have he := hadamard_unique hH hc
  subst H
  exact truncation_global_of_left candidate_left_limit x

end D5.S3.Weil.ZetaGamma.HadamardTruncatedBinomialLimit
