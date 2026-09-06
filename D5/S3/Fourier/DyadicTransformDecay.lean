/- GID: D5/S3/Fourier/DyadicTransformDecay
   generality: I
   mirror-B: D5/B/S3/Fourier/DyadicTransformDecay
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every polynomially weighted real-axis dyadic density transform is integrable. -/

/- Library-search audit trail (2026-09-07, repeated by continuation worker):
   1. D5: searched `sinc.*decay`, `integrable.*sinc`,
      `density_transform_decay`, and `sinc_product_decay`. Only this
      unverified draft matched; no existing decay theorem was found. Reuse
      InfiniteSincProduct.dyadic_uniform_convolution_product_ne_zero_off_real
      for product convergence and
      DyadicConvolutionDensity.dyadicConvolutionDensity_fourierLaplace
      for the actual density transform. Both imported modules have generality I.
   2. Pinned Mathlib v4.33.0: searched sinc bounds, finite-prefix product
      bounds, norm_tprod, integrable inverse powers, and measurable limits.
      Hits reused below: Real.abs_sinc_le_one, Real.abs_sin_le_one,
      Finset.prod_le_prod_of_subset_of_le_one, HasProd.tendsto_prod_nat,
      aestronglyMeasurable_of_tendsto_ae, and integrable_inv_one_add_sq.
      No theorem for arbitrary-order decay of this sinc product was found.
   3. GitHub via NyxID observer proxy: repository queries
      `sinc language:Lean`, `"infinite convolution" Lean`, and
      `Fabius language:Lean`. The latter two returned zero repositories;
      the first returned only iank/sincos_lut, whose inspected README is
      about a finite sine/cosine lookup table, not infinite sinc products.
      Global code query `"sinc" "decay" language:Lean` returned HTTP 401.
      Anonymous public routes returned HTTP 404; the proxy route worked.
      Service discovery reports the GitHub OAuth services failed/expired.
      Third-party code-level completeness is ASSUMED-UNVERIFIED.
   4. Local proof: retain any finite prefix, bound all remaining real-axis
      factors by one, and pass to the product limit. The preregistered
      escape witness is sinc_product_decay_bound; weighted integrability
      consumes its order k+2 estimate. Fourier inversion and smoothness
      are not claimed by this module.
-/

import D5.S3.Fourier.InfiniteSincProduct
import D5.S3.Fourier.DyadicConvolutionDensity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace D5.S3.Fourier.DyadicTransformDecay

open Filter MeasureTheory Set Topology
open D5.S3.Fourier.InfiniteSincProduct
open D5.S3.Fourier.DyadicConvolutionDensity

noncomputable section

private theorem complexSinc_ofReal (x : ℝ) : complexSinc (x : ℂ) = (Real.sinc x : ℂ) := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [complexSinc_of_ne_zero (Complex.ofReal_ne_zero.mpr hx), Real.sinc_of_ne_zero hx]
    simp

private theorem real_factor_norm_le_one (a xi : ℝ) :
    ‖complexSinc ((a : ℂ) * (xi : ℂ))‖ ≤ 1 := by
  rw [← Complex.ofReal_mul, complexSinc_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_sinc_le_one _

private theorem real_factor_norm_le_inv {a xi : ℝ} (ha : 0 < a) (hxi : xi ≠ 0) :
    ‖complexSinc ((a : ℂ) * (xi : ℂ))‖ ≤ a⁻¹ / |xi| := by
  rw [← Complex.ofReal_mul, complexSinc_ofReal, Complex.norm_real, Real.norm_eq_abs,
    Real.sinc_of_ne_zero (mul_ne_zero ha.ne' hxi), abs_div, abs_mul, abs_of_pos ha]
  calc
    |Real.sin (a * xi)| / (a * |xi|) ≤ 1 / (a * |xi|) := by
      exact div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by positivity)
    _ = a⁻¹ / |xi| := by ring

private theorem product_norm_le_prefix (ell : ℝ) (hell : 0 < ell) (xi : ℝ) (k : ℕ) :
    ‖∏' j, complexSinc ((dyadicHalfWidth ell j : ℝ) * (xi : ℂ))‖ ≤
      ∏ j ∈ Finset.range k, ‖complexSinc ((dyadicHalfWidth ell j : ℝ) * (xi : ℂ))‖ := by
  have hd := dyadic_uniform_convolution_product_ne_zero_off_real ell hell
  have hp := (hd.2.2.1 {(xi : ℂ)} isCompact_singleton).hasProd (mem_singleton _)
  apply le_of_tendsto hp.tendsto_prod_nat.norm
  filter_upwards [eventually_ge_atTop k] with n hn
  rw [norm_prod]
  exact Finset.prod_le_prod_of_subset_of_le_one (Finset.range_mono hn)
    (fun j _ => norm_nonneg _) (fun j _ _ => real_factor_norm_le_one _ _)

/-- Retaining an arbitrary finite prefix gives every inverse-power tail bound. -/
theorem sinc_product_decay_bound (ell : ℝ) (hell : 0 < ell) (k : ℕ) :
    ∃ C > 0, ∀ xi : ℝ, 1 ≤ |xi| →
      ‖densityFourierLaplace (dyadicConvolutionDensity ell) (xi : ℂ)‖ ≤ C / |xi| ^ k := by
  let C : ℝ := ∏ j ∈ Finset.range k, (dyadicHalfWidth ell j)⁻¹
  have ha (j : ℕ) : 0 < dyadicHalfWidth ell j := by
    unfold dyadicHalfWidth
    positivity
  refine ⟨C, Finset.prod_pos (fun j _ => inv_pos.mpr (ha j)), ?_⟩
  intro xi hxi
  have hxi0 : xi ≠ 0 := by intro h; norm_num [h] at hxi
  rw [dyadicConvolutionDensity_fourierLaplace ell hell]
  calc
    ‖∏' j, complexSinc ((dyadicHalfWidth ell j : ℝ) * (xi : ℂ))‖ ≤
        ∏ j ∈ Finset.range k,
          ‖complexSinc ((dyadicHalfWidth ell j : ℝ) * (xi : ℂ))‖ :=
      product_norm_le_prefix ell hell xi k
    _ ≤ ∏ j ∈ Finset.range k, (dyadicHalfWidth ell j)⁻¹ / |xi| :=
      Finset.prod_le_prod (fun j _ => norm_nonneg _)
        (fun j _ => real_factor_norm_le_inv (ha j) hxi0)
    _ = C / |xi| ^ k := by simp [C, Finset.prod_div_distrib]

private theorem weighted_transform_bounded (ell : ℝ) (hell : 0 < ell) (k : ℕ) :
    ∃ C > 0, ∀ xi : ℝ,
      |xi| ^ k * ‖densityFourierLaplace (dyadicConvolutionDensity ell) (xi : ℂ)‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := sinc_product_decay_bound ell hell k
  refine ⟨1 + C, by positivity, ?_⟩
  intro xi
  by_cases hxi : 1 ≤ |xi|
  · have hpos : 0 < |xi| ^ k := pow_pos (lt_of_lt_of_le zero_lt_one hxi) _
    have hb := (le_div_iff₀ hpos).mp (hbound xi hxi)
    nlinarith
  · have hp : |xi| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg xi) (le_of_not_ge hxi)
    have ht : ‖densityFourierLaplace (dyadicConvolutionDensity ell) (xi : ℂ)‖ ≤ 1 := by
      rw [dyadicConvolutionDensity_fourierLaplace ell hell]
      simpa only [Finset.range_zero, Finset.prod_empty] using
        product_norm_le_prefix ell hell xi 0
    have hb := mul_le_mul hp ht (norm_nonneg _) zero_le_one
    nlinarith

private theorem transform_aestronglyMeasurable (ell : ℝ) (hell : 0 < ell) :
    AEStronglyMeasurable
      (fun xi : ℝ => densityFourierLaplace (dyadicConvolutionDensity ell) (xi : ℂ)) := by
  simp_rw [dyadicConvolutionDensity_fourierLaplace ell hell]
  apply aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun (n : ℕ) (xi : ℝ) => ∏ j ∈ Finset.range n,
      complexSinc ((dyadicHalfWidth ell j : ℂ) * (xi : ℂ)))
  · intro n
    apply Continuous.aestronglyMeasurable
    apply continuous_finsetProd
    intro j _
    exact continuous_complexSinc.comp (continuous_const.mul Complex.continuous_ofReal)
  · apply Eventually.of_forall
    intro xi
    have hd := dyadic_uniform_convolution_product_ne_zero_off_real ell hell
    exact ((hd.2.2.1 {(xi : ℂ)} isCompact_singleton).hasProd
      (mem_singleton _)).tendsto_prod_nat

/-- Every polynomially weighted real-axis density transform has finite absolute integral. -/
theorem dyadic_density_transform_decay (ell : ℝ) (hell : 0 < ell) (k : ℕ) :
    Integrable (fun xi : ℝ =>
      |xi| ^ k * ‖densityFourierLaplace (dyadicConvolutionDensity ell) (xi : ℂ)‖) := by
  obtain ⟨C, _, hC⟩ := weighted_transform_bounded ell hell k
  obtain ⟨D, _, hD⟩ := weighted_transform_bounded ell hell (k + 2)
  have hm := (continuous_abs.pow k).aestronglyMeasurable.mul
    (transform_aestronglyMeasurable ell hell).norm
  refine (integrable_inv_one_add_sq.const_mul (C + D)).mono' hm
    (Eventually.of_forall fun xi => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  calc
    (|xi| ^ k * ‖densityFourierLaplace (dyadicConvolutionDensity ell) (xi : ℂ)‖) *
        (1 + xi ^ 2) =
      |xi| ^ k * ‖densityFourierLaplace (dyadicConvolutionDensity ell) (xi : ℂ)‖ +
        |xi| ^ (k + 2) *
          ‖densityFourierLaplace (dyadicConvolutionDensity ell) (xi : ℂ)‖ := by
            rw [pow_add, sq_abs]
            ring
    _ ≤ C + D := add_le_add (hC xi) (hD xi)

#print axioms sinc_product_decay_bound
#print axioms dyadic_density_transform_decay

end

end D5.S3.Fourier.DyadicTransformDecay
