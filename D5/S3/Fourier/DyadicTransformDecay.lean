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

#print axioms sinc_product_decay_bound

end

end D5.S3.Fourier.DyadicTransformDecay
