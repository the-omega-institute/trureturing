/- GID: D5/S3/Weil/TestFunctions/QuantitativeEvenSeed
   generality: G
   mirror-B: D5/B/S3/Weil/TestFunctions/QuantitativeEvenSeed
   mirror-E: none(waiver:explicit-nonvanishing-seed-radius)
   anchors: []
   digest: Replace an unspecified Fourier nonvanishing neighborhood by the explicit radius 1/(4(R+1)) and a uniform transform lower bound one half. -/

import D5.S3.Weil.TestFunctions.FinitePaleyWienerInterpolation

/-!
# Quantitative seed nonvanishing

A normalized nonnegative even bump of radius h satisfies
|FT(psi)(z)-1| <= 2h|z| whenever h|z| <= 1. This follows by integrating
Complex.norm_exp_sub_one_le against the normalized bump.

For h=1/(4(R+1)) and |z|<=R, the transform norm is at least 1/2.
The result supplies an explicit normalization denominator for the existing
Lagrange interpolation method. It does not bound the higher derivative
seminorms of the bump, and does not claim executable evaluation of real
integrals without separately certified numerical enclosures.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Weil.TestFunctions.QuantitativeEvenSeed

open Set MeasureTheory Metric
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.Convention
open D5.S3.Weil.FourierLaplace
open scoped ContDiff

/-- Explicit positive-radius bump data, independent of a nonvanishing choice. -/
def radiusBump (h : ℝ) (hh : 0 < h) : ContDiffBump (0 : ℝ) where
  rIn := h / 2
  rOut := h
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

/-- A normalized nonnegative even bump in the actual Weil test bundle. -/
def normalizedEvenSeed (h : ℝ) (hh : 0 < h) : WeilTestFunction where
  toFun x := ((radiusBump h hh).normed volume x : ℂ)
  contDiff' := Complex.ofRealCLM.contDiff.comp (radiusBump h hh).contDiff_normed
  hasCompactSupport' :=
    (radiusBump h hh).hasCompactSupport_normed.comp_left (by simp)
  even' x := by exact_mod_cast (radiusBump h hh).normed_neg (μ := volume) x

/-- The seed has unit integral. -/
theorem normalizedEvenSeed_integral (h : ℝ) (hh : 0 < h) :
    (∫ x : ℝ, normalizedEvenSeed h hh x) = 1 := by
  change (∫ x : ℝ, ((radiusBump h hh).normed volume x : ℂ)) = 1
  rw [integral_complex_ofReal]
  exact_mod_cast (radiusBump h hh).integral_normed (μ := volume)

/-- Positivity also makes the L1 norm exactly one. -/
theorem normalizedEvenSeed_norm_integral (h : ℝ) (hh : 0 < h) :
    (∫ x : ℝ, ‖normalizedEvenSeed h hh x‖) = 1 := by
  have hnorm (x : ℝ) : ‖normalizedEvenSeed h hh x‖ =
      (radiusBump h hh).normed volume x := by
    change ‖((radiusBump h hh).normed volume x : ℂ)‖ = _
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((radiusBump h hh).nonneg_normed x)]
  simp_rw [hnorm]
  exact (radiusBump h hh).integral_normed

/-- The radius is a bound on topological support, including its boundary. -/
theorem normalizedEvenSeed_tsupport (h : ℝ) (hh : 0 < h) :
    tsupport (normalizedEvenSeed h hh : ℝ → ℂ) ⊆ Icc (-h) h := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  have hn : (radiusBump h hh).normed volume x ≠ 0 := by
    intro hz
    exact hx (by change ((radiusBump h hh).normed volume x : ℂ) = 0; rw [hz]; rfl)
  have hb : x ∈ Metric.ball (0 : ℝ) h := by
    have hx' : x ∈ Function.support ((radiusBump h hh).normed volume) := hn
    rwa [(radiusBump h hh).support_normed_eq] at hx'
  have habs : |x| < h := by simpa only [mem_ball, Real.dist_eq, sub_zero] using hb
  exact abs_le.mp habs.le

/-- A finite support and unit mass give an explicit transform perturbation. -/
theorem fourierLaplace_sub_one_norm_le
    (psi : WeilTestFunction) (h : ℝ) (hh : 0 ≤ h)
    (hsupport : tsupport (psi : ℝ → ℂ) ⊆ Icc (-h) h)
    (hmass : (∫ x : ℝ, psi x) = 1)
    (hnorm : (∫ x : ℝ, ‖psi x‖) = 1)
    (z : ℂ) (hz : h * ‖z‖ ≤ 1) :
    ‖fourierLaplace psi z - 1‖ ≤ 2 * h * ‖z‖ := by
  have hkernel : Continuous (fun x : ℝ => fourierKernel z x) := by
    unfold fourierKernel
    fun_prop
  have hprod : Integrable (fun x : ℝ => fourierKernel z x * psi x) :=
    (hkernel.mul psi.continuous).integrable_of_hasCompactSupport psi.hasCompactSupport.mul_left
  have hdiff : Integrable (fun x : ℝ => (fourierKernel z x - 1) * psi x) :=
    ((hkernel.sub continuous_const).mul psi.continuous).integrable_of_hasCompactSupport
      psi.hasCompactSupport.mul_left
  have heq : fourierLaplace psi z - 1 =
      ∫ x : ℝ, (fourierKernel z x - 1) * psi x := by
    rw [fourierLaplace_apply, ← hmass, ← integral_sub hprod psi.integrable]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have hpoint (x : ℝ) : ‖(fourierKernel z x - 1) * psi x‖ ≤
      (2 * h * ‖z‖) * ‖psi x‖ := by
    by_cases hx : psi x = 0
    · simp [hx]
    · have hxh := hsupport (subset_tsupport (psi : ℝ → ℂ) hx)
      have hxa : |x| ≤ h := abs_le.mpr hxh
      have hexpnorm : ‖-Complex.I * z * (x : ℂ)‖ = ‖z‖ * |x| := by
        simp [norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
      have hsmall : ‖-Complex.I * z * (x : ℂ)‖ ≤ 1 := by
        rw [hexpnorm]
        exact (mul_le_mul_of_nonneg_left hxa (norm_nonneg _)).trans (by nlinarith [hz])
      have hk := Complex.norm_exp_sub_one_le hsmall
      rw [hexpnorm] at hk
      have hk' : ‖fourierKernel z x - 1‖ ≤ 2 * h * ‖z‖ := by
        unfold fourierKernel
        nlinarith [mul_le_mul_of_nonneg_left hxa (norm_nonneg z)]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hk' (norm_nonneg _)
  rw [heq]
  calc
    _ ≤ ∫ x : ℝ, ‖(fourierKernel z x - 1) * psi x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, (2 * h * ‖z‖) * ‖psi x‖ :=
      integral_mono hdiff.norm (psi.integrable.norm.const_mul _) hpoint
    _ = 2 * h * ‖z‖ := by rw [integral_const_mul, hnorm, mul_one]

/-- A rational upper bound R gives this explicit rational support radius. -/
def quantitativeSeedRadius (R : ℝ) : ℝ := 1 / (4 * (R + 1))

/-- No neighborhood search is involved in the radius selection. -/
theorem quantitativeSeedRadius_pos (R : ℝ) (hR : 0 ≤ R) :
    0 < quantitativeSeedRadius R := by unfold quantitativeSeedRadius; positivity

/-- Uniform denominator control for every interpolation node in the radius-R ball. -/
theorem quantitativeEvenSeed_transform_lower
    (R : ℝ) (hR : 0 ≤ R) (z : ℂ) (hz : ‖z‖ ≤ R) :
    (1 / 2 : ℝ) ≤ ‖fourierLaplace
      (normalizedEvenSeed (quantitativeSeedRadius R) (quantitativeSeedRadius_pos R hR)) z‖ := by
  let h := quantitativeSeedRadius R
  have hh : 0 < h := quantitativeSeedRadius_pos R hR
  have hsmall : h * ‖z‖ ≤ (1 / 4 : ℝ) := by
    calc
      h * ‖z‖ = ‖z‖ / (4 * (R + 1)) := by
        dsimp [h, quantitativeSeedRadius]
        ring
      _ ≤ 1 / 4 := by
        apply (div_le_iff₀ (by positivity : 0 < 4 * (R + 1))).2
        nlinarith
  have hpert := fourierLaplace_sub_one_norm_le (normalizedEvenSeed h hh) h hh.le
    (normalizedEvenSeed_tsupport h hh) (normalizedEvenSeed_integral h hh)
    (normalizedEvenSeed_norm_integral h hh) z (by linarith)
  have hreverse := norm_sub_norm_le (1 : ℂ) (fourierLaplace (normalizedEvenSeed h hh) z)
  rw [norm_one, norm_sub_rev] at hreverse
  change (1 / 2 : ℝ) ≤ ‖fourierLaplace (normalizedEvenSeed h hh) z‖
  linarith

#print axioms normalizedEvenSeed_tsupport
#print axioms fourierLaplace_sub_one_norm_le
#print axioms quantitativeEvenSeed_transform_lower

end D5.S3.Weil.TestFunctions.QuantitativeEvenSeed
