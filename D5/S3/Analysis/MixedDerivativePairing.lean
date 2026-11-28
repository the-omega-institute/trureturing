/- GID: D5/S3/Analysis/MixedDerivativePairing
   generality: G
   mirror-B: none(waiver:covered-by-null-diamond-de-sitter-kernel-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Mixed derivative pairing against product tests with vanishing endpoint values. -/

import OmegaBuild.Commands
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Complex.Basic

/-!
Omega original.

Mixed derivative pairing against product tests with vanishing endpoint values.
-/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace Omega

set_option maxHeartbeats 500000 in
-- Elaborating the two product integrals requires additional reduction.
/-- A sum of separate coordinate functions vanishes when paired against the mixed derivative
of a product test whose factors vanish at both endpoints of the interval. -/
theorem integral_separate_mul_deriv_product_eq_zero {a b : ℝ} {A B : ℝ → ℂ} {F G : ℝ → ℝ}
    (hab : a ≤ b) (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hFa : F a = 0) (hFb : F b = 0) (hGa : G a = 0) (hGb : G b = 0) :
    let μ := (volume : Measure ℝ).restrict (Ioc a b)
    ∫ z : ℝ × ℝ, (A z.1 + B z.2) * ((deriv F z.1 : ℝ) : ℂ) *
      ((deriv G z.2 : ℝ) : ℂ) ∂μ.prod μ = 0 := by
  let μ := (volume : Measure ℝ).restrict (Ioc a b)
  have hderiv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfa : f a = 0) (hfb : f b = 0) :
      Continuous (fun x => ((deriv f x : ℝ) : ℂ)) ∧ ∫ x : ℝ, ((deriv f x : ℝ) : ℂ) ∂μ = 0 := by
    have hcont : Continuous (deriv f) := hf.continuous_deriv (by norm_num)
    have he : (∫ y in a..b, deriv f y) = 0 := by
      rw [intervalIntegral.integral_deriv_eq_sub (fun x _ => hf.differentiable (by norm_num) x)
        hcont.continuousOn.intervalIntegrable, hfa, hfb, sub_self]
    refine ⟨Complex.continuous_ofReal.comp hcont, ?_⟩
    rw [integral_complex_ofReal]
    change ((↑(∫ x in Ioc a b, deriv f x : ℝ)) : ℂ) = 0
    rw [← intervalIntegral.integral_of_le hab, he, Complex.ofReal_zero]
  obtain ⟨hFc, hF0⟩ := hderiv hF hFa hFb
  obtain ⟨hGc, hG0⟩ := hderiv hG hGa hGb
  have hint {f : ℝ → ℂ} (hf : ContinuousOn f (Icc a b)) : Integrable f μ :=
    (hf.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
  have h1 := (hint (hA.mul hFc.continuousOn)).mul_prod (hint hGc.continuousOn)
  have h2 := (hint hFc.continuousOn).mul_prod (hint (hB.mul hGc.continuousOn))
  change Integrable (fun z : ℝ × ℝ => A z.1 * ↑(deriv F z.1) * ↑(deriv G z.2)) (μ.prod μ)
    at h1
  change Integrable (fun z : ℝ × ℝ => ↑(deriv F z.1) * (B z.2 * ↑(deriv G z.2))) (μ.prod μ)
    at h2
  calc
    _ = ∫ z : ℝ × ℝ, A z.1 * ((deriv F z.1 : ℝ) : ℂ) * ((deriv G z.2 : ℝ) : ℂ) +
        ((deriv F z.1 : ℝ) : ℂ) * (B z.2 * ((deriv G z.2 : ℝ) : ℂ)) ∂μ.prod μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by ring
    _ = 0 := by
      rw [integral_add h1 h2,
        integral_prod_mul (μ := μ) (ν := μ) (fun x => A x * ↑(deriv F x)) (fun x => ↑(deriv G x)),
        integral_prod_mul (μ := μ) (ν := μ) (fun x => ↑(deriv F x)) (fun x => B x * ↑(deriv G x)),
        hF0, hG0, mul_zero, zero_mul, add_zero]

/-- A kernel on a coordinate domain with an almost-everywhere separable expression has
zero mixed pairing on a compact subinterval. -/
theorem integral_mul_deriv_product_eq_zero_of_ae_separate
    {a b : ℝ} {s : Set ℝ} {K : ℝ × ℝ → ℂ} {A B : ℝ → ℂ} {F G : ℝ → ℝ}
    (hab : a ≤ b) (hs : Ioc a b ⊆ s) (hA : ContinuousOn A (Icc a b))
    (hB : ContinuousOn B (Icc a b)) (hF : ContDiff ℝ 1 F) (hG : ContDiff ℝ 1 G)
    (hFa : F a = 0) (hFb : F b = 0) (hGa : G a = 0) (hGb : G b = 0)
    (hsep : let ν := (volume : Measure ℝ).restrict s
      ∀ᵐ z ∂ν.prod ν, K z = A z.1 + B z.2) :
    let μ := (volume : Measure ℝ).restrict (Ioc a b)
    ∫ z : ℝ × ℝ, K z * ((deriv F z.1 : ℝ) : ℂ) * ((deriv G z.2 : ℝ) : ℂ) ∂μ.prod μ = 0 := by
  have hm := Measure.restrict_mono_set (volume : Measure ℝ) hs
  refine (integral_congr_ae ((hsep.filter_mono (ae_mono (Measure.prod_mono hm hm))).mono
    fun z hz => by rw [hz])).trans ?_
  exact integral_separate_mul_deriv_product_eq_zero hab hA hB hF hG hFa hFb hGa hGb

end Omega
