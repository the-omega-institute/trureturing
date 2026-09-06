/- GID: D5/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability
   generality: G
   mirror-B: D5/B/S3/Observer/HilbertGeometry/VectorPathDerivativeIntegrability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounded variation gives Bochner integrability of the totalized vector path derivative. -/

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.Topology.EMetricSpace.VariationOnFromTo

/-!
Derivative integrability is a prerequisite for the Bochner fundamental theorem
for absolutely continuous Hilbert paths. The estimate here works in every real
Banach space. It does not assert almost-everywhere differentiability or integral
reconstruction: Mathlib's `deriv` is zero at points of nondifferentiability.

The scalar monotone derivative-integrability owner is reused after domination
by the signed accumulated variation. No square-integrability claim is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace D5.S3.Observer.HilbertGeometry.VectorPathDerivativeIntegrability

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_deriv_le_of_increment_le {f : ℝ → F} {g : ℝ → ℝ} {t : ℝ}
    (hg : DifferentiableAt ℝ g t)
    (hfg : ∀ᶠ y in 𝓝 t, ‖f y - f t‖ ≤ ‖g y - g t‖) :
    ‖deriv f t‖ ≤ ‖deriv g t‖ := by
  by_cases hf : DifferentiableAt ℝ f t
  · apply le_of_tendsto_of_tendsto hf.hasDerivAt.tendsto_slope.norm
      hg.hasDerivAt.tendsto_slope.norm
    filter_upwards [hfg.filter_mono nhdsWithin_le_nhds] with y hy
    simpa only [slope, vsub_eq_sub, norm_smul] using
      mul_le_mul_of_nonneg_left hy (norm_nonneg ((y - t)⁻¹))
  · simp [deriv_zero_of_not_differentiableAt hf]

omit [NormedSpace ℝ F] in
private theorem norm_sub_le_variation_sub {f : ℝ → F} {a b u v : ℝ}
    (hf : BoundedVariationOn f (uIcc a b))
    (hu : u ∈ uIcc a b) (hv : v ∈ uIcc a b) :
    ‖f v - f u‖ ≤
      ‖variationOnFromTo f (uIcc a b) a v - variationOnFromTo f (uIcc a b) a u‖ := by
  wlog huv : u ≤ v generalizing u v
  · simpa only [norm_sub_rev] using this hv hu (le_of_not_ge huv)
  rw [variationOnFromTo.sub_right hf.locallyBoundedVariationOn (by simp) hv hu,
    Real.norm_of_nonneg (variationOnFromTo.nonneg_of_le _ _ huv),
    variationOnFromTo.eq_of_le _ _ huv, ← dist_eq_norm]
  exact (hf.mono inter_subset_left).dist_le ⟨hv, huv, le_rfl⟩ ⟨hu, le_rfl, huv⟩

variable [CompleteSpace F]

/-- The totalized derivative of a Banach-valued path of bounded variation is
Bochner interval-integrable, without a differentiability hypothesis. -/
theorem bounded_variation_interval_integrable_deriv {f : ℝ → F} {a b : ℝ}
    (hf : BoundedVariationOn f (uIcc a b)) :
    IntervalIntegrable (deriv f) volume a b := by
  let V := variationOnFromTo f (uIcc a b) a
  have hV : MonotoneOn V (uIcc a b) :=
    variationOnFromTo.monotoneOn hf.locallyBoundedVariationOn (by simp)
  apply hV.intervalIntegrable_deriv.mono_fun (aestronglyMeasurable_deriv _ _)
  rw [EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
  -- Away from the null endpoint, variation controls the local difference quotients.
  filter_upwards [hV.ae_differentiableWithinAt_of_mem,
      show ∀ᵐ t : ℝ, t ≠ max a b by simp [ae_iff, measure_singleton]] with t ht htb htmem
  have htcc : t ∈ uIcc a b := uIoc_subset_uIcc htmem
  have htnhds : uIcc a b ∈ 𝓝 t :=
    Icc_mem_nhds htmem.1 (lt_of_le_of_ne htmem.2 htb)
  apply norm_deriv_le_of_increment_le ((ht htcc).differentiableAt htnhds)
  filter_upwards [htnhds] with y hy
  exact norm_sub_le_variation_sub hf htcc hy

/-- Absolute continuity supplies bounded variation and hence Bochner
integrability of the totalized vector derivative. This is not yet the FTC. -/
theorem absolutely_continuous_interval_integrable_deriv {f : ℝ → F} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    IntervalIntegrable (deriv f) volume a b :=
  bounded_variation_interval_integrable_deriv hf.boundedVariationOn

end D5.S3.Observer.HilbertGeometry.VectorPathDerivativeIntegrability
