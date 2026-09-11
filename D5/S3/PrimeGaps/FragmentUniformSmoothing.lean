/- GID: D5/S3/PrimeGaps/FragmentUniformSmoothing
   generality: G
   mirror-B: D5/B/S3/PrimeGaps/FragmentUniformSmoothing
   mirror-E: none(waiver:measure-domination)
   anchors: []
   utility: none
   digest: Derive volume domination for the actual uniform scale mixture used by the Dickman perpetuity. -/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform scale smoothing

This file constructs the law of `U * (zeta + S)` on an actual product measure,
where `U` is uniform on `(0,1]` and independent of the nonnegative random
variable `S`. It proves probability normalization and volume domination;
no density or anti-concentration hypothesis is assumed.

For the canonical `fragmentLaw`, identifying its scalar mass law with this
mixture is a separate distributional theorem. The consumer states that
identity explicitly. The Laplace-functional proof of the identity is given
in the accompanying research discussion, but is not a theorem in this file.

The distributional fixed point is classical Dickman theory: Bhattacharjee
and Goldstein, arXiv:1706.08192; the scale-invariant Poisson interpretation is
Bhattacharjee and Molchanov, arXiv:1911.06229. No priority claim is made.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PrimeGap186

/-- The pushforward of the independent residual/uniform pair. The order of
coordinates is residual first and uniform second. -/
noncomputable def uniformScaleMixture (zeta : ℝ) (nu : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.2 * (zeta + p.1))
    (nu.prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))

/-- The unit interval already has volume one, so no normalization oracle is
needed to construct the probability law. -/
theorem uniformScaleMixture_isProbabilityMeasure
    (zeta : ℝ) (nu : Measure ℝ) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (uniformScaleMixture zeta nu) := by
  letI : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ⟨by simp [Real.volume_Ioc]⟩
  unfold uniformScaleMixture
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- Integrating the conditional scaled-uniform sections gives a genuine
Lebesgue-volume bound for every measurable set, including unbounded sets. -/
theorem uniformScaleMixture_apply_le
    (zeta : ℝ) (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hzeta : 0 < zeta) (hnu : ∀ᵐ s ∂nu, 0 ≤ s)
    (A : Set ℝ) (hA : MeasurableSet A) :
    uniformScaleMixture zeta nu A ≤ ENNReal.ofReal zeta⁻¹ * volume A := by
  have hmap : Measurable (fun p : ℝ × ℝ => p.2 * (zeta + p.1)) := by fun_prop
  unfold uniformScaleMixture
  rw [Measure.map_apply hmap hA, Measure.prod_apply (hA.preimage hmap)]
  calc
    _ ≤ ∫⁻ _s, ENNReal.ofReal zeta⁻¹ * volume A ∂nu := by
      apply lintegral_mono_ae
      refine hnu.mono fun s hs => ?_
      change (volume.restrict (Set.Ioc (0 : ℝ) 1))
        ((fun u : ℝ => u * (zeta + s)) ⁻¹' A) ≤ _
      have hscale : 0 < zeta + s := lt_of_lt_of_le hzeta (by linarith)
      have hinv : (zeta + s)⁻¹ ≤ zeta⁻¹ := by
        simpa only [one_div] using
          one_div_le_one_div_of_le hzeta (show zeta ≤ zeta + s by linarith)
      calc
        _ ≤ volume ((fun u : ℝ => u * (zeta + s)) ⁻¹' A) :=
          Measure.restrict_apply_le _ _
        _ = ENNReal.ofReal (zeta + s)⁻¹ * volume A := by
          rw [Real.volume_preimage_mul_right (ne_of_gt hscale),
            abs_of_pos (inv_pos.mpr hscale)]
        _ ≤ _ := mul_le_mul_left (ENNReal.ofReal_le_ofReal hinv) _
    _ = _ := by simp

/-- Every half-open interval of length delta has probability at most
`delta / zeta`. Negative lengths give the empty-interval case automatically. -/
theorem uniformScaleMixture_Ico_le
    (zeta : ℝ) (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hzeta : 0 < zeta) (hnu : ∀ᵐ s ∂nu, 0 ≤ s) (x delta : ℝ) :
    uniformScaleMixture zeta nu (Set.Ico x (x + delta)) ≤
      ENNReal.ofReal (delta / zeta) := by
  calc
    _ ≤ ENNReal.ofReal zeta⁻¹ * ENNReal.ofReal delta := by
      simpa only [Real.volume_Ico, add_sub_cancel_left] using
        uniformScaleMixture_apply_le zeta nu hzeta hnu
          (Set.Ico x (x + delta)) measurableSet_Ico
    _ = _ := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hzeta.le)]
      congr 1
      ring

/-- A scalar fixed-point law inherits the interval estimate. This is a
consumer of the proved mixture bound, not a proof that a given Poisson
construction satisfies the fixed-point identity. -/
theorem uniform_scale_fixedPoint_Ico_le
    (zeta : ℝ) (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hzeta : 0 < zeta) (hnu : ∀ᵐ s ∂nu, 0 ≤ s)
    (hfixed : nu = uniformScaleMixture zeta nu) (x delta : ℝ) :
    nu (Set.Ico x (x + delta)) ≤ ENNReal.ofReal (delta / zeta) := by
  calc
    _ = uniformScaleMixture zeta nu (Set.Ico x (x + delta)) :=
      congrArg (fun m : Measure ℝ => m (Set.Ico x (x + delta))) hfixed
    _ ≤ _ := uniformScaleMixture_Ico_le zeta nu hzeta hnu x delta

#print axioms uniformScaleMixture_isProbabilityMeasure
#print axioms uniformScaleMixture_apply_le
#print axioms uniformScaleMixture_Ico_le
#print axioms uniform_scale_fixedPoint_Ico_le

end PrimeGap186
