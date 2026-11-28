/- GID: D5/S3/Divergence/ChiSquareBilinearFusion
   generality: G
   mirror-B: D5/B/S3/Divergence/ChiSquareBilinearFusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bilinear chi-square fusion for arbitrary finite channels under a common uniform input. -/

module

public import OmegaMath.InformationTheory.PottsFusion.RawChannel
public import OmegaMath.InformationTheory.PottsFusion.CalibratedBilinear

/-! # Bilinear information combining without channel symmetry -/

@[expose] public section

namespace D5.S3.Divergence.ChiSquareBilinearFusion

open scoped BigOperators
open Omega.InformationTheory.PottsFusion

universe u v w

/-- A coefficient depending only on the input size controls every finite output pair. -/
theorem bilinear_fusion_bound
    (I : Type u) [Fintype I] [Nonempty I]
    (Y : Type v) (Z : Type w) [Fintype Y] [Fintype Z]
    (P : I → Y → ℝ) (Q : I → Z → ℝ)
    (hP0 : ∀ i y, 0 ≤ P i y) (hQ0 : ∀ i z, 0 ≤ Q i z)
    (hP1 : ∀ i, ∑ y, P i y = 1) (hQ1 : ∀ i, ∑ z, Q i z = 1) :
    channelCapacity (rawProduct P Q) ≤ channelCapacity P + channelCapacity Q +
      (13 * (Fintype.card I : ℝ)) * channelCapacity P * channelCapacity Q := by
  rw [raw_product_capacity_eq_calibratedFusion P Q hP0 hQ0,
    raw_capacity_eq_calibratedCapacity P hP0 hP1,
    raw_capacity_eq_calibratedCapacity Q hQ0 hQ1]
  apply calibratedFusion_bilinear_bound
  all_goals first
    | exact raw_margin_nonneg P hP0
    | exact raw_margin_nonneg Q hQ0
    | exact raw_density_nonneg P hP0
    | exact raw_density_nonneg Q hQ0
    | exact raw_density_mean_one P
    | exact raw_density_mean_one Q
    | exact raw_density_calibrated P hP0 hP1
    | exact raw_density_calibrated Q hQ0 hQ1

end D5.S3.Divergence.ChiSquareBilinearFusion
