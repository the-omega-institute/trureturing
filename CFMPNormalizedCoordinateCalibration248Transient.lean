import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeBoundaryVariation435Transient
import D5.S3.Geometry.Hyperideal.CFMPNormalizedHausdorffDimension435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalBoundaryFlux435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorNativeReferenceFlux435Transient
import D5.S3.Geometry.Hyperideal.CFMPGenuineLengthNeighborhood435Transient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff ENNReal Matrix.Norms.Elementwise
open Set Filter MeasureTheory
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPFrameAffineTransport435Transient CFMPActualCellMotion435Transient
open CFMPActualNativeCellMotion435Transient CFMPOriginalCellsIndependent435Transient
open CFMPOriginalFrameDensity435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalCellKernel435Transient CFMPCompactKernelIntegral435Transient
open CFMPCompactKernelTube435Transient (delta delta_compact timeDerivative)
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace

open CFMPActualNativeMass435Transient
open D5.S3.Geometry.HyperbolicNormalizedDensity
open D5.S3.Geometry.HyperbolicTopology

open CFMPAnchoredOriginalExteriorFaceMotion435Transient
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalExteriorNativeNormal435Transient
open CFMPNativePullbackMetric435Transient CFMPNativePlaneNormal435Transient

namespace CFMPOriginalNormalizedVolume435Transient

local instance : MeasurableSpace Coordinates3 := borel _
local instance : BorelSpace Coordinates3 := ⟨rfl⟩
local instance : MeasurableSpace Native3 := borel _
local instance : BorelSpace Native3 := ⟨rfl⟩

-- All declarations in this temporary file are exact applications, not library additions.
theorem coordinate_h3_eq_volume_comap :
    (Measure.euclideanHausdorffMeasure 3 : Measure Coordinates3) =
      (volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ) := by
  have hdim : Module.finrank ℝ (Ambient ℂ) = 3 := by
    rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℝ)).finrank_eq]
    simp [Module.finrank_prod]
  have hcal : (Measure.euclideanHausdorffMeasure 3 : Measure (Ambient ℂ)) = volume := by
    simpa only [hdim] using
      (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := Ambient ℂ))
  have hset : MeasurableSet {p : Ambient ℂ | 0 < (WithLp.ofLp p).2} :=
    (isOpen_lt continuous_const (by fun_prop)).measurableSet
  have he : MeasurableEmbedding (Subtype.val : Coordinates3 → Ambient ℂ) :=
    Topology.IsEmbedding.subtypeVal.measurableEmbedding (by
      simpa only [Subtype.range_val_subtype] using hset)
  ext A hA
  rw [Measure.comap_apply _ Subtype.val_injective
    (fun B hB => he.measurableSet_image.mpr hB) _ hA]
  rw [← hcal]
  exact (isometry_subtype_coe.euclideanHausdorffMeasure_image A).symm

theorem normalized_native_h3_density :
    (Measure.euclideanHausdorffMeasure 3 : Measure Native3).map coordinatesEquiv =
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)).withDensity heightDensity := by
  have h := CFMPNormalizedHausdorffDimension435Transient.normalized_native_density_nat 3
  rw [coordinate_h3_eq_volume_comap] at h
  exact h

theorem calibrated_native_h3_eq (c : ℝ≥0∞)
    (hcal : (c⁻¹ • rawNativeMeasure).map coordinatesEquiv =
      ((volume : Measure (Ambient ℂ)).comap
        (Subtype.val : Coordinates3 → Ambient ℂ)).withDensity heightDensity) :
    c⁻¹ • rawNativeMeasure = (Measure.euclideanHausdorffMeasure 3 : Measure Native3) := by
  apply coordinatesEquiv.measurableEmbedding.map_injective
  exact hcal.trans normalized_native_h3_density.symm

end CFMPOriginalNormalizedVolume435Transient
