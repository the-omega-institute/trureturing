import D5.S3.Geometry.Hyperideal.CFMPHausdorffDimension435Transient
import Mathlib.Geometry.Euclidean.Volume.Measure

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped NNReal ENNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicNormalizedDensity
open CFMPHausdorffDimension435Transient

namespace CFMPNormalizedHausdorffDimension435Transient

private local instance : MeasurableSpace (UpperHalfSpace ℂ) := borel _
private local instance : BorelSpace (UpperHalfSpace ℂ) := ⟨rfl⟩
private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

-- A temporary measure-scaling application, consumed by the normalized comparison.
private theorem density_smul_nnreal {X : Type*} [MeasurableSpace X]
    (c : ℝ≥0) (μ : Measure X) (f : X → ℝ≥0∞) :
    (c • μ).withDensity f = c • μ.withDensity f := by
  ext s hs
  simp [withDensity_apply, hs, lintegral_smul_measure]

-- The same dimension-dependent scalar normalizes both metrics.
theorem normalized_native_density_nat (d : ℕ) :
    (Measure.euclideanHausdorffMeasure d : Measure HyperbolicThreeSpace).map
        coordinatesEquiv =
      (Measure.euclideanHausdorffMeasure d : Measure (UpperHalfSpace ℂ)).withDensity
        (fun x => ENNReal.ofReal ((height x)⁻¹ ^ d)) := by
  let c : ℝ≥0 := Measure.addHaarScalarFactor
    (volume : Measure (EuclideanSpace ℝ (Fin d))) (Measure.hausdorffMeasure (d : ℝ))
  change (c • rawNativeMeasureDim d).map coordinatesEquiv =
    (c • rawCoordinateMeasureDim d).withDensity (heightDensityDim d)
  rw [Measure.map_smul _ coordinatesEquiv.measurable.aemeasurable,
    raw_native_density_nat]
  exact (density_smul_nnreal c (rawCoordinateMeasureDim d) (heightDensityDim d)).symm

-- Independent two-dimensional Euclidean calibration, with no H3 volume scalar.
example : (Measure.euclideanHausdorffMeasure 2 : Measure ℂ) = volume := by
  simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℂ))

end CFMPNormalizedHausdorffDimension435Transient
