import D5.S3.Geometry.Hyperideal.CFMPReflectedPlaneChart435Transient
import D5.S3.Geometry.Hyperideal.CFMPVerticalNative2Density435Transient

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped Matrix BigOperators ENNReal NNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPReflectedPlaneChart435Transient
open CFMPVerticalNative2Density435Transient

namespace CFMPWeightedNativePlane435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

-- Native measure transport allows a variable weight, including infinite integrals.
theorem native_plane_weighted_integral (e : UpperHalfPlane → HyperbolicThreeSpace)
    (he : Isometry e) (weight : HyperbolicThreeSpace → ℝ≥0∞)
    (A : Set UpperHalfPlane) :
    (∫⁻ y in e '' A, weight y
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      ∫⁻ z in A, weight (e z) ∂(volume : Measure UpperHalfPlane) := by
  have hm : MeasurableEmbedding e := he.isClosedEmbedding.measurableEmbedding
  let hp : MeasurePreserving e volume
      ((Measure.euclideanHausdorffMeasure 2).restrict (range e)) :=
    ⟨hm.measurable, native_plane_transport e he⟩
  have h := hp.setLIntegral_comp_emb hm weight A
  rw [Measure.restrict_restrict_of_subset (image_subset_range e A)] at h
  exact h.symm

theorem affine_chart_weighted_density_integral (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) (K : Set E) (hK : MeasurableSet K)
    (hr : ∀ q ∈ K, 0 < radius (affine v a q))
    (hd : ∀ q ∈ K, 0 < delta (affine v a q)) (weight : E → ℝ≥0∞) :
    (∫⁻ y in (fun q => chart (affine v a q)) '' K,
      ENNReal.ofReal ((y 1)⁻¹ ^ (2 : ℕ)) * weight y) =
    ∫⁻ q in K, ENNReal.ofReal
      (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3) * weight (chart (affine v a q)) := by
  have hf : ∀ q ∈ K, HasFDerivWithinAt (fun w => chart (affine v a w))
      (jacobian a (affine v a q)).mulVecLin.toContinuousLinearMap K q :=
    fun q hq => (affine_chart_hasFDerivAt v a q (hr q hq) (hd q hq).ne').hasFDerivWithinAt
  have hsub : K ⊆ {q | 0 < radius (affine v a q) ∧ 0 < delta (affine v a q)} := by
    intro q hq
    exact ⟨hr q hq, hd q hq⟩
  have hi : InjOn (fun q => chart (affine v a q)) K :=
    Set.InjOn.mono hsub (affine_chart_injOn v a S hv hS ha)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hK hf hi]
  apply setLIntegral_congr_fun hK
  intro q hq
  have hdet : ((jacobian a (affine v a q)).mulVecLin.toContinuousLinearMap).det =
      (jacobian a (affine v a q)).det := by
    rw [LinearMap.det_toContinuousLinearMap]
    exact LinearMap.det_toLin' _
  have hprod : |(jacobian a (affine v a q)).det| *
      ((chart (affine v a q) 1)⁻¹)^2 =
      |(augmented a (affine v a q)).det| /
        (Real.sqrt (radius (affine v a q)))^3 := by
    simpa only [div_eq_mul_inv, inv_pow] using
      jacobian_height_density a (affine v a q) (hr q hq) (hd q hq)
  dsimp only
  rw [hdet, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _), hprod, affine_augmented_det]

end CFMPWeightedNativePlane435Transient
