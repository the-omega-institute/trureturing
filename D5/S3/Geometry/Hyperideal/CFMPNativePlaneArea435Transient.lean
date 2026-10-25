import D5.S3.Geometry.Hyperideal.CFMPVerticalNative2Density435Transient
import D5.S3.Geometry.Hyperideal.CFMPReflectedPlaneChart435Transient
import D5.S3.Geometry.Hyperideal.CFMPActualPlaneIsometry435Transient
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped NNReal ENNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPVerticalNative2Density435Transient
open CFMPReflectedPlaneChart435Transient

namespace CFMPNativePlaneArea435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

-- The coordinate equivalence preserves volume; no metric claim on the sup-norm plane.
theorem complex_coordinate_integral (B : Set ℂ) :
    (∫⁻ z in B, ENNReal.ofReal ((z.im)⁻¹ ^ (2 : ℕ)) ∂(volume : Measure ℂ)) =
      ∫⁻ t in Complex.measurableEquivPi '' B,
        ENNReal.ofReal ((t 1)⁻¹ ^ (2 : ℕ)) ∂(volume : Measure E) := by
  exact Complex.volume_preserving_equiv_pi.setLIntegral_comp_emb
    Complex.measurableEquivPi.measurableEmbedding
    (fun t : E => ENNReal.ofReal ((t 1)⁻¹ ^ (2 : ℕ))) B

-- This identifies the actual image measure of any supplied native isometric plane chart.
theorem native_plane_area (e : UpperHalfPlane → HyperbolicThreeSpace)
    (he : Isometry e) (z : E → UpperHalfPlane)
    (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) (K : Set E) (hK : MeasurableSet K)
    (hr : ∀ q ∈ K, 0 < radius (affine v a q))
    (hd : ∀ q ∈ K, 0 < delta (affine v a q))
    (hz : ∀ q ∈ K, Complex.measurableEquivPi (z q : ℂ) = chart (affine v a q)) :
    (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
        ((fun q => e (z q)) '' K) =
      ∫⁻ q in K, ENNReal.ofReal
        (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3) := by
  have himage : Complex.measurableEquivPi '' (UpperHalfPlane.coe '' (z '' K)) =
      (fun q => chart (affine v a q)) '' K := by
    rw [image_image,image_image]
    exact Set.image_congr hz
  calc
    _ = (volume : Measure UpperHalfPlane) (z '' K) := by
      rw [← image_image]
      exact native_plane_image e he (z '' K)
    _ = ∫⁻ c in UpperHalfPlane.coe '' (z '' K),
        ENNReal.ofReal ((c.im)⁻¹ ^ (2 : ℕ)) ∂(volume : Measure ℂ) := by
      rw [UpperHalfPlane.volume_eq_lintegral]
      apply lintegral_congr
      intro c
      rw [← ENNReal.ofReal_coe_nnreal]
      congr 1
      simp [NNReal.coe_pow, NNReal.coe_div, Real.norm_eq_abs, one_div, inv_pow, sq_abs]
    _ = ∫⁻ t in (fun q => chart (affine v a q)) '' K,
        ENNReal.ofReal ((t 1)⁻¹ ^ (2 : ℕ)) ∂(volume : Measure E) := by
      rw [complex_coordinate_integral,himage]
    _ = _ := affine_chart_density_integral v a S hv hS ha K hK hr hd

-- Equality on K keeps the original native image when a chart parametrizes that same map.
theorem native_plane_area_of_pointwise (e : UpperHalfPlane → HyperbolicThreeSpace)
    (he : Isometry e) (z : E → UpperHalfPlane) (p : E → HyperbolicThreeSpace)
    (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) (K : Set E) (hK : MeasurableSet K)
    (hr : ∀ q ∈ K, 0 < radius (affine v a q))
    (hd : ∀ q ∈ K, 0 < delta (affine v a q))
    (hz : ∀ q ∈ K, Complex.measurableEquivPi (z q : ℂ) = chart (affine v a q))
    (hp : ∀ q ∈ K, e (z q) = p q) :
    (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) (p '' K) =
      ∫⁻ q in K, ENNReal.ofReal
        (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3) := by
  rw [← Set.image_congr hp]
  exact native_plane_area e he z v a S hv hS ha K hK hr hd hz

end CFMPNativePlaneArea435Transient
