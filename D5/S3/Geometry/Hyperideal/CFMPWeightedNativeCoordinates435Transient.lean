import D5.S3.Geometry.Hyperideal.CFMPWeightedNativePlane435Transient
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

noncomputable section
set_option autoImplicit false
open MeasureTheory Set
open scoped Matrix BigOperators ENNReal NNReal
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPReflectedPlaneChart435Transient
open CFMPWeightedNativePlane435Transient

namespace CFMPWeightedNativeCoordinates435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem upperHalfPlane_weighted_integral (A : Set UpperHalfPlane)
    (hA : MeasurableSet A) (weight : UpperHalfPlane → ℝ≥0∞) :
    (∫⁻ z in A, weight z ∂(volume : Measure UpperHalfPlane)) =
      ∫⁻ c in UpperHalfPlane.coe '' A,
        ENNReal.ofReal ((c.im)⁻¹ ^ (2 : ℕ)) * weight (UpperHalfPlane.ofComplex c)
          ∂(volume : Measure ℂ) := by
  have hvol : (volume : Measure UpperHalfPlane) =
      (volume.comap UpperHalfPlane.coe).withDensity
        (fun z => ENNReal.ofReal ((z.im)⁻¹ ^ (2 : ℕ))) := by
    rw [UpperHalfPlane.volume_def]
    congr 1
    funext z
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
    simp [NNReal.coe_pow,NNReal.coe_div,one_div]
  have hm : Measurable (fun z : UpperHalfPlane =>
      ENNReal.ofReal ((z.im)⁻¹ ^ (2 : ℕ))) := by
    fun_prop
  rw [hvol, setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable _ hm weight hA
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hp : MeasurePreserving UpperHalfPlane.coe (volume.comap UpperHalfPlane.coe)
      (volume.restrict (range UpperHalfPlane.coe)) :=
    ⟨UpperHalfPlane.measurable_coe, by rw [UpperHalfPlane.measurableEmbedding_coe.map_comap]⟩
  have h := hp.setLIntegral_comp_emb UpperHalfPlane.measurableEmbedding_coe
    (fun c : ℂ => ENNReal.ofReal ((c.im)⁻¹ ^ (2 : ℕ)) *
      weight (UpperHalfPlane.ofComplex c)) A
  rw [Measure.restrict_restrict_of_subset (image_subset_range UpperHalfPlane.coe A)] at h
  simpa only [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.coe_im, Pi.mul_apply] using h

-- The original closed parameter set is retained; the weight can vary arbitrarily.
theorem native_plane_weighted_coordinates
    (e : UpperHalfPlane → HyperbolicThreeSpace) (he : Isometry e)
    (z : E → UpperHalfPlane) (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) (K : Set E) (hK : MeasurableSet K)
    (hr : ∀ q ∈ K, 0 < radius (affine v a q))
    (hd : ∀ q ∈ K, 0 < delta (affine v a q))
    (hz : ∀ q ∈ K, Complex.measurableEquivPi (z q : ℂ) = chart (affine v a q))
    (weight : HyperbolicThreeSpace → ℝ≥0∞) :
    (∫⁻ p in (fun q => e (z q)) '' K, weight p
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      ∫⁻ q in K, ENNReal.ofReal
        (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3) *
          weight (e (z q)) := by
  have himage : Complex.measurableEquivPi '' (UpperHalfPlane.coe '' (z '' K)) =
      (fun q => chart (affine v a q)) '' K := by
    rw [image_image,image_image]
    exact Set.image_congr hz
  have hf : ∀ q ∈ K, HasFDerivWithinAt (fun w => chart (affine v a w))
      (jacobian a (affine v a q)).mulVecLin.toContinuousLinearMap K q :=
    fun q hq => (affine_chart_hasFDerivAt v a q (hr q hq) (hd q hq).ne').hasFDerivWithinAt
  have hsub : K ⊆ {q | 0 < radius (affine v a q) ∧ 0 < delta (affine v a q)} :=
    fun q hq => ⟨hr q hq,hd q hq⟩
  have hi : InjOn (fun q => chart (affine v a q)) K :=
    Set.InjOn.mono hsub (affine_chart_injOn v a S hv hS ha)
  have hA : MeasurableSet (z '' K) := by
    apply UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mp
    apply Complex.measurableEquivPi.measurableEmbedding.measurableSet_image.mp
    rw [himage]
    exact measurable_image_of_fderivWithin hK hf hi
  let weightE : E → ℝ≥0∞ := fun t =>
    weight (e (UpperHalfPlane.ofComplex (Complex.measurableEquivPi.symm t)))
  let H : E → ℝ≥0∞ := fun t => ENNReal.ofReal ((t 1)⁻¹ ^ (2 : ℕ)) * weightE t
  calc
    _ = ∫⁻ u in z '' K, weight (e u) ∂(volume : Measure UpperHalfPlane) := by
      rw [← image_image]
      exact native_plane_weighted_integral e he weight (z '' K)
    _ = ∫⁻ c in UpperHalfPlane.coe '' (z '' K),
        ENNReal.ofReal ((c.im)⁻¹ ^ (2 : ℕ)) * weight (e (UpperHalfPlane.ofComplex c))
          ∂(volume : Measure ℂ) := upperHalfPlane_weighted_integral _ hA _
    _ = ∫⁻ t in (fun q => chart (affine v a q)) '' K, H t := by
      rw [← himage]
      have h := Complex.volume_preserving_equiv_pi.setLIntegral_comp_emb
        Complex.measurableEquivPi.measurableEmbedding H
        (UpperHalfPlane.coe '' (z '' K))
      simpa [H,weightE,Complex.measurableEquivPi_apply] using h
    _ = ∫⁻ q in K, ENNReal.ofReal
        (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3) *
          weightE (chart (affine v a q)) :=
      affine_chart_weighted_density_integral v a S hv hS ha K hK hr hd weightE
    _ = _ := by
      apply setLIntegral_congr_fun hK
      intro q hq
      dsimp only
      rw [← hz q hq]
      simp only [weightE, MeasurableEquiv.symm_apply_apply, UpperHalfPlane.ofComplex_apply]

end CFMPWeightedNativeCoordinates435Transient
