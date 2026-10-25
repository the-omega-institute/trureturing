import D5.S3.Geometry.Hyperideal.CFMPNativePlaneArea435Transient
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
open CFMPReflectedPlaneChart435Transient
open CFMPNativePlaneArea435Transient
open D5.S3.Geometry.HyperbolicUpperHalfSpace

namespace CFMPNativePlaneFiniteArea435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem compact_density_integrable (v : W) (a : A32) (K : Set E)
    (hK : IsCompact K) (hr : ∀ q ∈ K, 0 < radius (affine v a q)) :
    IntegrableOn (fun q => |(augmented a v).det| /
      (Real.sqrt (radius (affine v a q)))^3) K := by
  have haff : Continuous (affine v a) := continuous_iff_continuousAt.mpr
    (fun q => (affine_hasFDerivAt v a q).continuousAt)
  have hc (i : Fin 3) : Continuous (fun q => affine v a q i) :=
    (continuous_apply i).comp haff
  have hrad : Continuous (fun q : E => radius (affine v a q)) :=
    ((hc 2).pow 2).sub ((hc 1).pow 2) |>.sub ((hc 0).pow 2)
  apply ContinuousOn.integrableOn_compact hK
  exact continuousOn_const.div (hrad.continuousOn.sqrt.pow 3)
    (fun q hq => pow_ne_zero 3 (Real.sqrt_pos.mpr (hr q hq)).ne')

theorem compact_density_lintegral_finite (v : W) (a : A32) (K : Set E)
    (hK : IsCompact K) (hr : ∀ q ∈ K, 0 < radius (affine v a q)) :
    (∫⁻ q in K, ENNReal.ofReal
      (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3)) < ∞ :=
  (compact_density_integrable v a K hK hr).lintegral_lt_top

-- Finiteness of the actual native image follows under the same chart conditions.
theorem native_compact_area_finite (e : UpperHalfPlane → HyperbolicThreeSpace)
    (he : Isometry e) (z : E → UpperHalfPlane)
    (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) (K : Set E) (hK : IsCompact K)
    (hr : ∀ q ∈ K, 0 < radius (affine v a q))
    (hd : ∀ q ∈ K, 0 < delta (affine v a q))
    (hz : ∀ q ∈ K, Complex.measurableEquivPi (z q : ℂ) = chart (affine v a q)) :
    (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
      ((fun q => e (z q)) '' K) < ∞ := by
  rw [native_plane_area e he z v a S hv hS ha K hK.measurableSet hr hd hz]
  exact compact_density_lintegral_finite v a K hK hr


theorem density_integral_positive (v : W) (a : A32) (K : Set E)
    (hr : ∀ q ∈ K, 0 < radius (affine v a q))
    (hC : (augmented a v).det ≠ 0) (hvol : 0 < volume K) :
    0 < ∫⁻ q in K, ENNReal.ofReal
      (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3) := by
  have haff : Continuous (affine v a) := continuous_iff_continuousAt.mpr
    (fun q => (affine_hasFDerivAt v a q).continuousAt)
  have hc (i : Fin 3) : Continuous (fun q => affine v a q i) :=
    (continuous_apply i).comp haff
  have hrad : Continuous (fun q : E => radius (affine v a q)) :=
    ((hc 2).pow 2).sub ((hc 1).pow 2) |>.sub ((hc 0).pow 2)
  have hm : Measurable (fun q : E => ENNReal.ofReal
      (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3)) :=
    ENNReal.measurable_ofReal.comp
      (measurable_const.div (hrad.sqrt.pow 3).measurable)
  rw [setLIntegral_pos_iff hm]
  have hs : Function.support (fun q : E => ENNReal.ofReal
      (|(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3)) ∩ K = K := by
    apply Set.inter_eq_right.mpr
    intro q hq
    exact ne_of_gt (ENNReal.ofReal_pos.mpr
      (div_pos (abs_pos.mpr hC) (pow_pos (Real.sqrt_pos.mpr (hr q hq)) 3)))
  rw [hs]
  exact hvol

def referenceTriangle : Set E := {q | 0 ≤ q 0 ∧ 0 ≤ q 1 ∧ q 0 + q 1 ≤ 1}

theorem referenceTriangle_compact : IsCompact referenceTriangle := by
  have hclosed : IsClosed referenceTriangle :=
    (isClosed_le continuous_const (continuous_apply 0)).inter
      ((isClosed_le continuous_const (continuous_apply 1)).inter
        (isClosed_le ((continuous_apply 0).add (continuous_apply 1)) continuous_const))
  apply (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1))).of_isClosed_subset hclosed
  intro q hq
  constructor
  · intro i
    fin_cases i
    · exact hq.1
    · exact hq.2.1
  · intro i
    fin_cases i <;> dsimp <;> linarith [hq.1, hq.2.1, hq.2.2]

theorem referenceTriangle_volume_positive : 0 < volume referenceTriangle := by
  let U : Set E := {q | 0 < q 0 ∧ 0 < q 1 ∧ q 0 + q 1 < 1}
  have ho : IsOpen U :=
    (isOpen_lt continuous_const (continuous_apply 0)).inter
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt ((continuous_apply 0).add (continuous_apply 1)) continuous_const))
  have hn : U.Nonempty := ⟨(fun _ => (1/4 : ℝ)), by norm_num [U]⟩
  have hs : U ⊆ referenceTriangle := fun q hq => ⟨hq.1.le, hq.2.1.le, hq.2.2.le⟩
  exact (ho.measure_pos volume hn).trans_le (measure_mono hs)

theorem native_compact_area_bounds_of_pointwise
    (e : UpperHalfPlane → HyperbolicThreeSpace)
    (he : Isometry e) (z : E → UpperHalfPlane) (p : E → HyperbolicThreeSpace)
    (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec) (K : Set E) (hK : IsCompact K)
    (hvol : 0 < volume K)
    (hr : ∀ q ∈ K, 0 < radius (affine v a q))
    (hd : ∀ q ∈ K, 0 < delta (affine v a q))
    (hz : ∀ q ∈ K, Complex.measurableEquivPi (z q : ℂ) = chart (affine v a q))
    (hp : ∀ q ∈ K, e (z q) = p q) :
    0 < (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) (p '' K) ∧
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) (p '' K) < ∞ := by
  rw [native_plane_area_of_pointwise e he z p v a S hv hS ha K hK.measurableSet hr hd hz hp]
  exact ⟨density_integral_positive v a K hr (augmented_det_ne_zero v a S hv hS ha) hvol,
    compact_density_lintegral_finite v a K hK hr⟩

theorem native_closed_triangle_area_bounds_of_pointwise
    (e : UpperHalfPlane → HyperbolicThreeSpace)
    (he : Isometry e) (z : E → UpperHalfPlane) (p : E → HyperbolicThreeSpace)
    (v : W) (a : A32) (S : W →ₗ[ℝ] ℝ)
    (hv : S v = 1) (hS : ∀ j, S (a.col j) = 0)
    (ha : Function.Injective a.mulVec)
    (hr : ∀ q ∈ referenceTriangle, 0 < radius (affine v a q))
    (hd : ∀ q ∈ referenceTriangle, 0 < delta (affine v a q))
    (hz : ∀ q ∈ referenceTriangle, Complex.measurableEquivPi (z q : ℂ) = chart (affine v a q))
    (hp : ∀ q ∈ referenceTriangle, e (z q) = p q) :
    0 < (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) (p '' referenceTriangle) ∧
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) (p '' referenceTriangle) < ∞ :=
  native_compact_area_bounds_of_pointwise e he z p v a S hv hS ha referenceTriangle
    referenceTriangle_compact referenceTriangle_volume_positive hr hd hz hp

end CFMPNativePlaneFiniteArea435Transient
