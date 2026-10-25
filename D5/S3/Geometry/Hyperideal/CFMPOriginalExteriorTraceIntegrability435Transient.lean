import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorFaceChart435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativePlaneFiniteArea435Transient
import D5.S3.Geometry.Hyperideal.CFMPWeightedNativeCoordinates435Transient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import D5.S3.Geometry.Hyperideal.CFMPNativeSurfaceJacobian435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeCoordinates435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory Topology
open scoped Matrix BigOperators ENNReal Classical
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicPlaneRealization
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPReflectedPlaneChart435Transient
open CFMPReflectedCoefficientSection435Transient
open CFMPActualPlaneIsometry435Transient
open CFMPActualTriangleNormal435Transient
open CFMPOriginalExteriorFaceChart435Transient
open CFMPNativePlaneFiniteArea435Transient
open CFMPWeightedNativeCoordinates435Transient

namespace CFMPOriginalExteriorTraceIntegrability435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem original_face_continuous_trace_integrable
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Coeff, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) :
    let F : parameterTriangle → HyperbolicThreeSpace := fun q =>
      f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩
    IsClosedEmbedding F ∧
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
        (range F) < ∞ ∧
      ∀ phi : HyperbolicThreeSpace → ℝ, ContinuousOn phi (range F) →
        IntegrableOn phi (range F)
          (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) := by
  classical
  obtain ⟨A,hA,he,hplane,hs,hcols,hdetChart,hinj,hpositive,hchart⟩ :=
    same_reflection_chart_data l hl M hM hG f hf n
  let v : W := forward M (reflectionLinear A) (base l n)
  let a : A32 := reflectedTangents M (reflectionLinear A)
    (direction l n 0) (direction l n 1)
  let S : W →ₗ[ℝ] ℝ := sectionMap M (reflectionLinear A)
  let e : UpperHalfPlane → HyperbolicThreeSpace :=
    fun z => reflectionNative A hA (vertical z)
  let z : E → UpperHalfPlane := fun q =>
    if hq : q ∈ parameterTriangle then Classical.choose (hchart q hq)
    else UpperHalfPlane.I
  let p : E → HyperbolicThreeSpace := fun q =>
    if hq : q ∈ parameterTriangle then
      f ⟨xi l n q, xi_mem_cutBody l hl n q hq⟩
    else f ⟨D5.S3.Geometry.Hyperideal.LengthGramSideTrace.barycenter,
      (shared_radial_body l hl).2.1⟩
  have hchoice (q : E) (hq : q ∈ parameterTriangle) :
      z q = Classical.choose (hchart q hq) := by
    simp only [z, dite_eq_left hq]
  have hp_original (q : E) (hq : q ∈ parameterTriangle) :
      p q = f ⟨xi l n q, xi_mem_cutBody l hl n q hq⟩ := by
    simp only [p, dite_eq_left hq]
  have hpair : ∀ X Y, lorentz (reflectionLinear A X) (reflectionLinear A Y) =
      lorentz X Y := by
    intro X Y
    simpa only [reflectionLinear_apply] using reflection_pair A X Y hA.ne'
  have hradius (q : E) : radius (affine v a q) =
      -lorentz (xi l n q ᵥ* M) (xi l n q ᵥ* M) := by
    dsimp only [v,a]
    rw [affine_forward]
    exact actual_radius M (reflectionLinear A) hpair _ (hplane q)
  have hz : ∀ q ∈ parameterTriangle,
      Complex.measurableEquivPi (z q : ℂ) = chart (affine v a q) := by
    intro q hq
    obtain ⟨hzre,hzim,hpoint⟩ := Classical.choose_spec (hchart q hq)
    rw [hchoice q hq]
    ext j
    fin_cases j
    · change (Classical.choose (hchart q hq)).re =
        (affine v a q) 0 / delta (affine v a q)
      rw [hzre]
      dsimp only [v,a]
      rw [affine_forward]
      rfl
    · change (Classical.choose (hchart q hq)).im =
        Real.sqrt (radius (affine v a q)) / delta (affine v a q)
      rw [hzim, hradius]
      dsimp only [v,a]
      rw [affine_forward]
      rfl
  have hp : ∀ q ∈ parameterTriangle, e (z q) = p q := by
    intro q hq
    change reflectionNative A hA (vertical (z q)) = p q
    rw [hchoice q hq, (Classical.choose_spec (hchart q hq)).2.2,
      hp_original q hq]
  have hK : IsCompact parameterTriangle := by
    exact referenceTriangle_compact
  have himage : p '' parameterTriangle =
      range (fun q : parameterTriangle =>
        f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩) := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq⟩, (hp_original q hq).symm⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q.val,q.property,hp_original q.val q.property⟩
  let F : parameterTriangle → HyperbolicThreeSpace := fun q =>
    f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩
  letI : CompactSpace parameterTriangle := isCompact_iff_compactSpace.mp hK
  have haff : Continuous (affine v a) := continuous_iff_continuousAt.mpr
    (fun q => (affine_hasFDerivAt v a q).continuousAt)
  have hc (j : Fin 3) : Continuous (fun q : parameterTriangle => affine v a q.val j) :=
    (continuous_apply j).comp (haff.comp continuous_subtype_val)
  have hrad : Continuous (fun q : parameterTriangle => radius (affine v a q.val)) :=
    ((hc 2).pow 2).sub ((hc 1).pow 2) |>.sub ((hc 0).pow 2)
  have hdelta : Continuous (fun q : parameterTriangle => delta (affine v a q.val)) :=
    (hc 2).sub (hc 1)
  have hchartc : Continuous (fun q : parameterTriangle => chart (affine v a q.val)) := by
    apply continuous_pi
    intro j
    fin_cases j
    · change Continuous (fun q : parameterTriangle =>
        affine v a q.val 0 / delta (affine v a q.val))
      exact (hc 0).div hdelta (fun q => (hpositive q.val q.property).2.ne')
    · change Continuous (fun q : parameterTriangle =>
        Real.sqrt (radius (affine v a q.val)) / delta (affine v a q.val))
      exact hrad.sqrt.div hdelta (fun q => (hpositive q.val q.property).2.ne')
  have hzcont : Continuous (fun q : parameterTriangle => z q.val) := by
    apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
    have hcomplex : Continuous (fun q : parameterTriangle =>
        Complex.measurableEquivPi.symm (chart (affine v a q.val))) := by
      change Continuous (fun q : parameterTriangle =>
        Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm (chart (affine v a q.val)))
      exact Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm.continuous.comp hchartc
    exact hcomplex.congr (fun q => by
      rw [← hz q.val q.property, MeasurableEquiv.symm_apply_apply]
      rfl)
  have hFcont : Continuous F :=
    (he.continuous.comp hzcont).congr
      (fun q => (hp q.val q.property).trans (hp_original q.val q.property))
  have hFinj : Function.Injective F := by
    intro q r h
    apply Subtype.ext
    apply affine_chart_injOn v a S hs hcols hinj
      (hpositive q.val q.property) (hpositive r.val r.property)
    have heq : e (z q.val) = e (z r.val) := by
      rw [hp q.val q.property, hp r.val r.property,
        hp_original q.val q.property, hp_original r.val r.property]
      exact h
    have hzqr : z q.val = z r.val := he.injective heq
    change chart (affine v a q.val) = chart (affine v a r.val)
    rw [← hz q.val q.property, ← hz r.val r.property, hzqr]
  have harea := native_compact_area_finite e he z v a S hs hcols hinj
    parameterTriangle hK (fun q hq => (hpositive q hq).1)
    (fun q hq => (hpositive q hq).2) hz
  have he_image : (fun q => e (z q)) '' parameterTriangle = p '' parameterTriangle :=
    Set.image_congr hp
  rw [he_image,himage] at harea
  have hcompact : IsCompact (range F) := isCompact_range hFcont
  refine ⟨hFcont.isClosedEmbedding hFinj,harea,?_⟩
  intro phi hphi
  exact hphi.integrableOn_of_subset_isCompact hcompact hcompact.measurableSet
    Subset.rfl harea.ne

end CFMPOriginalExteriorTraceIntegrability435Transient
