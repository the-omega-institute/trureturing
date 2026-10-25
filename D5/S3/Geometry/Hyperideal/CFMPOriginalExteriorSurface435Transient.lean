import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorFaceChart435Transient
import D5.S3.Geometry.Hyperideal.CFMPNativePlaneFiniteArea435Transient
import D5.S3.Geometry.Hyperideal.CFMPWeightedNativeCoordinates435Transient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import D5.S3.Geometry.Hyperideal.CFMPNativeSurfaceJacobian435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeCoordinates435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
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

namespace CFMPOriginalExteriorSurface435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

-- Variable weights use the same original closed exterior triangle and native image.
theorem original_exterior_native_surface
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : M4) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Coeff, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0 / (y 3-y 2)) (y 1 / (y 3-y 2)), 1/(y 3-y 2)))
    (n : Fin 20) :
    ∃ rho : E → ℝ, ∃ P : E → HyperbolicThreeSpace,
    ∃ r : E → CFMPLorentzLiftSurface435Transient.V,
    ∃ D : E → E →L[ℝ] CFMPLorentzLiftSurface435Transient.V,
      Measurable rho ∧ Measurable P ∧
      (∀ q ∈ parameterTriangle, 0 < rho q) ∧
      (∀ (q : E) (hq : q ∈ parameterTriangle),
        P q = f ⟨xi l n q, xi_mem_cutBody l hl n q hq⟩) ∧
      (∀ (q : E) (hq : q ∈ parameterTriangle),
        r q = CFMPOriginalNativeCoordinates435Transient.nativeCoordinates
          (f ⟨xi l n q, xi_mem_cutBody l hl n q hq⟩) ∧
        HasFDerivAt r (D q) q ∧
        rho q = Real.sqrt
          (dotProduct ((D q (Pi.single 0 1)) ⨯₃ (D q (Pi.single 1 1)))
            ((D q (Pi.single 0 1)) ⨯₃ (D q (Pi.single 1 1)))) / (r q 2)^2) ∧
      Measure.map P ((volume.restrict parameterTriangle).withDensity
        (fun q => ENNReal.ofReal (rho q))) =
        (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace).restrict
          (range (fun q : parameterTriangle =>
            f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩)) ∧
      ∀ phi : HyperbolicThreeSpace → ℝ,
        IntegrableOn phi (range (fun q : parameterTriangle =>
          f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩))
          (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) →
        IntegrableOn (fun q => rho q * phi (P q)) parameterTriangle ∧
        (∫ p in range (fun q : parameterTriangle =>
          f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩), phi p
          ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
          ∫ q in parameterTriangle, rho q * phi (P q) := by
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
    simpa only [parameterTriangle, referenceTriangle] using referenceTriangle_compact
  have himage : p '' parameterTriangle =
      range (fun q : parameterTriangle =>
        f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩) := by
    ext x
    constructor
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨q,hq⟩, (hp_original q hq).symm⟩
    · rintro ⟨q,rfl⟩
      exact ⟨q.val,q.property,hp_original q.val q.property⟩
  let rho : E → ℝ := fun q =>
    |(augmented a v).det| / (Real.sqrt (radius (affine v a q)))^3
  have hdet : (augmented a v).det ≠ 0 := augmented_det_ne_zero v a S hs hcols hinj
  have haff : Continuous (affine v a) := continuous_iff_continuousAt.mpr
    (fun q => (affine_hasFDerivAt v a q).continuousAt)
  have hc (j : Fin 3) : Continuous (fun q => affine v a q j) :=
    (continuous_apply j).comp haff
  have hrad : Continuous (fun q : E => radius (affine v a q)) :=
    ((hc 2).pow 2).sub ((hc 1).pow 2) |>.sub ((hc 0).pow 2)
  have hdelta : Continuous (fun q : E => delta (affine v a q)) := (hc 2).sub (hc 1)
  have hrhomeas : Measurable rho :=
    measurable_const.div (hrad.sqrt.pow 3).measurable
  have hrhononneg (q : E) : 0 ≤ rho q :=
    div_nonneg (abs_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) 3)
  have hrhopos (q : E) (hq : q ∈ parameterTriangle) : 0 < rho q :=
    div_pos (abs_pos.mpr hdet) (pow_pos (Real.sqrt_pos.mpr (hpositive q hq).1) 3)
  have hchartmeas : Measurable (fun q => chart (affine v a q)) := by
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · change Measurable (fun q => affine v a q 0 / delta (affine v a q))
      exact (hc 0).measurable.div hdelta.measurable
    · change Measurable (fun q => Real.sqrt (radius (affine v a q)) / delta (affine v a q))
      exact hrad.sqrt.measurable.div hdelta.measurable
  have hof : Measurable (fun c : ℂ => UpperHalfPlane.ofComplex c) := by
    apply UpperHalfPlane.measurableEmbedding_coe.measurable_comp_iff.mp
    have heq : (fun c : ℂ => (UpperHalfPlane.ofComplex c : ℂ)) =
        (fun c : ℂ => if 0 < c.im then c else
          ((Classical.choice inferInstance : UpperHalfPlane) : ℂ)) := by
      funext c
      rw [UpperHalfPlane.ofComplex_apply_eq_ite]
      split_ifs <;> rfl
    change Measurable (fun c : ℂ => (UpperHalfPlane.ofComplex c : ℂ))
    rw [heq]
    exact measurable_id.piecewise
      (isOpen_lt continuous_const Complex.continuous_im).measurableSet measurable_const
  let P : E → HyperbolicThreeSpace := fun q => e
    (UpperHalfPlane.ofComplex (Complex.measurableEquivPi.symm (chart (affine v a q))))
  have hPmeas : Measurable P := he.continuous.measurable.comp
    (hof.comp (Complex.measurableEquivPi.symm.measurable.comp hchartmeas))
  have hP (q : E) (hq : q ∈ parameterTriangle) : P q = p q := by
    dsimp only [P]
    rw [← hz q hq]
    simp only [MeasurableEquiv.symm_apply_apply, UpperHalfPlane.ofComplex_apply]
    exact hp q hq
  have hw (weight : HyperbolicThreeSpace → ℝ≥0∞) :
      (∫⁻ x in range (fun q : parameterTriangle =>
        f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩), weight x
        ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      ∫⁻ q in parameterTriangle, ENNReal.ofReal (rho q) * weight (P q) := by
    have hb := native_plane_weighted_coordinates e he z v a S hs hcols hinj
      parameterTriangle hK.measurableSet
      (fun q hq => (hpositive q hq).1)
      (fun q hq => (hpositive q hq).2) hz weight
    have he_image : (fun q => e (z q)) '' parameterTriangle = p '' parameterTriangle :=
      Set.image_congr hp
    rw [he_image,himage] at hb
    refine hb.trans ?_
    apply setLIntegral_congr_fun hK.measurableSet
    intro q hq
    dsimp only [rho]
    rw [hp q hq, hP q hq]
  let nu : Measure E := (volume.restrict parameterTriangle).withDensity
    (fun q => ENNReal.ofReal (rho q))
  let target : Measure HyperbolicThreeSpace :=
    (Measure.euclideanHausdorffMeasure 2).restrict
      (range (fun q : parameterTriangle =>
        f ⟨xi l n q.val, xi_mem_cutBody l hl n q.val q.property⟩))
  let T : E →L[ℝ] (Fin 4 → ℝ) :=
    (ContinuousLinearMap.proj (0 : Fin 2) : E →L[ℝ] ℝ).smulRight (direction l n 0) +
      (ContinuousLinearMap.proj (1 : Fin 2) : E →L[ℝ] ℝ).smulRight (direction l n 1)
  let r : E → CFMPLorentzLiftSurface435Transient.V := fun q =>
    CFMPNativePullbackMetric435Transient.nativeMap (xi l n q ᵥ* M)
  let D : E → E →L[ℝ] CFMPLorentzLiftSurface435Transient.V := fun q =>
    ((CFMPNativePullbackMetric435Transient.nativeMatrix (xi l n q ᵥ* M)).mulVecLin.toContinuousLinearMap).comp
      (M.vecMulLinear.toContinuousLinearMap.comp T)
  have hxi (q : E) : HasFDerivAt (xi l n) T q := by
    have h := ((hasFDerivAt_const (base l n) q).add
      ((ContinuousLinearMap.proj (0 : Fin 2) : E →L[ℝ] ℝ).hasFDerivAt.smul_const
        (direction l n 0))).add
      ((ContinuousLinearMap.proj (1 : Fin 2) : E →L[ℝ] ℝ).hasFDerivAt.smul_const
        (direction l n 1))
    simp only [zero_add] at h
    convert h using 1 <;> rfl
  have hD (q : E) (hq : q ∈ parameterTriangle) : HasFDerivAt r (D q) q := by
    obtain ⟨hr,hd,hpoint⟩ :=
      CFMPOriginalNativeCoordinates435Transient.original_native_coordinates l hl M f hf
        ⟨xi l n q,xi_mem_cutBody l hl n q hq⟩
    exact (CFMPOriginalNativeCoordinates435Transient.coefficient_coordinate_hasFDerivAt
      M (xi l n q) hr hd.ne').comp q (hxi q)
  have hDbasis (q : E) (j : Fin 2) :
      D q (Pi.single j 1) =
        (CFMPNativePullbackMetric435Transient.nativeMatrix (xi l n q ᵥ* M)).mulVec
          (direction l n j ᵥ* M) := by
    have hT : T (Pi.single j 1) = direction l n j := by
      fin_cases j <;> simp [T,Pi.single_apply]
    change (CFMPNativePullbackMetric435Transient.nativeMatrix (xi l n q ᵥ* M)).mulVec
      ((T (Pi.single j 1)) ᵥ* M) = _
    rw [hT]
  have hgeometry (q : E) (hq : q ∈ parameterTriangle) :
      r q = CFMPOriginalNativeCoordinates435Transient.nativeCoordinates
          (f ⟨xi l n q,xi_mem_cutBody l hl n q hq⟩) ∧
        HasFDerivAt r (D q) q ∧
        rho q = Real.sqrt
          (dotProduct ((D q (Pi.single 0 1)) ⨯₃ (D q (Pi.single 1 1)))
            ((D q (Pi.single 0 1)) ⨯₃ (D q (Pi.single 1 1)))) / (r q 2)^2 := by
    obtain ⟨hr,hd,hpoint⟩ :=
      CFMPOriginalNativeCoordinates435Transient.original_native_coordinates l hl M f hf
        ⟨xi l n q,xi_mem_cutBody l hl n q hq⟩
    refine ⟨hpoint.symm,hD q hq,?_⟩
    let R := reflectionLinear A
    have hbase : R (base l n ᵥ* M) 1 = 0 := by simpa [xi] using hplane 0
    have hb : R (direction l n 0 ᵥ* M) 1 = 0 := by
      have h := hplane ![1,0]
      simpa [xi,Matrix.add_vecMul,Matrix.smul_vecMul,map_add,map_smul,hbase,R] using h
    have hc : R (direction l n 1 ᵥ* M) 1 = 0 := by
      have h := hplane ![0,1]
      simpa [xi,Matrix.add_vecMul,Matrix.smul_vecMul,map_add,map_smul,hbase,R] using h
    have hsurface := CFMPNativeSurfaceJacobian435Transient.native_surface_jacobian
      (xi l n q ᵥ* M) (direction l n 0 ᵥ* M) (direction l n 1 ᵥ* M)
      hr hd.ne' R hpair (hplane q) hb hc
    have hcolumns : CFMPNativeSurfaceJacobian435Transient.planeColumns
        (R (direction l n 0 ᵥ* M)) (R (direction l n 1 ᵥ* M)) = a := by
      ext k j
      fin_cases k <;> fin_cases j <;> rfl
    have hdrop : CFMPNativeSurfaceJacobian435Transient.dropPlane
        (R (xi l n q ᵥ* M)) = affine v a q := by
      dsimp only [v,a]
      rw [affine_forward]
      rfl
    have hradius' : CFMPNativePullbackMetric435Transient.radius (xi l n q ᵥ* M) =
        radius (affine v a q) := (hradius q).symm
    rw [hcolumns,hdrop,affine_augmented_det,hradius'] at hsurface
    rw [hDbasis q 0,hDbasis q 1]
    exact hsurface.symm
  have hJmeas : Measurable (fun q => ENNReal.ofReal (rho q)) :=
    ENNReal.measurable_ofReal.comp hrhomeas
  have hmap : Measure.map P nu = target := by
    apply Measure.ext_of_lintegral
    intro weight hweight
    rw [lintegral_map hweight hPmeas]
    change (∫⁻ q, (weight ∘ P) q ∂(volume.restrict parameterTriangle).withDensity
      (fun q => ENNReal.ofReal (rho q))) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ hJmeas (hweight.comp hPmeas)]
    exact (hw weight).symm
  refine ⟨rho,P,r,D,hrhomeas,hPmeas,hrhopos,?_,hgeometry,hmap,?_⟩
  · intro q hq
    exact (hP q hq).trans (hp_original q hq)
  · intro phi hphi
    have hi : Integrable phi (Measure.map P nu) := by
      rw [hmap]
      exact hphi
    have hip : Integrable (phi ∘ P) nu := hi.comp_measurable hPmeas
    have hfinite : ∀ᵐ q ∂(volume.restrict parameterTriangle : Measure E),
        ENNReal.ofReal (rho q) < ∞ := Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
    have hint := (integrable_withDensity_iff_integrable_smul₀'
      hJmeas.aemeasurable hfinite).mp hip
    have hisource : IntegrableOn (fun q => rho q * phi (P q)) parameterTriangle := by
      change Integrable (fun q => rho q * phi (P q)) (volume.restrict parameterTriangle)
      have hfun : (fun q => (ENNReal.ofReal (rho q)).toReal • (phi ∘ P) q) =
          (fun q => rho q * phi (P q)) := by
        funext q
        change (ENNReal.ofReal (rho q)).toReal • phi (P q) = rho q * phi (P q)
        rw [ENNReal.toReal_ofReal (hrhononneg q)]
        rfl
      rw [hfun] at hint
      exact hint
    refine ⟨hisource,?_⟩
    calc
      _ = ∫ x, phi x ∂Measure.map P nu := by rw [hmap]
      _ = ∫ q, phi (P q) ∂nu := integral_map hPmeas.aemeasurable hi.aestronglyMeasurable
      _ = _ := by
        dsimp only [nu]
        rw [integral_withDensity_eq_integral_toReal_smul₀ hJmeas.aemeasurable hfinite]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun q => by
          change (ENNReal.ofReal (rho q)).toReal • phi (P q) = rho q * phi (P q)
          rw [ENNReal.toReal_ofReal (hrhononneg q)]
          rfl)

end CFMPOriginalExteriorSurface435Transient
