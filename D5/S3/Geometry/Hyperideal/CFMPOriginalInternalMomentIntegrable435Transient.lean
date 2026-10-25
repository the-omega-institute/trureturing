import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalNativeMoment435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.HyperbolicTopology
open CFMPLorentzLiftSurface435Transient CFMPNativePullbackMetric435Transient
open CFMPOriginalInternalFaceBridge435V2Transient CFMPActualPlaneIsometry435Transient
open CFMPOriginalInternalMomentArea435Transient CFMPOriginalInternalNativeMoment435Transient
open CFMPPlaneDualConormal435Transient

namespace CFMPOriginalInternalMomentIntegrable435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem continuous_lift : Continuous (lift : HyperbolicThreeSpace → W) := by
  have hc : Continuous (fun p : HyperbolicThreeSpace => p.coordinates) :=
    coordinatesHomeomorph.continuous
  have hxy : Continuous (fun p : HyperbolicThreeSpace => p.coordinates.val.fst) :=
    (WithLp.continuous_fst 2 ℂ ℝ).comp (continuous_subtype_val.comp hc)
  have hx := Complex.continuous_re.comp hxy
  have hy := Complex.continuous_im.comp hxy
  have ht : Continuous (fun p : HyperbolicThreeSpace => height p.coordinates) :=
    (WithLp.continuous_snd 2 ℂ ℝ).comp (continuous_subtype_val.comp hc)
  have ht0 (p : HyperbolicThreeSpace) : height p.coordinates ≠ 0 :=
    p.coordinates.property.ne'
  have htwo (p : HyperbolicThreeSpace) : 2*height p.coordinates ≠ 0 :=
    mul_ne_zero (by norm_num) (ht0 p)
  have hQ := ((hx.pow 2).add (hy.pow 2)).add (ht.pow 2)
  apply continuous_pi
  intro k
  fin_cases k
  · exact hx.div ht ht0
  · exact hy.div ht ht0
  · exact (hQ.sub continuous_const).div (continuous_const.mul ht) htwo
  · exact (hQ.add continuous_const).div (continuous_const.mul ht) htwo

theorem continuous_lift_pairing (A : W) :
    Continuous (fun p : HyperbolicThreeSpace => lorentz (lift p) A) := by
  have hc (k : Fin 4) : Continuous (fun p : HyperbolicThreeSpace => lift p k) :=
    (continuous_apply k).comp continuous_lift
  unfold lorentz
  fun_prop

-- Integrability is transferred from the actual compact coefficient triangle.
-- Ambient H2 measure on the three-dimensional space is not assumed locally finite.
theorem original_internal_moment_integrable
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) (A : W) :
    IntegrableOn (fun p => lorentz (lift p) A) (faceImage l hl f n i)
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) := by
  obtain ⟨rho,P,r,D,hrho,hP,hpos,hpoint,hgeometry,hmap,hdensity,hsub⟩ :=
    CFMPOriginalCofactorSurface435Transient.original_internal_native_cofactor_surface
      l hl M hM hG f hf n i
  let U : (Fin 2 → ℝ) → W := fun q => xi l n i q ᵥ* M
  let phi : HyperbolicThreeSpace → ℝ := fun p => lorentz (lift p) A
  let F : (Fin 2 → ℝ) → ℝ := fun q =>
    areaCoefficient l M n i / (Real.sqrt (radius (U q)))^3 *
      lorentz ((Real.sqrt (radius (U q)))⁻¹ • U q) A
  have hK : IsCompact parameterTriangle :=
    CFMPNativePlaneFiniteArea435Transient.referenceTriangle_compact
  have hU : Continuous U := by
    apply continuous_pi
    intro k
    simp only [U,xi,Matrix.vecMul,dotProduct,Fin.sum_univ_four,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    fun_prop
  have hrad : Continuous (fun q => radius (U q)) := by
    have hc (k : Fin 4) : Continuous (fun q => U q k) := (continuous_apply k).comp hU
    unfold radius lorentz
    fun_prop
  have hr (q : Fin 2 → ℝ) (hq : q ∈ parameterTriangle) : 0 < radius (U q) :=
    (CFMPOriginalNativeCoordinates435Transient.original_native_coordinates l hl M f hf
      ⟨xi l n i q,xi_mem_cutBody l hl n i q hq⟩).1
  have hs (q : Fin 2 → ℝ) (hq : q ∈ parameterTriangle) :
      Real.sqrt (radius (U q)) ≠ 0 := (Real.sqrt_pos.mpr (hr q hq)).ne'
  have hn : ContinuousOn (fun q => (Real.sqrt (radius (U q)))⁻¹ • U q)
      parameterTriangle :=
    (hrad.sqrt.continuousOn.inv₀ hs).smul hU.continuousOn
  have hp : ContinuousOn
      (fun q => lorentz ((Real.sqrt (radius (U q)))⁻¹ • U q) A) parameterTriangle := by
    have hc (k : Fin 4) : ContinuousOn
        (fun q => ((Real.sqrt (radius (U q)))⁻¹ • U q) k) parameterTriangle :=
      (continuous_apply k).continuousOn.comp hn (fun _ _ => mem_univ _)
    unfold lorentz
    fun_prop
  have hF : IntegrableOn F parameterTriangle :=
    ((continuousOn_const.div (hrad.sqrt.continuousOn.pow 3)
      (fun q hq => pow_ne_zero 3 (hs q hq))).mul hp).integrableOn_compact hK
  let nu : Measure (Fin 2 → ℝ) :=
    (volume.restrict parameterTriangle).withDensity (fun q => ENNReal.ofReal (rho q))
  have hweighted : IntegrableOn
      (fun q => (ENNReal.ofReal (rho q)).toReal • (phi ∘ P) q) parameterTriangle := by
    apply hF.congr_fun _ hK.measurableSet
    intro q hq
    rw [ENNReal.toReal_ofReal (hpos q hq).le]
    change F q = rho q * phi (P q)
    rw [hdensity q hq,hpoint q hq]
    dsimp only [phi]
    rw [original_frame_normalized_lift l M hG f hf]
    rfl
  have hfinite : ∀ᵐ q ∂(volume.restrict parameterTriangle : Measure (Fin 2 → ℝ)),
      ENNReal.ofReal (rho q) < ∞ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  have hip : Integrable (phi ∘ P) nu :=
    (integrable_withDensity_iff_integrable_smul₀'
      (ENNReal.measurable_ofReal.comp hrho).aemeasurable hfinite).mpr hweighted
  have hphi : AEStronglyMeasurable phi (Measure.map P nu) :=
    (continuous_lift_pairing A).measurable.aestronglyMeasurable
  have hi : Integrable phi (Measure.map P nu) :=
    (integrable_map_measure hphi hP.aemeasurable).mpr hip
  rw [hmap] at hi
  exact hi

theorem original_realization_injective
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2))) :
    Function.Injective f := by
  have hpoint (w : cutBody l) : lift (f w) = radial l w.val ᵥ* M := by
    obtain ⟨y,hy,hu,ht,hc⟩ := hf w
    exact (lift_of_coordinates (f w) y hu ht hc).trans hy
  intro v w he
  have h := ((hpoint v).symm.trans (congrArg lift he)).trans (hpoint w)
  have hr := congrArg (fun z : W => z ᵥ* M⁻¹) h
  simp only [Matrix.vecMul_vecMul,
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),Matrix.vecMul_one] at hr
  apply Subtype.ext
  exact (shared_radial_body l hl).2.2.2.2.2.1 v.property w.property hr

-- No extra native integrability or realization-injectivity assumption is needed.
theorem original_internal_native_boundary_moment_complete
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) (a : Fin 3 → ℝ) :
    2*(∫ p in faceImage l hl f n i,
      lorentz (lift p)
        (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
      ∑ e : Fin 3,
        lorentz (basisPoint (faceV0 l M n) (faceB l M n i) (faceC l M n i) a)
          (dualUnit (faceV0 l M n) (faceB l M n i) (faceC l M n i) e) *
        dist (f (CFMPOriginalTriangleBoundary435Transient.edgeStart (facePoints l hl n i) e))
          (f (CFMPOriginalTriangleBoundary435Transient.edgeEnd (facePoints l hl n i) e)) := by
  exact original_internal_native_boundary_moment l hl M hM hG f
    (original_realization_injective l hl M hM f hf) hf n i a
    (original_internal_moment_integrable l hl M hM hG f hf n i _)

end CFMPOriginalInternalMomentIntegrable435Transient
