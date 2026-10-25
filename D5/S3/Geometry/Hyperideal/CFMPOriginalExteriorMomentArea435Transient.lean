import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorCofactorSurface435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalMomentIntegrable435Transient
import D5.S3.Geometry.Hyperideal.CFMPPlaneBoundaryMoment435Transient

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient CFMPNativePullbackMetric435Transient
open CFMPOriginalExteriorFaceChart435Transient
open CFMPActualPlaneIsometry435Transient
open CFMPPlaneMomentDivergence435Transient CFMPPlaneEdgeCofactor435Transient
open CFMPPlaneDualConormal435Transient CFMPReferenceSimplexDivergence435Transient
open CFMPOriginalInternalMomentArea435Transient (affine_pairings)
open CFMPOriginalInternalMomentIntegrable435Transient (continuous_lift_pairing)

namespace CFMPOriginalExteriorMomentArea435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

def faceV0 (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ) (n : Fin 20) : W :=
  base l n ᵥ* M

def faceB (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (n : Fin 20) : W := direction l n 0 ᵥ* M

def faceC (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (n : Fin 20) : W := direction l n 1 ᵥ* M

def faceImage (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (f : cutBody l → HyperbolicThreeSpace) (n : Fin 20) :
    Set HyperbolicThreeSpace :=
  range (fun q : parameterTriangle =>
    f ⟨xi l n q.val,xi_mem_cutBody l hl n q.val q.property⟩)

def areaCoefficient (l : Fin 6 → ℝ) (M : Matrix (Fin 4) (Fin 4) ℝ)
    (n : Fin 20) : ℝ :=
  |M.det| * Real.sqrt (lorentz
    (CFMPOriginalExteriorNativeNormal435Transient.raw l M n)
    (CFMPOriginalExteriorNativeNormal435Transient.raw l M n))

theorem original_exterior_moment_integrable
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (A : W) :
    IntegrableOn (fun p => lorentz (lift p) A) (faceImage l hl f n)
      (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) := by
  obtain ⟨rho,P,r,D,hrho,hP,hpos,hpoint,hgeometry,hmap,hdensity,hsub⟩ :=
    CFMPOriginalExteriorCofactorSurface435Transient.original_exterior_native_cofactor_surface
      l hl M hM hG f hf n
  let U : (Fin 2 → ℝ) → W := fun q => xi l n q ᵥ* M
  let phi : HyperbolicThreeSpace → ℝ := fun p => lorentz (lift p) A
  let F : (Fin 2 → ℝ) → ℝ := fun q =>
    areaCoefficient l M n / (Real.sqrt (radius (U q)))^3 *
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
      ⟨xi l n q,xi_mem_cutBody l hl n q hq⟩).1
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
    change F q = (ENNReal.ofReal (rho q)).toReal * phi (P q)
    rw [ENNReal.toReal_ofReal (hpos q hq).le]
    rw [hdensity q hq,hpoint q hq]
    dsimp only [phi]
    rw [original_frame_normalized_lift l M hG f hf]
    rfl
  have hfinite : ∀ᵐ q ∂(volume.restrict parameterTriangle : Measure (Fin 2 → ℝ)),
      ENNReal.ofReal (rho q) < (⊤ : ENNReal) :=
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

-- The same original realization and the same cofactor density occur in both integrals.
-- Integrability follows from the compact parameter triangle and the same pushforward.
theorem original_exterior_native_moment
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (a : Fin 3 → ℝ) :
    (∫ p in faceImage l hl f n,
      lorentz (lift p)
        (basisPoint (faceV0 l M n) (faceB l M n) (faceC l M n) a)
      ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
    ∫ z in CFMPSimplexDirection435Transient.triangle 1,
      areaCoefficient l M n *
        moment (pairingEntries (faceV0 l M n) (faceB l M n) (faceC l M n)) a z /
        (Q (pairingEntries (faceV0 l M n) (faceB l M n) (faceC l M n)) z)^2 := by
  obtain ⟨rho,P,r,D,hrho,hP,hpos,hpoint,hgeometry,hmap,hdensity,hsub⟩ :=
    CFMPOriginalExteriorCofactorSurface435Transient.original_exterior_native_cofactor_surface
      l hl M hM hG f hf n
  have hint := original_exterior_moment_integrable l hl M hM hG f hf n
    (basisPoint (faceV0 l M n) (faceB l M n) (faceC l M n) a)
  have hs := (hsub
    (fun p => lorentz (lift p)
      (basisPoint (faceV0 l M n) (faceB l M n) (faceC l M n) a)) hint).2
  change (∫ p in faceImage l hl f n,
    lorentz (lift p)
      (basisPoint (faceV0 l M n) (faceB l M n) (faceC l M n) a)
    ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) = _ at hs
  rw [hs,triangle_integral]
  apply setIntegral_congr_fun (CFMPSimplexDirection435Transient.triangle_compact 1).measurableSet
  intro z hz
  have hq : pack2 z ∈ parameterTriangle := hz
  have hraw : xi l n (pack2 z) ᵥ* M =
      faceV0 l M n+z.1 • faceB l M n+z.2 • faceC l M n := by
    simp only [xi,Matrix.add_vecMul,Matrix.smul_vecMul,pack2,
      Matrix.cons_val_zero,Matrix.cons_val_one,faceV0,faceB,faceC]
  have hpair := affine_pairings (faceV0 l M n) (faceB l M n)
    (faceC l M n) a z
  have hrad := (CFMPOriginalNativeCoordinates435Transient.original_native_coordinates
    l hl M f hf ⟨xi l n (pack2 z),xi_mem_cutBody l hl n (pack2 z) hq⟩).1
  have hQ : 0 < Q (pairingEntries (faceV0 l M n) (faceB l M n)
      (faceC l M n)) z := by
    rw [hraw,hpair.1] at hrad
    exact hrad
  have hroot := Real.sq_sqrt hQ.le
  have hsqrt : Real.sqrt (Q (pairingEntries (faceV0 l M n) (faceB l M n)
      (faceC l M n)) z) ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  dsimp only
  rw [hdensity (pack2 z) hq,hpoint (pack2 z) hq,
    original_frame_normalized_lift l M hG f hf]
  change (areaCoefficient l M n /
      (Real.sqrt (radius (xi l n (pack2 z) ᵥ* M)))^3) *
    lorentz ((Real.sqrt (radius (xi l n (pack2 z) ᵥ* M)))⁻¹ •
      (xi l n (pack2 z) ᵥ* M))
      (basisPoint (faceV0 l M n) (faceB l M n) (faceC l M n) a) = _
  have hscale (s : ℝ) (U A : W) : lorentz (s • U) A = s*lorentz U A := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  rw [hscale,hraw,hpair.1,hpair.2]
  field_simp [hsqrt,hQ.ne']
  have hfour := congrArg (fun t : ℝ => t ^ 2) hroot
  rw [← pow_mul] at hfour
  rw [hfour]
  ring

end CFMPOriginalExteriorMomentArea435Transient

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``CFMPOriginalExteriorMomentArea435Transient.original_exterior_moment_integrable,
      ``CFMPOriginalExteriorMomentArea435Transient.original_exterior_native_moment] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP515 checked target missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP515 disallowed axiom {ax}"
    Lean.logInfo m!"CFMP515 CHECKED {name} axioms={axioms}"
