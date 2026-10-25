import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorIntegratedNormalTrace435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalReferenceFluxReadout435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorActualTraceIntegrability435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorCofactorSurface435Transient

/-! Temporary exact application: the actual moving trace and its coefficient integral. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix BigOperators ENNReal Classical
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPAnchoredOriginalExteriorFaceMotion435Transient
open CFMPOriginalExteriorFaceChart435Transient
open CFMPOriginalExteriorNativeNormal435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePlaneNormal435Transient
open CFMPNativePlaneFiniteArea435Transient
open CFMPFrameMotion435Transient
open CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient

namespace CFMPOriginalExteriorNativeReferenceFlux435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem anchored_native_reference_face_flux
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0)
    (n : Fin 20) :
    let F : parameterTriangle → HyperbolicThreeSpace := fun q =>
      f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let E := deriv (fun s => CFMPOriginalCellsIndependent435Transient.edgeMatrix (l s) n) t
    let v := deriv (fun s => CFMPOriginalCellsIndependent435Transient.drop
      (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices (l s) n 0)) t
    let T := CFMPFrameAffineTransport435Transient.totalFlux M0 (D*M0⁻¹)
      (CFMPOriginalCellsIndependent435Transient.edgeMatrix l0 n) E
      (CFMPOriginalCellsIndependent435Transient.drop
        (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices l0 n 0)) v
    let flux : (Fin 2 → ℝ) → ℝ := fun q => (∑ j : Fin 3,T (![1-q 0-q 1,q 0,q 1]) j)
    ∃ phi : HyperbolicThreeSpace → ℝ,
      ContinuousOn phi (range F) ∧
      IntegrableOn phi (range F)
        (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) ∧
      IntegrableOn flux parameterTriangle ∧
      (∫ p in range F,phi p
          ∂(Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)) =
        ∫ q in parameterTriangle,flux q ∧
      ∀ q : parameterTriangle,
        let c : ℝ → Fin 3 → ℝ := fun s => nativeMap
          (ambient (frame M0 (l s)) (facePoint (l s) n q.val))
        c t = nativeCoordinates (F q) ∧
        DifferentiableAt ℝ c t ∧
        dotProduct (deriv c t)
          (coordinateNormal (nativeCoordinates (F q)) (unit l0 M0 n)) /
            (nativeCoordinates (F q) 2)^2 = phi (F q) := by
  classical
  let F : parameterTriangle → HyperbolicThreeSpace := fun q =>
    f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let E := deriv (fun s => CFMPOriginalCellsIndependent435Transient.edgeMatrix (l s) n) t
  let v := deriv (fun s => CFMPOriginalCellsIndependent435Transient.drop
    (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices (l s) n 0)) t
  let T := CFMPFrameAffineTransport435Transient.totalFlux M0 (D*M0⁻¹)
    (CFMPOriginalCellsIndependent435Transient.edgeMatrix l0 n) E
    (CFMPOriginalCellsIndependent435Transient.drop
      (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices l0 n 0)) v
  let flux : (Fin 2 → ℝ) → ℝ := fun q => (∑ j : Fin 3,T (![1-q 0-q 1,q 0,q 1]) j)
  let coeff : (Fin 2 → ℝ) → ℝ := fun q =>
    |M0.det| * dotProduct (outwardCoefficient l0 n)
      (deriv (fun s => facePoint (l s) n q) t +
        field (D * M0⁻¹) (facePoint l0 n q)) /
      (radius (xi l0 n q ᵥ* M0))^2
  obtain ⟨phi,hcont,hint,hicoeff,hchange,htrace⟩ :=
    CFMPOriginalExteriorIntegratedNormalTrace435Transient.anchored_integrated_original_face_trace
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase n
  have hpositive : ∀ k, 0 < l t k := by simpa only [hbase] using hl0
  have hread : EqOn flux coeff parameterTriangle := by
    intro q hq
    have h := CFMPOriginalReferenceFluxReadout435Transient.actual_exterior_reference_trace
      M0 (D*M0⁻¹) l t hl.differentiableAt hpositive n q
    simpa only [hbase] using h
  have hK : MeasurableSet parameterTriangle :=
    (show IsCompact parameterTriangle from
      CFMPNativePlaneFiniteArea435Transient.referenceTriangle_compact).measurableSet
  refine ⟨phi,hcont,hint,hicoeff.congr_fun hread.symm hK,?_,htrace⟩
  exact hchange.trans (setIntegral_congr_fun hK hread.symm)

end CFMPOriginalExteriorNativeReferenceFlux435Transient
