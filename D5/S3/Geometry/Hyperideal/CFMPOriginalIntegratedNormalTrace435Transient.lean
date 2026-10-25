import D5.S3.Geometry.Hyperideal.CFMPOriginalActualTraceIntegrability435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalCofactorSurface435Transient

/-! Temporary exact application: the actual moving trace and its coefficient integral. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix BigOperators ENNReal Classical
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalFacePairing435Transient
open CFMPOriginalPairedFaceMotion435Transient
open CFMPOriginalInternalFaceBridge435V2Transient
open CFMPOriginalInternalNormals435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePlaneNormal435Transient
open CFMPNativePlaneFiniteArea435Transient
open CFMPFrameMotion435Transient
open CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient

namespace CFMPOriginalIntegratedNormalTrace435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem anchored_integrated_original_face_trace
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
    (n : Fin 20) (i : Fin 3) :
    let F : parameterTriangle → HyperbolicThreeSpace := fun q =>
      f ⟨xi l0 n i q.val,xi_mem_cutBody l0 hl0 n i q.val q.property⟩
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let flux : (Fin 2 → ℝ) → ℝ := fun q =>
      |M0.det| * dotProduct (A l0 n i)
        (deriv (fun s => facePoint (l s) n i q) t +
          field (D * M0⁻¹) (facePoint l0 n i q)) /
        (radius (xi l0 n i q ᵥ* M0))^2
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
          (ambient (frame M0 (l s)) (facePoint (l s) n i q.val))
        c t = nativeCoordinates (F q) ∧
        DifferentiableAt ℝ c t ∧
        dotProduct (deriv c t)
          (coordinateNormal (nativeCoordinates (F q)) (unit M0 (A l0 n i))) /
            (nativeCoordinates (F q) 2)^2 = phi (F q) := by
  classical
  let F : parameterTriangle → HyperbolicThreeSpace := fun q =>
    f ⟨xi l0 n i q.val,xi_mem_cutBody l0 hl0 n i q.val q.property⟩
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let flux : (Fin 2 → ℝ) → ℝ := fun q =>
    |M0.det| * dotProduct (A l0 n i)
      (deriv (fun s => facePoint (l s) n i q) t +
        field (D * M0⁻¹) (facePoint l0 n i q)) /
      (radius (xi l0 n i q ᵥ* M0))^2
  obtain ⟨phi,hcont,hint,htrace⟩ :=
    CFMPOriginalActualTraceIntegrability435Transient.anchored_actual_normal_trace_integrable
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase n i
  have hG := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0
  obtain ⟨rho,P,r,dP,hrho,hP,hpos,hpoint,hgeometry,hmap,hcofactor,hintegral⟩ :=
    CFMPOriginalCofactorSurface435Transient.original_internal_native_cofactor_surface
      l0 hl0 M0 hm0 hG f hf n i
  have hEq : EqOn (fun q => rho q * phi (P q)) flux parameterTriangle := by
    intro q hq
    have hphiq := (htrace ⟨q,hq⟩).1
    change rho q * phi (P q) = flux q
    rw [hpoint q hq,hphiq,hcofactor q hq]
    change (|M0.det| * Real.sqrt (lorentz (raw M0 (A l0 n i))
        (raw M0 (A l0 n i))) /
        (Real.sqrt (radius (xi l0 n i q ᵥ* M0)))^3) *
      (dotProduct (A l0 n i)
        (deriv (fun s => facePoint (l s) n i q) t +
          field (D * M0⁻¹) (facePoint l0 n i q)) /
        (Real.sqrt (radius (xi l0 n i q ᵥ* M0)) *
          Real.sqrt (lorentz (raw M0 (A l0 n i)) (raw M0 (A l0 n i))))) = flux q
    have hr := (original_native_coordinates l0 hl0 M0 f hf
      ⟨xi l0 n i q,xi_mem_cutBody l0 hl0 n i q hq⟩).1
    have hs : Real.sqrt (radius (xi l0 n i q ᵥ* M0)) ≠ 0 :=
      (Real.sqrt_pos.mpr hr).ne'
    have hb : Real.sqrt (lorentz (raw M0 (A l0 n i)) (raw M0 (A l0 n i))) ≠ 0 :=
      (Real.sqrt_pos.mpr (raw_spacelike l0 hl0 M0 hm0 f hf n i)).ne'
    calc
      _ = |M0.det| * dotProduct (A l0 n i)
          (deriv (fun s => facePoint (l s) n i q) t +
            field (D * M0⁻¹) (facePoint l0 n i q)) /
          ((Real.sqrt (radius (xi l0 n i q ᵥ* M0)))^2)^2 := by
        field_simp [hs,hb]
        <;> ring
      _ = flux q := by rw [Real.sq_sqrt hr.le]
  have hK : MeasurableSet parameterTriangle :=
    (show IsCompact parameterTriangle from
      CFMPNativePlaneFiniteArea435Transient.referenceTriangle_compact).measurableSet
  obtain ⟨hip,hchange⟩ := hintegral phi hint
  refine ⟨phi,hcont,hint,hip.congr_fun hEq hK,?_,?_⟩
  · exact hchange.trans (setIntegral_congr_fun hK hEq)
  · intro q
    exact (htrace q).2

end CFMPOriginalIntegratedNormalTrace435Transient
