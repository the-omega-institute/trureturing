import D5.S3.Geometry.Hyperideal.CFMPOriginalActualInternalFlux435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeReferenceFlux435Transient

/-! Temporary exact application: the sixty original reference-face terms cancel. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Matrix BigOperators ENNReal Classical
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalInternalFaceBridge435V2Transient
open CFMPOriginalInternalNormals435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePlaneNormal435Transient
open CFMPFrameMotion435Transient
open CFMPFrameContinuity435Transient
open CFMPFrameAffineTransport435Transient
open CFMPAnchoredSmoothFrame435Transient
open CFMPOriginalReferenceFluxReadout435Transient

namespace CFMPOriginalReferenceInternalCancellation435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem anchored_reference_internal_flux_sum_zero
    (l0 : Fin 6 → ℝ) (hl0 : ∀ k, 0 < l0 k)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0) :
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let T : Fin 20 → (Fin 3 → ℝ) → Fin 3 → ℝ := fun n =>
      totalFlux M0 (D*M0⁻¹)
        (CFMPOriginalCellsIndependent435Transient.edgeMatrix l0 n)
        (deriv (fun s => CFMPOriginalCellsIndependent435Transient.edgeMatrix (l s) n) t)
        (CFMPOriginalCellsIndependent435Transient.drop
          (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices l0 n 0))
        (deriv (fun s => CFMPOriginalCellsIndependent435Transient.drop
          (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices (l s) n 0)) t)
    (∀ n i, IntegrableOn (fun q => -(T n (referenceInternalFace i q) i))
      parameterTriangle) ∧
    (∑ n : Fin 20, ∑ i : Fin 3,
      ∫ q in parameterTriangle, -(T n (referenceInternalFace i q) i)) = 0 := by
  classical
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let T : Fin 20 → (Fin 3 → ℝ) → Fin 3 → ℝ := fun n =>
    totalFlux M0 (D*M0⁻¹)
      (CFMPOriginalCellsIndependent435Transient.edgeMatrix l0 n)
      (deriv (fun s => CFMPOriginalCellsIndependent435Transient.edgeMatrix (l s) n) t)
      (CFMPOriginalCellsIndependent435Transient.drop
        (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices l0 n 0))
      (deriv (fun s => CFMPOriginalCellsIndependent435Transient.drop
        (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices (l s) n 0)) t)
  let F : (Fin 20 × Fin 3) → parameterTriangle → HyperbolicThreeSpace :=
    fun j q => f ⟨xi l0 j.1 j.2 q.val,
      xi_mem_cutBody l0 hl0 j.1 j.2 q.val q.property⟩
  let mu := (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
  obtain ⟨Phi,hPhi,hcancel⟩ :=
    CFMPOriginalActualInternalFlux435Transient.anchored_actual_internal_flux_sum_zero
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase
  have hG := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0
  have hmeas (j : Fin 20 × Fin 3) : MeasurableSet (range (F j)) :=
    (CFMPOriginalTraceIntegrability435Transient.original_face_continuous_trace_integrable
      l0 hl0 M0 hm0 hG f hf j.1 j.2).1.isClosed_range.measurableSet
  have hface (j : Fin 20 × Fin 3) :
      IntegrableOn (fun q => -(T j.1 (referenceInternalFace j.2 q) j.2))
        parameterTriangle ∧
      (∫ q in parameterTriangle, -(T j.1 (referenceInternalFace j.2 q) j.2)) =
        ∫ z in range (F j), Phi j z ∂mu := by
    obtain ⟨psi,hcont,hint,hiflux,hchange,htrace⟩ :=
      CFMPOriginalNativeReferenceFlux435Transient.anchored_native_reference_face_flux
        l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase j.1 j.2
    have heq : EqOn psi (Phi j) (range (F j)) := by
      rintro z ⟨q,rfl⟩
      exact ((htrace q).2.2).symm.trans ((hPhi j).2.2 q).2.2
    refine ⟨hiflux,?_⟩
    exact hchange.symm.trans (setIntegral_congr_fun (hmeas j) heq)
  refine ⟨fun n i => (hface (n,i)).1,?_⟩
  calc
    _ = ∑ n : Fin 20, ∑ i : Fin 3,
        ∫ z in range (F (n,i)), Phi (n,i) z ∂mu := by
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro i _
      exact (hface (n,i)).2
    _ = 0 := hcancel

end CFMPOriginalReferenceInternalCancellation435Transient
