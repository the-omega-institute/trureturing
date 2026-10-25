import D5.S3.Geometry.Hyperideal.CFMPOriginalReferenceInternalCancellation435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalReferenceFluxRegularity435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorNativeReferenceFlux435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorIntegratedNormalTrace435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalReferenceFluxReadout435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorActualTraceIntegrability435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorCofactorSurface435Transient

/-! Temporary exact assembly of the twenty-cell reference divergence as actual exterior flux. -/
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

namespace CFMPOriginalBoundaryFlux435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem anchored_actual_boundary_flux
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
    let F : Fin 20 → parameterTriangle → HyperbolicThreeSpace := fun n q =>
      f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let T : Fin 20 → (Fin 3 → ℝ) → Fin 3 → ℝ := fun n =>
      CFMPFrameAffineTransport435Transient.totalFlux M0 (D*M0⁻¹)
        (CFMPOriginalCellsIndependent435Transient.edgeMatrix l0 n)
        (deriv (fun s => CFMPOriginalCellsIndependent435Transient.edgeMatrix (l s) n) t)
        (CFMPOriginalCellsIndependent435Transient.drop
          (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices l0 n 0))
        (deriv (fun s => CFMPOriginalCellsIndependent435Transient.drop
          (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices (l s) n 0)) t)
    let c : Fin 20 → parameterTriangle → ℝ → Fin 3 → ℝ := fun n q s =>
      nativeMap (ambient (frame M0 (l s)) (facePoint (l s) n q.val))
    let mu := (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
    ∃ Phi : Fin 20 → HyperbolicThreeSpace → ℝ,
      (∀ n, ContinuousOn (Phi n) (range (F n)) ∧
        IntegrableOn (Phi n) (range (F n)) mu ∧
        ∀ q : parameterTriangle,
          c n q t = nativeCoordinates (F n q) ∧
          DifferentiableAt ℝ (c n q) t ∧
          dotProduct (deriv (c n q) t)
            (coordinateNormal (nativeCoordinates (F n q)) (unit l0 M0 n)) /
              (nativeCoordinates (F n q) 2)^2 = Phi n (F n q)) ∧
      (∑ n : Fin 20, ∫ u in CFMPReferenceSimplexDivergence435Transient.simplex,
        CFMPFrameMotion435Transient.divergence (T n) u) =
      ∑ n : Fin 20, ∫ z in range (F n), Phi n z ∂mu := by
  classical
  let F : Fin 20 → parameterTriangle → HyperbolicThreeSpace := fun n q =>
    f ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let T : Fin 20 → (Fin 3 → ℝ) → Fin 3 → ℝ := fun n =>
    CFMPFrameAffineTransport435Transient.totalFlux M0 (D*M0⁻¹)
      (CFMPOriginalCellsIndependent435Transient.edgeMatrix l0 n)
      (deriv (fun s => CFMPOriginalCellsIndependent435Transient.edgeMatrix (l s) n) t)
      (CFMPOriginalCellsIndependent435Transient.drop
        (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices l0 n 0))
      (deriv (fun s => CFMPOriginalCellsIndependent435Transient.drop
        (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices (l s) n 0)) t)
  let c : Fin 20 → parameterTriangle → ℝ → Fin 3 → ℝ := fun n q s =>
    nativeMap (ambient (frame M0 (l s)) (facePoint (l s) n q.val))
  let mu := (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace)
  have hex := fun n : Fin 20 =>
    CFMPOriginalExteriorNativeReferenceFlux435Transient.anchored_native_reference_face_flux
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase n
  choose Phi hcont hint htop hchange htrace using hex
  obtain ⟨hintI,hzero⟩ :=
    CFMPOriginalReferenceInternalCancellation435Transient.anchored_reference_internal_flux_sum_zero
      l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase
  let top : Fin 20 → (Fin 2 → ℝ) → ℝ :=
    fun n q => ∑ i : Fin 3, T n ![1-q 0-q 1,q 0,q 1] i
  let bottom : Fin 20 → Fin 3 → (Fin 2 → ℝ) → ℝ :=
    fun n i q => -(T n
      (CFMPOriginalReferenceFluxReadout435Transient.referenceInternalFace i q) i)
  have hbottom (n : Fin 20) :
      IntegrableOn (fun q => ∑ i : Fin 3, bottom n i q) parameterTriangle :=
    integrable_finsetSum Finset.univ (fun i _ => hintI n i)
  have hcell (n : Fin 20) :
      (∫ u in CFMPReferenceSimplexDivergence435Transient.simplex,
        CFMPFrameMotion435Transient.divergence (T n) u) =
      (∫ q in parameterTriangle, top n q) +
        ∑ i : Fin 3, ∫ q in parameterTriangle, bottom n i q := by
    have hreg (u : Fin 3 → ℝ)
        (hu : u ∈ CFMPReferenceSimplexDivergence435Transient.simplex) :
        ContDiffAt ℝ 1 (T n) u :=
      CFMPOriginalReferenceFluxRegularity435Transient.original_total_flux_c1
        l0 hl0 M0 hm0 f hf (D*M0⁻¹) n
        (deriv (fun s => CFMPOriginalCellsIndependent435Transient.edgeMatrix (l s) n) t)
        (deriv (fun s => CFMPOriginalCellsIndependent435Transient.drop
          (D5.S3.Geometry.Hyperideal.LengthGramSideTrace.vertices (l s) n 0)) t) u hu
    have hdiv := CFMPReferenceSimplexDivergence435Transient.simplex_full_flux (T n) hreg
    calc
      _ = ∫ q in parameterTriangle, top n q + ∑ i : Fin 3, bottom n i q := by
        rw [hdiv]
        apply integral_congr_ae
        filter_upwards with q
        simp only [top,bottom,Finset.sum_neg_distrib,sub_eq_add_neg]
      _ = _ := by
        rw [integral_add (htop n) (hbottom n),
          integral_finsetSum Finset.univ (fun i _ => hintI n i)]
  refine ⟨Phi,fun n => ⟨hcont n,hint n,htrace n⟩,?_⟩
  calc
    _ = ∑ n : Fin 20, ((∫ q in parameterTriangle,top n q) +
        ∑ i : Fin 3, ∫ q in parameterTriangle,bottom n i q) := by
      apply Finset.sum_congr rfl
      intro n _
      exact hcell n
    _ = (∑ n : Fin 20, ∫ q in parameterTriangle,top n q) +
        ∑ n : Fin 20, ∑ i : Fin 3, ∫ q in parameterTriangle,bottom n i q :=
      Finset.sum_add_distrib
    _ = ∑ n : Fin 20, ∫ q in parameterTriangle,top n q := by
      rw [show (∑ n : Fin 20, ∑ i : Fin 3,
        ∫ q in parameterTriangle,bottom n i q) = 0 from hzero,add_zero]
    _ = ∑ n : Fin 20, ∫ z in range (F n),Phi n z ∂mu := by
      apply Finset.sum_congr rfl
      intro n _
      exact (hchange n).symm

end CFMPOriginalBoundaryFlux435Transient
