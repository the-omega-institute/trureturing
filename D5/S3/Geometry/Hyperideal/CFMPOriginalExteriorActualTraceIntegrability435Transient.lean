import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorTraceIntegrability435Transient
import D5.S3.Geometry.Hyperideal.CFMPAnchoredOriginalExteriorFaceMotion435Transient
import Mathlib.Analysis.Calculus.Deriv.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Topology
open scoped Matrix BigOperators ENNReal Classical Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPOriginalCellsIndependent435Transient
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open CFMPActualCellMotion435Transient
open CFMPAnchoredOriginalExteriorFaceMotion435Transient
open CFMPOriginalExteriorFaceChart435Transient
open CFMPOriginalExteriorNativeNormal435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePlaneNormal435Transient
open CFMPFrameMotion435Transient
open CFMPFrameContinuity435Transient
open CFMPAnchoredSmoothFrame435Transient

namespace CFMPOriginalExteriorActualTraceIntegrability435Transient

private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

def vertexVelocity (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (n : Fin 20) (j : Fin 3) : Fin 3 → ℝ :=
  deriv (fun s => drop (vertices (l s) n j.succ)) t

theorem facePoint_velocity_affine
    (l : ℝ → Fin 6 → ℝ) (t : ℝ) (hl : DifferentiableAt ℝ l t)
    (n : Fin 20) (q : Fin 2 → ℝ) :
    deriv (fun s => facePoint (l s) n q) t =
      vertexVelocity l t n 0 +
        q 0 • (vertexVelocity l t n 1 - vertexVelocity l t n 0) +
        q 1 • (vertexVelocity l t n 2 - vertexVelocity l t n 0) := by
  have hd (j : Fin 3) :
      DifferentiableAt ℝ (fun s => drop (vertices (l s) n j.succ)) t :=
    drop.toContinuousLinearMap.differentiableAt.comp t
      (vertices_differentiable l t hl n j.succ)
  have hc (j k : Fin 3) :
      HasDerivAt (fun s => drop (vertices (l s) n j.succ) k)
        (vertexVelocity l t n j k) t :=
    hasDerivAt_pi.mp (hd j).hasDerivAt k
  have hder : HasDerivAt (fun s => facePoint (l s) n q)
      (vertexVelocity l t n 0 +
        q 0 • (vertexVelocity l t n 1 - vertexVelocity l t n 0) +
        q 1 • (vertexVelocity l t n 2 - vertexVelocity l t n 0)) t := by
    apply hasDerivAt_pi.mpr
    intro k
    change HasDerivAt (fun s => drop (vertices (l s) n 1) k +
      q 0 * (drop (vertices (l s) n 2) k - drop (vertices (l s) n 1) k) +
      q 1 * (drop (vertices (l s) n 3) k - drop (vertices (l s) n 1) k))
      (vertexVelocity l t n 0 k +
        q 0 * (vertexVelocity l t n 1 k - vertexVelocity l t n 0 k) +
        q 1 * (vertexVelocity l t n 2 k - vertexVelocity l t n 0 k)) t
    exact ((hc 0 k).add (((hc 1 k).sub (hc 0 k)).const_mul (q 0))).add
      (((hc 2 k).sub (hc 0 k)).const_mul (q 1))
  exact hder.deriv

theorem anchored_actual_normal_trace_integrable
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
      f ⟨xi l0 n q.val, xi_mem_cutBody l0 hl0 n q.val q.property⟩
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let psi : parameterTriangle → ℝ := fun q =>
      dotProduct (outwardCoefficient l0 n)
        (deriv (fun s => facePoint (l s) n q.val) t +
          field (D * M0⁻¹) (facePoint l0 n q.val)) /
        (Real.sqrt (radius (xi l0 n q.val ᵥ* M0)) *
          Real.sqrt (lorentz (raw l0 M0 n) (raw l0 M0 n)))
    ∃ phi : HyperbolicThreeSpace → ℝ,
      ContinuousOn phi (range F) ∧
      IntegrableOn phi (range F)
        (Measure.euclideanHausdorffMeasure 2 : Measure HyperbolicThreeSpace) ∧
      ∀ q : parameterTriangle,
        phi (F q) = psi q ∧
        (let c : ℝ → Fin 3 → ℝ := fun s => nativeMap
          (ambient (frame M0 (l s)) (facePoint (l s) n q.val))
         c t = nativeCoordinates (F q) ∧
         DifferentiableAt ℝ c t ∧
         dotProduct (deriv c t)
           (coordinateNormal (nativeCoordinates (F q)) (unit l0 M0 n)) /
             (nativeCoordinates (F q) 2)^2 = phi (F q)) := by
  classical
  let F : parameterTriangle → HyperbolicThreeSpace := fun q =>
    f ⟨xi l0 n q.val, xi_mem_cutBody l0 hl0 n q.val q.property⟩
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let psi : parameterTriangle → ℝ := fun q =>
    dotProduct (outwardCoefficient l0 n)
      (deriv (fun s => facePoint (l s) n q.val) t +
        field (D * M0⁻¹) (facePoint l0 n q.val)) /
      (Real.sqrt (radius (xi l0 n q.val ᵥ* M0)) *
        Real.sqrt (lorentz (raw l0 M0 n) (raw l0 M0 n)))
  have hG := CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0
  obtain ⟨hEmb,harea,hint⟩ :=
    CFMPOriginalExteriorTraceIntegrability435Transient.original_face_continuous_trace_integrable
      l0 hl0 M0 hm0 hG f hf n
  have hvcont : Continuous (fun q : Fin 2 → ℝ =>
      deriv (fun s => facePoint (l s) n q) t) := by
    have haff : Continuous (fun q : Fin 2 → ℝ =>
        vertexVelocity l t n 0 +
          q 0 • (vertexVelocity l t n 1 - vertexVelocity l t n 0) +
          q 1 • (vertexVelocity l t n 2 - vertexVelocity l t n 0)) :=
      (continuous_const.add ((continuous_apply 0).smul continuous_const)).add
        ((continuous_apply 1).smul continuous_const)
    exact haff.congr (fun q =>
      (facePoint_velocity_affine l t hl.differentiableAt n q).symm)
  have hxcont : Continuous (fun q : Fin 2 → ℝ => facePoint l0 n q) := by
    apply continuous_pi
    intro k
    change Continuous (fun q : Fin 2 → ℝ => drop (vertices l0 n 1) k +
      q 0 * (drop (vertices l0 n 2) k - drop (vertices l0 n 1) k) +
      q 1 * (drop (vertices l0 n 3) k - drop (vertices l0 n 1) k))
    fun_prop
  have hfield : Continuous (field (D * M0⁻¹)) := by
    apply continuous_pi
    intro k
    simp only [field,alpha,lift,Fin.sum_univ_four]
    fun_prop
  have hnum : Continuous (fun q : Fin 2 → ℝ =>
      dotProduct (outwardCoefficient l0 n)
        (deriv (fun s => facePoint (l s) n q) t +
          field (D * M0⁻¹) (facePoint l0 n q))) := by
    have hc (k : Fin 3) := (continuous_apply k).comp
      (hvcont.add (hfield.comp hxcont))
    simp only [dotProduct,Fin.sum_univ_three]
    fun_prop
  have hxi : Continuous (xi l0 n) := by
    exact (continuous_const.add ((continuous_apply 0).smul continuous_const)).add
      ((continuous_apply 1).smul continuous_const)
  have hU : Continuous (fun q : Fin 2 → ℝ => xi l0 n q ᵥ* M0) :=
    M0.vecMulLinear.toContinuousLinearMap.continuous.comp hxi
  have hrad : Continuous (fun q : Fin 2 → ℝ => radius (xi l0 n q ᵥ* M0)) := by
    have hc (k : Fin 4) := (continuous_apply k).comp hU
    simp only [radius,lorentz,Fin.sum_univ_four]
    fun_prop
  have hb : 0 < Real.sqrt (lorentz (raw l0 M0 n) (raw l0 M0 n)) :=
    Real.sqrt_pos.mpr (raw_spacelike l0 hl0 M0 hm0 hG f hf n)
  have hpsi : Continuous psi := by
    apply (hnum.comp continuous_subtype_val).div
      (((hrad.comp continuous_subtype_val).sqrt).mul continuous_const)
    intro q
    exact mul_ne_zero (Real.sqrt_pos.mpr
      (original_native_coordinates l0 hl0 M0 f hf
        ⟨xi l0 n q.val,xi_mem_cutBody l0 hl0 n q.val q.property⟩).1).ne' hb.ne'
  let H := hEmb.isEmbedding.toHomeomorph
  let phi : HyperbolicThreeSpace → ℝ := fun p =>
    if hp : p ∈ range F then psi (H.symm ⟨p,hp⟩) else 0
  have hphi : ContinuousOn phi (range F) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (hpsi.comp H.symm.continuous).congr (fun p => by
      change psi (H.symm p) = phi p.val
      dsimp only [phi]
      rw [dif_pos p.property])
  have hphiq (q : parameterTriangle) : phi (F q) = psi q := by
    have hq : F q ∈ range F := mem_range_self q
    dsimp only [phi]
    rw [dif_pos hq]
    change psi (H.symm (H q)) = psi q
    rw [H.symm_apply_apply]
  refine ⟨phi,hphi,hint phi hphi,?_⟩
  intro q
  refine ⟨hphiq q,?_⟩
  have ha := CFMPAnchoredOriginalExteriorFaceMotion435Transient.anchored_original_exterior_face_velocity
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase n q.val q.property
  refine ⟨ha.1,ha.2.1,?_⟩
  rw [hphiq q]
  exact ha.2.2

end CFMPOriginalExteriorActualTraceIntegrability435Transient
