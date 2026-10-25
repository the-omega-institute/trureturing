import D5.S3.Geometry.Hyperideal.CFMPFrameAffineTransport435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorFaceChart435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalNormals435Transient
import D5.S3.Geometry.Hyperideal.CFMPAnchoredOriginalFaceMotion435Transient
import D5.S3.Geometry.Hyperideal.CFMPAnchoredOriginalExteriorFaceMotion435Transient

/-! Temporary pointwise identification of the original reference-flux components. -/
noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open scoped Matrix.Norms.Elementwise
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open CFMPOriginalCellsIndependent435Transient
open CFMPOriginalInternalNormals435Transient
open CFMPOriginalExteriorFaceChart435Transient
open CFMPFrameMotion435Transient
open CFMPFrameContinuity435Transient
open CFMPFrameAffineTransport435Transient

namespace CFMPOriginalReferenceFluxReadout435Transient

def referenceInternalFace (i : Fin 3) (q : Fin 2 → ℝ) : Fin 3 → ℝ :=
  ![![0,q 0,q 1],![q 0,0,q 1],![q 0,q 1,0]] i

theorem original_internal_reference_point
    (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ) :
    CFMPOriginalPairedFaceMotion435Transient.facePoint l n i q =
      drop (vertices l n 0) +
        (edgeMatrix l n).mulVec (referenceInternalFace i q) := by
  have h21 : ((2 : Fin 3).succAbove (1 : Fin 2)).succ = (2 : Fin 4) := by decide
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [CFMPOriginalPairedFaceMotion435Transient.facePoint,
      CFMPOriginalFacePairing435Transient.faceParam,
      CFMPOriginalFacePairing435Transient.faceVertices,referenceInternalFace,
      drop,edgeMatrix,Matrix.mulVec,dotProduct,Fin.sum_univ_three,smul_eq_mul,h21] <;> ring

theorem internal_reference_component
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (P K : M4) (E : Matrix (Fin 3) (Fin 3) ℝ) (v u : Fin 3 → ℝ)
    (n : Fin 20) (i : Fin 3) :
    let B := edgeMatrix l n
    let o := drop (vertices l n 0)
    let x := o+B.mulVec u;
    -(totalFlux P K B E o v u i) = density P x *
      dotProduct (A l n i) (v+E.mulVec u+field K x) := by
  let B := edgeMatrix l n
  let o := drop (vertices l n 0)
  let x := o+B.mulVec u
  let w := v+E.mulVec u+field K x
  have hd : B.det ≠ 0 := edgeMatrix_det_ne_zero l hl n
  have h := CFMPOriginalCellsOrientation435Transient.coefficient_dot_mulVec
    B hd i (B⁻¹.mulVec w)
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv B
    (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec] at h
  have hc : CFMPOriginalCellsOrientation435Transient.coefficient B i = A l n i :=
    coefficient_eq l hl n i
  rw [hc] at h
  change -((|B.det| * density P x) * (B⁻¹.mulVec w) i) =
    density P x * dotProduct (A l n i) w
  rw [h]
  ring

theorem exterior_reference_component_sum
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (P K : M4) (E : Matrix (Fin 3) (Fin 3) ℝ) (v u : Fin 3 → ℝ)
    (n : Fin 20) :
    let B := edgeMatrix l n
    let o := drop (vertices l n 0)
    let x := o+B.mulVec u
    (∑ i : Fin 3,totalFlux P K B E o v u i) = density P x *
      dotProduct (outwardCoefficient l n) (v+E.mulVec u+field K x) := by
  let B := edgeMatrix l n
  let o := drop (vertices l n 0)
  let x := o+B.mulVec u
  let w := v+E.mulVec u+field K x
  have hd : B.det ≠ 0 := edgeMatrix_det_ne_zero l hl n
  have h := outward_coefficient_mulVec l hl n (B⁻¹.mulVec w)
  change dotProduct (outwardCoefficient l n) (B.mulVec (B⁻¹.mulVec w)) =
    |B.det| * ∑ j,(B⁻¹.mulVec w) j at h
  rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv B
    (isUnit_iff_ne_zero.mpr hd),Matrix.one_mulVec] at h
  change (∑ i : Fin 3,(|B.det| * density P x) * (B⁻¹.mulVec w) i) =
    density P x * dotProduct (outwardCoefficient l n) w
  rw [← Finset.mul_sum,h]
  ring

theorem actual_internal_reference_trace
    (M0 K : M4) (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (hl0 : ∀ k, 0 < l t k)
    (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ)
    (hq : q ∈ CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle) :
    let B := edgeMatrix (l t) n
    let E := deriv (fun s => edgeMatrix (l s) n) t
    let o := drop (vertices (l t) n 0)
    let v := deriv (fun s => drop (vertices (l s) n 0)) t;
    -(totalFlux M0 K B E o v (referenceInternalFace i q) i) =
      |M0.det| * dotProduct (A (l t) n i)
        (deriv (fun s => CFMPOriginalPairedFaceMotion435Transient.facePoint
          (l s) n i q) t +
          field K (CFMPOriginalPairedFaceMotion435Transient.facePoint (l t) n i q)) /
        (CFMPNativePullbackMetric435Transient.radius
          (CFMPOriginalInternalFaceBridge435V2Transient.xi (l t) n i q ᵥ* M0))^2 := by
  let l0 := l t
  let B : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => edgeMatrix (l s) n
  let o : ℝ → (Fin 3 → ℝ) := fun s => drop (vertices (l s) n 0)
  let E := deriv B t
  let v := deriv o t
  have hBdiff : DifferentiableAt ℝ B t :=
    CFMPActualCellMotion435Transient.edgeMatrix_differentiable l t hl n
  have hB : HasDerivAt B E t := by
    change HasDerivAt B (deriv B t) t
    exact DifferentiableAt.hasDerivAt (𝕜 := ℝ) (f := B) (x := t) hBdiff
  have ho : HasDerivAt o v t :=
    (drop.toContinuousLinearMap.differentiableAt.comp t
      (CFMPActualCellMotion435Transient.vertices_differentiable
        l t hl n 0)).hasDerivAt
  have hd := CFMPAffineDensityTransport435Transient.actual_affine_velocity
    o B v (referenceInternalFace i q) E t ho
      (fun j k => hasDerivAt_pi.mp (hasDerivAt_pi.mp hB j) k)
  have hcurve :
      (fun s => CFMPAffineDensityTransport435Transient.affinePoint
        o B s (referenceInternalFace i q)) =
      (fun s => CFMPOriginalPairedFaceMotion435Transient.facePoint (l s) n i q) := by
    funext s
    exact (original_internal_reference_point (l s) n i q).symm
  rw [hcurve] at hd
  have hv := hd.deriv
  have h := internal_reference_component l0 hl0 M0 K E v
    (referenceInternalFace i q) n i
  dsimp only at h
  rw [← original_internal_reference_point] at h
  have hlift := CFMPAnchoredOriginalFaceMotion435Transient.lift_facePoint
    l0 hl0 n i q hq
  have hr : CFMPFrameContinuity435Transient.q M0
      (CFMPOriginalPairedFaceMotion435Transient.facePoint l0 n i q) =
      CFMPNativePullbackMetric435Transient.radius
        (CFMPOriginalInternalFaceBridge435V2Transient.xi l0 n i q ᵥ* M0) := by
    simp only [CFMPFrameContinuity435Transient.q,ambient,hlift,
      CFMPNativePullbackMetric435Transient.radius]
  change -(totalFlux M0 K (edgeMatrix l0 n) E
    (drop (vertices l0 n 0)) v (referenceInternalFace i q) i) = _
  rw [h]
  rw [density,hr,hv]
  ring

theorem actual_exterior_reference_trace
    (M0 K : M4) (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (hl0 : ∀ k, 0 < l t k)
    (n : Fin 20) (q : Fin 2 → ℝ) :
    let B := edgeMatrix (l t) n
    let E := deriv (fun s => edgeMatrix (l s) n) t
    let o := drop (vertices (l t) n 0)
    let v := deriv (fun s => drop (vertices (l s) n 0)) t
    (∑ i : Fin 3,totalFlux M0 K B E o v ![1-q 0-q 1,q 0,q 1] i) =
      |M0.det| * dotProduct (outwardCoefficient (l t) n)
        (deriv (fun s => CFMPAnchoredOriginalExteriorFaceMotion435Transient.facePoint
          (l s) n q) t +
          field K (CFMPAnchoredOriginalExteriorFaceMotion435Transient.facePoint (l t) n q)) /
        (CFMPNativePullbackMetric435Transient.radius
          (CFMPOriginalExteriorFaceChart435Transient.xi (l t) n q ᵥ* M0))^2 := by
  let l0 := l t
  let B : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => edgeMatrix (l s) n
  let o : ℝ → (Fin 3 → ℝ) := fun s => drop (vertices (l s) n 0)
  let E := deriv B t
  let v := deriv o t
  have hBdiff : DifferentiableAt ℝ B t :=
    CFMPActualCellMotion435Transient.edgeMatrix_differentiable l t hl n
  have hB : HasDerivAt B E t := by
    change HasDerivAt B (deriv B t) t
    exact DifferentiableAt.hasDerivAt (𝕜 := ℝ) (f := B) (x := t) hBdiff
  have ho : HasDerivAt o v t :=
    (drop.toContinuousLinearMap.differentiableAt.comp t
      (CFMPActualCellMotion435Transient.vertices_differentiable
        l t hl n 0)).hasDerivAt
  have hd := CFMPAffineDensityTransport435Transient.actual_affine_velocity
    o B v ![1-q 0-q 1,q 0,q 1] E t ho
      (fun j k => hasDerivAt_pi.mp (hasDerivAt_pi.mp hB j) k)
  have hcurve :
      (fun s => CFMPAffineDensityTransport435Transient.affinePoint
        o B s ![1-q 0-q 1,q 0,q 1]) =
      (fun s => CFMPAnchoredOriginalExteriorFaceMotion435Transient.facePoint (l s) n q) := by
    funext s
    exact (drop_xi (l s) n q).symm
  rw [hcurve] at hd
  have hv := hd.deriv
  have h := exterior_reference_component_sum l0 hl0 M0 K E v
    ![1-q 0-q 1,q 0,q 1] n
  dsimp only at h
  rw [← drop_xi] at h
  have hlift := CFMPAnchoredOriginalExteriorFaceMotion435Transient.lift_facePoint
    l0 hl0 n q
  have hr : CFMPFrameContinuity435Transient.q M0
      (CFMPAnchoredOriginalExteriorFaceMotion435Transient.facePoint l0 n q) =
      CFMPNativePullbackMetric435Transient.radius
        (CFMPOriginalExteriorFaceChart435Transient.xi l0 n q ᵥ* M0) := by
    simp only [CFMPFrameContinuity435Transient.q,ambient,hlift,
      CFMPNativePullbackMetric435Transient.radius]
  change (∑ i : Fin 3,totalFlux M0 K (edgeMatrix l0 n) E
    (drop (vertices l0 n 0)) v ![1-q 0-q 1,q 0,q 1] i) = _
  rw [h]
  change density M0
      (CFMPAnchoredOriginalExteriorFaceMotion435Transient.facePoint l0 n q) *
      dotProduct (outwardCoefficient l0 n)
        (v + E.mulVec ![1-q 0-q 1,q 0,q 1] +
          field K (CFMPAnchoredOriginalExteriorFaceMotion435Transient.facePoint l0 n q)) = _
  rw [density,hr,hv]
  ring

end CFMPOriginalReferenceFluxReadout435Transient
