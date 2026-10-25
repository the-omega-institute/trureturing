import D5.S3.Geometry.Hyperideal.CFMPActualCellMotion435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalInternalNormals435Transient

/-! Temporary exact applications for the literal paired moving faces. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology
open Set Filter
open CFMPOriginalFacePairing435Transient
open CFMPOriginalCellsIndependent435Transient
open CFMPActualCellMotion435Transient
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPNativePullbackMetric435Transient

namespace CFMPOriginalPairedFaceMotion435Transient

-- The original closed coefficient triangle, with its original vertex order.
def facePoint (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 3)
    (q : Fin 2 → ℝ) : Fin 3 → ℝ :=
  drop (faceParam l n i q)

theorem face_vertices_differentiable (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) (i j : Fin 3) :
    DifferentiableAt ℝ (fun s => faceVertices (l s) n i j) t := by
  fin_cases j
  · exact vertices_differentiable l t hl n 0
  · exact vertices_differentiable l t hl n (i.succAbove 0).succ
  · exact vertices_differentiable l t hl n (i.succAbove 1).succ

theorem faceParam_differentiable (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ) :
    DifferentiableAt ℝ (fun s => faceParam (l s) n i q) t := by
  have hv (j : Fin 3) (k : Fin 4) :
      DifferentiableAt ℝ (fun s => faceVertices (l s) n i j k) t :=
    differentiableAt_pi.mp (face_vertices_differentiable l t hl n i j) k
  apply differentiableAt_pi.mpr
  intro k
  change DifferentiableAt ℝ (fun s => faceVertices (l s) n i 0 k +
    q 0 * (faceVertices (l s) n i 1 k - faceVertices (l s) n i 0 k) +
    q 1 * (faceVertices (l s) n i 2 k - faceVertices (l s) n i 0 k)) t
  exact ((hv 0 k).add ((differentiableAt_const (q 0)).mul
    ((hv 1 k).sub (hv 0 k)))).add
      ((differentiableAt_const (q 1)).mul ((hv 2 k).sub (hv 0 k)))

theorem facePoint_differentiable (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ) :
    DifferentiableAt ℝ (fun s => facePoint (l s) n i q) t := by
  exact drop.toContinuousLinearMap.differentiableAt.comp t
    (faceParam_differentiable l t hl n i q)

theorem pair_facePoint (l : Fin 6 → ℝ) (p : Fin 30) (q : Fin 2 → ℝ) :
    facePoint l (pairTable p).1.1 (pairTable p).1.2 q =
      facePoint l (pairTable p).2.1 (pairTable p).2.2 (pairedParam p q) := by
  exact congrArg (fun v => drop v)
    (CFMPOriginalInternalNormals435Transient.pair_xi l p q)

theorem actual_native_face_derivative (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ)
    (P : ℝ → M4) (D : M4) (hP : HasDerivAt P D t)
    (hr : 0 < CFMPFrameContinuity435Transient.q (P t) (facePoint (l t) n i q))
    (hd : delta (ambient (P t) (facePoint (l t) n i q)) ≠ 0) :
    HasDerivAt (fun s => nativeMap (ambient (P s) (facePoint (l s) n i q)))
      ((nativeMatrix (ambient (P t) (facePoint (l t) n i q))).mulVec
        (Matrix.vecMul (CFMPFrameContinuity435Transient.tangent
          (deriv (fun s => facePoint (l s) n i q) t)) (P t) +
          Matrix.vecMul (CFMPFrameMotion435Transient.lift (facePoint (l t) n i q)) D)) t := by
  exact CFMPNativeMovingPoint435Transient.native_moving_derivative P D
    (fun s => facePoint (l s) n i q) _ t hP
    (facePoint_differentiable l t hl n i q).hasDerivAt hr hd

theorem paired_native_velocities (l : ℝ → Fin 6 → ℝ) (P : ℝ → M4)
    (p : Fin 30) (q : Fin 2 → ℝ) (t : ℝ) :
    deriv (fun s => nativeMap
      (ambient (P s) (facePoint (l s) (pairTable p).1.1 (pairTable p).1.2 q))) t =
    deriv (fun s => nativeMap
      (ambient (P s) (facePoint (l s) (pairTable p).2.1 (pairTable p).2.2
        (pairedParam p q)))) t := by
  have he : (fun s => nativeMap
      (ambient (P s) (facePoint (l s) (pairTable p).1.1 (pairTable p).1.2 q))) =
    (fun s => nativeMap
      (ambient (P s) (facePoint (l s) (pairTable p).2.1 (pairTable p).2.2
        (pairedParam p q)))) := by
    funext s
    rw [pair_facePoint]
  rw [he]

end CFMPOriginalPairedFaceMotion435Transient
