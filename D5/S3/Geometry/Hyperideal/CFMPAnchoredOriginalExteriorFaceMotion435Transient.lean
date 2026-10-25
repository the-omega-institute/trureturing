import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorNativeNormal435Transient
import D5.S3.Geometry.Hyperideal.CFMPActualCellMotion435Transient
import D5.S3.Geometry.Hyperideal.CFMPAnchoredFrameContinuity435Transient

/-! Temporary exact anchored motion of the actual exterior triangles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPNativePullbackMetric435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPOriginalCellsIndependent435Transient CFMPActualCellMotion435Transient
open CFMPOriginalExteriorFaceChart435Transient CFMPOriginalExteriorNativeNormal435Transient
open CFMPNativePlaneNormal435Transient
open CFMPAnchoredSmoothFrame435Transient

namespace CFMPAnchoredOriginalExteriorFaceMotion435Transient

def facePoint (l : Fin 6 → ℝ) (n : Fin 20) (u : Fin 2 → ℝ) : Fin 3 → ℝ :=
  drop (xi l n u)

theorem facePoint_differentiable (l : ℝ → Fin 6 → ℝ) (t : ℝ)
    (hl : DifferentiableAt ℝ l t) (n : Fin 20) (u : Fin 2 → ℝ) :
    DifferentiableAt ℝ (fun s => facePoint (l s) n u) t := by
  have hv (j : Fin 4) (k : Fin 4) :
      DifferentiableAt ℝ (fun s => vertices (l s) n j k) t :=
    differentiableAt_pi.mp (vertices_differentiable l t hl n j) k
  have hxi : DifferentiableAt ℝ (fun s => xi (l s) n u) t := by
    apply differentiableAt_pi.mpr
    intro k
    change DifferentiableAt ℝ (fun s => vertices (l s) n 1 k +
      u 0 * (vertices (l s) n 2 k-vertices (l s) n 1 k) +
      u 1 * (vertices (l s) n 3 k-vertices (l s) n 1 k)) t
    exact ((hv 1 k).add ((differentiableAt_const (u 0)).mul
      ((hv 2 k).sub (hv 1 k)))).add
        ((differentiableAt_const (u 1)).mul ((hv 3 k).sub (hv 1 k)))
  exact drop.toContinuousLinearMap.differentiableAt.comp t hxi

theorem lift_facePoint (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (n : Fin 20) (u : Fin 2 → ℝ) :
    CFMPFrameMotion435Transient.lift (facePoint l n u) = xi l n u := by
  change liftAffine (drop (xi l n u)) = xi l n u
  exact lift_drop _ (xi_sum_one l hl n u)

theorem anchored_original_exterior_face_velocity
    (l0 : Fin 6 → ℝ) (hl0 : ∀ i, 0 < l0 i)
    (M0 : M4) (hm0 : M0.det ≠ 0)
    (hg0 : M0 * J * M0.transpose = lengthGram l0)
    (f : cutBody l0 → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : Fin 4 → ℝ, y = (radial l0 w.val) ᵥ* M0 ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (l : ℝ → Fin 6 → ℝ) (dl : Fin 6 → ℝ) (t : ℝ)
    (hl : HasDerivAt l dl t) (hbase : l t = l0)
    (n : Fin 20) (u : Fin 2 → ℝ) (hu : u ∈ parameterTriangle) :
    let P : ℝ → M4 := fun s => frame M0 (l s)
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let x := facePoint l0 n u
    let v := deriv (fun s => facePoint (l s) n u) t
    let c : ℝ → CFMPLorentzLiftSurface435Transient.V := fun s =>
      nativeMap (ambient (P s) (facePoint (l s) n u))
    let w : cutBody l0 := ⟨xi l0 n u,xi_mem_cutBody l0 hl0 n u hu⟩
    c t = nativeCoordinates (f w) ∧
    DifferentiableAt ℝ c t ∧
    dotProduct (deriv c t) (coordinateNormal (nativeCoordinates (f w))
      (unit l0 M0 n)) / (nativeCoordinates (f w) 2)^2 =
      dotProduct (outwardCoefficient l0 n) (v+field (D*M0⁻¹) x) /
        (Real.sqrt (radius (w.val ᵥ* M0))*
          Real.sqrt (lorentz (raw l0 M0 n) (raw l0 M0 n))) := by
  let P : ℝ → M4 := fun s => frame M0 (l s)
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let x := facePoint l0 n u
  let v := deriv (fun s => facePoint (l s) n u) t
  have hxlift : CFMPFrameMotion435Transient.lift x = xi l0 n u :=
    lift_facePoint l0 hl0 n u
  have hx : CFMPFrameMotion435Transient.lift x ∈ cutBody l0 := by
    rw [hxlift]
    exact xi_mem_cutBody l0 hl0 n u hu
  have ha := CFMPAnchoredFrameContinuity435Transient.anchored_original_motion
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase x hx
  have hp := original_native_coordinates l0 hl0 M0 f hf
    ⟨xi l0 n u,xi_mem_cutBody l0 hl0 n u hu⟩
  have hq : 0 < CFMPFrameContinuity435Transient.q M0 x := by
    change 0 < radius ((CFMPFrameMotion435Transient.lift x) ᵥ* M0)
    rw [hxlift]
    exact hp.1
  have hd : delta (ambient M0 x) ≠ 0 := by
    change delta ((CFMPFrameMotion435Transient.lift x) ᵥ* M0) ≠ 0
    rw [hxlift]
    exact hp.2.1.ne'
  have hxt : facePoint (l t) n u = x := by simp only [hbase,x]
  have hPt : P t = M0 := ha.1
  have hqt : 0 < CFMPFrameContinuity435Transient.q (P t) (facePoint (l t) n u) := by
    rw [hPt,hxt];exact hq
  have hdt : delta (ambient (P t) (facePoint (l t) n u)) ≠ 0 := by
    rw [hPt,hxt];exact hd
  have hface := facePoint_differentiable l t hl.differentiableAt n u
  have hder := CFMPNativeMovingPoint435Transient.native_moving_derivative P D
    (fun s => facePoint (l s) n u) _ t ha.2.1 hface.hasDerivAt hqt hdt
  have ht := CFMPNativeMovingPoint435Transient.total_native_velocity P D
    (fun s => facePoint (l s) n u) v t ha.2.1 hface.hasDerivAt
    (by simpa only [hPt] using hm0) hqt hdt
  rw [hPt,hxt] at ht
  have hs := CFMPNativeMovingPoint435Transient.native_spatial_direction M0 x
    (v+field (D*M0⁻¹) x) hq hd
  have hvel := ht.trans hs.deriv
  refine ⟨?_,hder.differentiableAt,?_⟩
  · change nativeMap (ambient (P t) (facePoint (l t) n u)) = _
    rw [hPt,hxt]
    simpa only [ambient,hxlift] using hp.2.2.symm
  · change dotProduct (deriv (fun s => nativeMap
        (ambient (P s) (facePoint (l s) n u))) t) _ / _ = _
    rw [hvel]
    simpa only [ambient,hxlift] using
      CFMPOriginalExteriorNativeNormal435Transient.original_face_normal_speed
        l0 hl0 M0 hm0
          (CFMPAnchoredFrameContinuity435Transient.matrix_gram_rows M0 l0 hg0) f hf n u hu (v+field (D*M0⁻¹) x)

#print axioms anchored_original_exterior_face_velocity
end CFMPAnchoredOriginalExteriorFaceMotion435Transient
