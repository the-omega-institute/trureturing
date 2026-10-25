import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeNormalSpeed435Transient
import D5.S3.Geometry.Hyperideal.CFMPAnchoredFrameContinuity435Transient

/-! Temporary exact anchored moving-face application. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology ContDiff Matrix.Norms.Elementwise
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPFrameMotion435Transient CFMPFrameContinuity435Transient
open CFMPNativePullbackMetric435Transient CFMPOriginalNativeCoordinates435Transient
open CFMPOriginalCellsIndependent435Transient CFMPOriginalPairedFaceMotion435Transient
open CFMPOriginalInternalFaceBridge435V2Transient CFMPOriginalInternalNormals435Transient
open CFMPNativePlaneNormal435Transient
open CFMPAnchoredSmoothFrame435Transient

namespace CFMPAnchoredOriginalFaceMotion435Transient

theorem lift_facePoint (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (i : Fin 3) (u : Fin 2 → ℝ) (hu : u ∈ parameterTriangle) :
    CFMPFrameMotion435Transient.lift (facePoint l n i u) = xi l n i u := by
  change liftAffine (drop (xi l n i u)) = xi l n i u
  exact CFMPOriginalCellsIndependent435Transient.lift_drop _
    (xi_mem_cutBody l hl n i u hu).1.2

theorem anchored_original_face_velocity
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
    (n : Fin 20) (i : Fin 3) (u : Fin 2 → ℝ) (hu : u ∈ parameterTriangle) :
    let P : ℝ → M4 := fun s => frame M0 (l s)
    let D : M4 := (fderiv ℝ (frame M0) l0) dl
    let x := facePoint l0 n i u
    let v := deriv (fun s => facePoint (l s) n i u) t
    let c : ℝ → CFMPLorentzLiftSurface435Transient.V := fun s =>
      nativeMap (ambient (P s) (facePoint (l s) n i u))
    let w : cutBody l0 := ⟨xi l0 n i u,xi_mem_cutBody l0 hl0 n i u hu⟩
    c t = nativeCoordinates (f w) ∧
    DifferentiableAt ℝ c t ∧
    dotProduct (deriv c t) (coordinateNormal (nativeCoordinates (f w))
      (unit M0 (A l0 n i))) / (nativeCoordinates (f w) 2)^2 =
      dotProduct (A l0 n i) (v+field (D*M0⁻¹) x) /
        (Real.sqrt (radius (w.val ᵥ* M0))*
          Real.sqrt (lorentz (raw M0 (A l0 n i)) (raw M0 (A l0 n i)))) := by
  let P : ℝ → M4 := fun s => frame M0 (l s)
  let D : M4 := (fderiv ℝ (frame M0) l0) dl
  let x := facePoint l0 n i u
  let v := deriv (fun s => facePoint (l s) n i u) t
  have hxlift : CFMPFrameMotion435Transient.lift x = xi l0 n i u :=
    lift_facePoint l0 hl0 n i u hu
  have hx : CFMPFrameMotion435Transient.lift x ∈ cutBody l0 := by
    rw [hxlift]
    exact xi_mem_cutBody l0 hl0 n i u hu
  have ha := CFMPAnchoredFrameContinuity435Transient.anchored_original_motion
    l0 hl0 M0 hm0 hg0 f hf l dl t hl hbase x hx
  have hp := original_native_coordinates l0 hl0 M0 f hf
    ⟨xi l0 n i u,xi_mem_cutBody l0 hl0 n i u hu⟩
  have hq : 0 < CFMPFrameContinuity435Transient.q M0 x := by
    change 0 < radius ((CFMPFrameMotion435Transient.lift x) ᵥ* M0)
    rw [hxlift]
    exact hp.1
  have hd : delta (ambient M0 x) ≠ 0 := by
    change delta ((CFMPFrameMotion435Transient.lift x) ᵥ* M0) ≠ 0
    rw [hxlift]
    exact hp.2.1.ne'
  have hxt : facePoint (l t) n i u = x := by simp only [hbase,x]
  have hPt : P t = M0 := ha.1
  have hqt : 0 < CFMPFrameContinuity435Transient.q (P t) (facePoint (l t) n i u) := by
    rw [hPt,hxt];exact hq
  have hdt : delta (ambient (P t) (facePoint (l t) n i u)) ≠ 0 := by
    rw [hPt,hxt];exact hd
  have hface := facePoint_differentiable l t hl.differentiableAt n i u
  have hder := actual_native_face_derivative l t hl.differentiableAt n i u P D
    ha.2.1 hqt hdt
  have ht := CFMPNativeMovingPoint435Transient.total_native_velocity P D
    (fun s => facePoint (l s) n i u) v t ha.2.1 hface.hasDerivAt
    (by simpa only [hPt] using hm0) hqt hdt
  rw [hPt,hxt] at ht
  have hs := CFMPNativeMovingPoint435Transient.native_spatial_direction M0 x
    (v+field (D*M0⁻¹) x) hq hd
  have hvel := ht.trans hs.deriv
  refine ⟨?_,hder.differentiableAt,?_⟩
  · change nativeMap (ambient (P t) (facePoint (l t) n i u)) = _
    rw [hPt,hxt]
    simpa only [ambient,hxlift] using hp.2.2.symm
  · change dotProduct (deriv (fun s => nativeMap
        (ambient (P s) (facePoint (l s) n i u))) t) _ / _ = _
    rw [hvel]
    simpa only [ambient,hxlift] using
      CFMPOriginalNativeNormalSpeed435Transient.original_face_normal_speed
        l0 hl0 M0 hm0 f hf n i u hu (v+field (D*M0⁻¹) x)

#print axioms anchored_original_face_velocity
end CFMPAnchoredOriginalFaceMotion435Transient
