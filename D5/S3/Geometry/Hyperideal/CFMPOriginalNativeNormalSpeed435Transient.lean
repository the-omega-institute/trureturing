import D5.S3.Geometry.Hyperideal.CFMPOriginalPairedFaceMotion435Transient

/-! Temporary exact native normal-speed application on the original closed face. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators Topology
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalInternalNormals435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePullbackBridge435Transient
open CFMPNativePlaneNormal435Transient

namespace CFMPOriginalNativeNormalSpeed435Transient

theorem tangent_covector (a Z : V) :
    dotProduct (CFMPFrameContinuity435Transient.tangent Z) (covector a) =
      dotProduct a Z := by
  simp [CFMPFrameContinuity435Transient.tangent,covector,dotProduct,
    Fin.sum_univ_four,Fin.sum_univ_three]
  ring

theorem original_face_normal_speed
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ)
    (hq : q ∈ CFMPOriginalInternalFaceBridge435V2Transient.parameterTriangle)
    (Z : V) :
    let xi : cutBody l := ⟨CFMPOriginalInternalFaceBridge435V2Transient.xi l n i q,
      CFMPOriginalInternalFaceBridge435V2Transient.xi_mem_cutBody l hl n i q hq⟩
    let U : W := xi.val ᵥ* M
    let p : V := nativeCoordinates (f xi)
    let a : V := A l n i
    let b : ℝ := Real.sqrt (lorentz (raw M a) (raw M a))
    dotProduct ((nativeMatrix U).mulVec
      ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M))
      (coordinateNormal p (unit M a))/(p 2)^2 =
      dotProduct a Z/(Real.sqrt (radius U)*b) := by
  dsimp only
  let xi : cutBody l := ⟨CFMPOriginalInternalFaceBridge435V2Transient.xi l n i q,
      CFMPOriginalInternalFaceBridge435V2Transient.xi_mem_cutBody l hl n i q hq⟩
  let U : W := xi.val ᵥ* M
  let p : V := nativeCoordinates (f xi)
  let a : V := A l n i
  let b : ℝ := Real.sqrt (lorentz (raw M a) (raw M a))
  have hr := original_native_coordinates l hl M f hf xi
  have hout := (original_outward_face l hl M hM f hf n i).2 q hq
  have hp : p 2 ≠ 0 := (f xi).coordinates.property.ne'
  have hnormal : (liftMatrix p).mulVec (coordinateNormal p (unit M a)) =
      unit M a := hout.1
  have hplane : lorentz U (raw M a) = 0 := by
    exact (pair_raw M hM xi.val a).trans (face_readout l hl n i q)
  have hZ : lorentz
      ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M) (raw M a) =
      dotProduct a Z :=
    (pair_raw M hM _ a).trans (tangent_covector a Z)
  change dotProduct ((nativeMatrix U).mulVec
    ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M))
    (coordinateNormal p (unit M a))/(p 2)^2 = _
  rw [← liftMatrix_lorentz p _ _ hp,hnormal]
  have hi : (liftMatrix p).mulVec ((nativeMatrix U).mulVec
      ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M)) =
      normalizedTangent U ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M) := by
    dsimp only [p]
    rw [hr.2.2]
    exact derivative_intertwining U _ hr.1 hr.2.1.ne'
  rw [hi]
  have he (r s : ℝ) (X Y N : W) :
      lorentz (r • X+s • Y) (b⁻¹ • N) =
        r*b⁻¹*lorentz X N+s*b⁻¹*lorentz Y N := by
    simp [lorentz,Fin.sum_univ_four,smul_eq_mul]
    ring
  change lorentz
    ((Real.sqrt (radius U))⁻¹ •
      ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M) +
      (lorentz U ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M) /
        (Real.sqrt (radius U))^3) • U) (b⁻¹ • raw M a) = _
  rw [he,hZ,hplane,mul_zero,add_zero]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end CFMPOriginalNativeNormalSpeed435Transient
