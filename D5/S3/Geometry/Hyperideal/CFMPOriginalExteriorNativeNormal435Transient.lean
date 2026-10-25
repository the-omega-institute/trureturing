import D5.S3.Geometry.Hyperideal.CFMPOriginalExteriorStaticNormal228Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeNormalSpeed435Transient

/-! Temporary actual offset normals for the twenty original exterior triangles. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped Matrix BigOperators Topology
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalCellsIndependent435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePullbackBridge435Transient
open CFMPNativePlaneNormal435Transient
open CFMPNativeNormalCoorientation435Transient
open CFMPActualTriangleNormal435Transient
open CFMPOriginalExteriorFaceChart435Transient

namespace CFMPOriginalExteriorNativeNormal435Transient
theorem tangent_covector (l : Fin 6 → ℝ) (n : Fin 20) (Z : CFMPLorentzLiftSurface435Transient.V) :
    dotProduct (CFMPFrameContinuity435Transient.tangent Z) (exteriorCovector l n) =
      dotProduct (outwardCoefficient l n) Z := by
  simp [CFMPFrameContinuity435Transient.tangent,exteriorCovector,dotProduct,
    Fin.sum_univ_four,Fin.sum_univ_three] <;> ring


theorem original_face_normal_speed
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : W, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (q : Fin 2 → ℝ)
    (hq : q ∈ parameterTriangle)
    (Z : CFMPLorentzLiftSurface435Transient.V) :
    let xi : cutBody l := ⟨xi l n q,
      xi_mem_cutBody l hl n q hq⟩
    let U : W := xi.val ᵥ* M
    let p : CFMPLorentzLiftSurface435Transient.V := nativeCoordinates (f xi)
    let a : CFMPLorentzLiftSurface435Transient.V := outwardCoefficient l n
    let b : ℝ := Real.sqrt (lorentz (raw l M n) (raw l M n))
    dotProduct ((nativeMatrix U).mulVec
      ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M))
      (coordinateNormal p (unit l M n))/(p 2)^2 =
      dotProduct a Z/(Real.sqrt (radius U)*b) := by
  dsimp only
  let xi : cutBody l := ⟨xi l n q,
      xi_mem_cutBody l hl n q hq⟩
  let U : W := xi.val ᵥ* M
  let p : CFMPLorentzLiftSurface435Transient.V := nativeCoordinates (f xi)
  let a : CFMPLorentzLiftSurface435Transient.V := outwardCoefficient l n
  let b : ℝ := Real.sqrt (lorentz (raw l M n) (raw l M n))
  have hr := original_native_coordinates l hl M f hf xi
  have hout := (original_outward_face l hl M hM hG f hf n).2 q hq
  have hp : p 2 ≠ 0 := (f xi).coordinates.property.ne'
  have hnormal : (liftMatrix p).mulVec (coordinateNormal p (unit l M n)) =
      unit l M n := hout.1
  have hplane : lorentz U (raw l M n) = 0 := by
    exact (pair_raw l M hM n xi.val).trans (face_readout l hl n q)
  have hZ : lorentz
      ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M) (raw l M n) =
      dotProduct a Z :=
    (pair_raw l M hM n _).trans (tangent_covector l n Z)
  change dotProduct ((nativeMatrix U).mulVec
    ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M))
    (coordinateNormal p (unit l M n))/(p 2)^2 = _
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
        (Real.sqrt (radius U))^3) • U) (b⁻¹ • raw l M n) = _
  rw [he,hZ,hplane,mul_zero,add_zero]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring


#print axioms original_face_normal_speed
end CFMPOriginalExteriorNativeNormal435Transient
