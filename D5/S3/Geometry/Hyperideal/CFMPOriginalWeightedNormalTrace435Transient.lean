import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeNormalSpeed435Transient
import D5.S3.Geometry.Hyperideal.CFMPOriginalCofactorSurface435Transient
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Temporary exact physical normal-trace/density cancellation. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Matrix BigOperators
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalInternalNormals435Transient
open CFMPOriginalNativeCoordinates435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePlaneNormal435Transient
open CFMPOriginalInternalFaceBridge435V2Transient

namespace CFMPOriginalWeightedNormalTrace435Transient

-- rho is the same actual surface density supplied by the cofactor surface theorem.
theorem original_weighted_normal_trace
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) (q : Fin 2 → ℝ) (hq : q ∈ parameterTriangle)
    (Z : V) (rho : ℝ)
    (hrho : rho = |M.det| * Real.sqrt (lorentz (raw M (A l n i))
        (raw M (A l n i))) /
      (Real.sqrt (radius (xi l n i q ᵥ* M)))^3) :
    let w : cutBody l := ⟨xi l n i q,xi_mem_cutBody l hl n i q hq⟩
    let U : Fin 4 → ℝ := w.val ᵥ* M
    let p : V := nativeCoordinates (f w)
    rho * (dotProduct ((nativeMatrix U).mulVec
      ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M))
      (coordinateNormal p (unit M (A l n i)))/(p 2)^2) =
      |M.det| * dotProduct (A l n i) Z / (radius U)^2 := by
  dsimp only
  let U : Fin 4 → ℝ := xi l n i q ᵥ* M
  have hr : 0 < radius U :=
    (original_native_coordinates l hl M f hf
      ⟨xi l n i q,xi_mem_cutBody l hl n i q hq⟩).1
  have hs : Real.sqrt (radius U) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hb : Real.sqrt (lorentz (raw M (A l n i))
      (raw M (A l n i))) ≠ 0 :=
    (Real.sqrt_pos.mpr (raw_spacelike l hl M hM f hf n i)).ne'
  rw [CFMPOriginalNativeNormalSpeed435Transient.original_face_normal_speed
    l hl M hM f hf n i q hq Z,hrho]
  change (|M.det| * Real.sqrt (lorentz (raw M (A l n i)) (raw M (A l n i))) /
      (Real.sqrt (radius U))^3) *
    (dotProduct (A l n i) Z /
      (Real.sqrt (radius U) * Real.sqrt (lorentz (raw M (A l n i))
        (raw M (A l n i))))) = _
  calc
    _ = |M.det| * dotProduct (A l n i) Z / ((Real.sqrt (radius U))^2)^2 := by
      field_simp
      <;> ring
    _ = _ := by rw [Real.sq_sqrt hr.le]


-- The pushforward and normal trace share the very same cofactor-density witness.
private local instance : MeasurableSpace HyperbolicThreeSpace := borel _
private local instance : BorelSpace HyperbolicThreeSpace := ⟨rfl⟩

theorem original_cofactor_normal_trace
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0)
    (hG : ∀ i j, lorentz (M i) (M j) = lengthGram l i j)
    (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ v, ∃ y : Fin 4 → ℝ, y = (radial l v.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f v).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)),1/(y 3-y 2)))
    (n : Fin 20) (i : Fin 3) :
    ∃ rho : (Fin 2 → ℝ) → ℝ, ∃ P : (Fin 2 → ℝ) → HyperbolicThreeSpace,
      Measurable rho ∧ Measurable P ∧
      (∀ q ∈ parameterTriangle, 0 < rho q) ∧
      (∀ (q : Fin 2 → ℝ) (hq : q ∈ parameterTriangle),
        P q = f ⟨xi l n i q,xi_mem_cutBody l hl n i q hq⟩) ∧
      MeasureTheory.Measure.map P
        ((MeasureTheory.volume.restrict parameterTriangle).withDensity
          (fun q => ENNReal.ofReal (rho q))) =
        (MeasureTheory.Measure.euclideanHausdorffMeasure 2 :
          MeasureTheory.Measure HyperbolicThreeSpace).restrict (faceSet l hl f n i) ∧
      ∀ (q : Fin 2 → ℝ) (hq : q ∈ parameterTriangle) (Z : V),
        let w : cutBody l := ⟨xi l n i q,xi_mem_cutBody l hl n i q hq⟩
        let U : Fin 4 → ℝ := w.val ᵥ* M
        let p : V := nativeCoordinates (f w)
        rho q * (dotProduct ((nativeMatrix U).mulVec
          ((CFMPFrameContinuity435Transient.tangent Z) ᵥ* M))
          (coordinateNormal p (unit M (A l n i)))/(p 2)^2) =
          |M.det| * dotProduct (A l n i) Z / (radius U)^2 := by
  obtain ⟨rho,P,r,D,hrho,hP,hpos,hpoint,hgeometry,hmap,hcofactor,hintegral⟩ :=
    CFMPOriginalCofactorSurface435Transient.original_internal_native_cofactor_surface
      l hl M hM hG f hf n i
  refine ⟨rho,P,hrho,hP,hpos,hpoint,?_,?_⟩
  · exact hmap
  · intro q hq Z
    exact original_weighted_normal_trace l hl M hM f hf n i q hq Z (rho q)
      (hcofactor q hq)

end CFMPOriginalWeightedNormalTrace435Transient
