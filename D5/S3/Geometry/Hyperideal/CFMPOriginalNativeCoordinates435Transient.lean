import D5.S3.Geometry.Hyperideal.CFMPNativePullbackBridge435Transient
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPNativePullbackMetric435Transient
open CFMPNativePullbackBridge435Transient

namespace CFMPOriginalNativeCoordinates435Transient

def nativeCoordinates (p : HyperbolicThreeSpace) : V :=
  ![p.coordinates.val.fst.re, p.coordinates.val.fst.im, height p.coordinates]

-- The point is the same original f(w), selected by its supplied radial contract.
theorem original_native_coordinates
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (w : cutBody l) :
    0 < radius (w.val ᵥ* M) ∧ 0 < delta (w.val ᵥ* M) ∧
      nativeCoordinates (f w) = nativeMap (w.val ᵥ* M) := by
  let s := Real.sqrt (-gramQuadratic l w.val)
  let U := w.val ᵥ* M
  have hs : 0 < s := Real.sqrt_pos.mpr
    (neg_pos.mpr ((shared_radial_body l hl).2.2.2.1 w.val w.property))
  obtain ⟨y,hy,hu,ht,hcoord⟩ := hf w
  have hy' : y = s⁻¹ • U := by
    rw [hy]
    have hr : radial l w.val = s⁻¹ • w.val := by
      ext i
      simp [radial, s, div_eq_mul_inv, mul_comm]
    rw [hr,Matrix.smul_vecMul]
  have hU : U = s • y := by rw [hy',smul_smul, mul_inv_cancel₀ hs.ne',one_smul]
  have hradius : radius U = s^2 := by
    rw [hU]
    simp [radius,lorentz,Fin.sum_univ_four,smul_eq_mul] at hu ⊢
    linear_combination -s^2 * hu
  have hsqrt : Real.sqrt (radius U) = s := by
    rw [hradius,Real.sqrt_sq hs.le]
  have hden : 0 < delta U := by
    have hd := future_den y hu ht
    change 0 < U 3-U 2
    rw [hU]
    change 0 < s*y 3-s*y 2
    nlinarith
  refine ⟨by rw [hradius]; exact sq_pos_of_pos hs,hden,?_⟩
  change nativeCoordinates (f w) = nativeMap U
  have hdy : y 3-y 2 ≠ 0 := (future_den y hu ht).ne'
  ext i
  fin_cases i
  all_goals simp [nativeCoordinates,nativeMap,height,hcoord,hsqrt]
  all_goals rw [hU]
  all_goals simp [delta,smul_eq_mul]
  all_goals field_simp [hs.ne',hdy]
  all_goals ring

-- The derivative is on an open coordinate neighborhood in R4, so it also
-- applies at the boundary of the original closed body by restriction.
theorem coefficient_coordinate_hasFDerivAt
    (M : Matrix (Fin 4) (Fin 4) ℝ) (ξ : W)
    (hr : 0 < radius (ξ ᵥ* M)) (hd : delta (ξ ᵥ* M) ≠ 0) :
    HasFDerivAt (fun η : W => nativeMap (η ᵥ* M))
      (((nativeMatrix (ξ ᵥ* M)).mulVecLin.toContinuousLinearMap).comp
        M.vecMulLinear.toContinuousLinearMap) ξ := by
  exact (nativeMap_hasFDerivAt _ hr hd).comp ξ
    M.vecMulLinear.toContinuousLinearMap.hasFDerivAt

def coefficientSection (M : Matrix (Fin 4) (Fin 4) ℝ) : W →ₗ[ℝ] ℝ :=
  (∑ i, LinearMap.proj i).comp (M⁻¹).vecMulLinear

theorem coefficientSection_apply
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0) (ξ : W) :
    coefficientSection M (ξ ᵥ* M) = ∑ i, ξ i := by
  change (∑ i, LinearMap.proj i) ((ξ ᵥ* M) ᵥ* M⁻¹) = _
  rw [Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM),
    Matrix.vecMul_one]
  simp

-- The radial null direction is eliminated by the actual sum-one section.
theorem coefficient_tangent_injective
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0) (ξ η : W)
    (hξ : ∑ i, ξ i = 1) (hη : ∑ i, η i = 0)
    (hr : 0 < radius (ξ ᵥ* M)) (hd : delta (ξ ᵥ* M) ≠ 0)
    (hzero : (nativeMatrix (ξ ᵥ* M)).mulVec (η ᵥ* M) = 0) : η = 0 := by
  let U := ξ ᵥ* M
  let v := η ᵥ* M
  let s := Real.sqrt (radius U)
  let a := lorentz U v / s^3
  have hs : s ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  have hn : normalizedTangent U v = 0 := by
    rw [← derivative_intertwining U v hr hd,hzero]
    simp
  have hx : coefficientSection M U = 1 :=
    (coefficientSection_apply M hM ξ).trans hξ
  have hv : coefficientSection M v = 0 :=
    (coefficientSection_apply M hM η).trans hη
  have ha : a = 0 := by
    have h := congrArg (coefficientSection M) hn
    simpa [normalizedTangent,map_add,map_smul,hx,hv,a,s] using h
  have hvzero : v = 0 := by
    change s⁻¹ • v+a • U = 0 at hn
    rw [ha,zero_smul,add_zero] at hn
    exact (smul_eq_zero.mp hn).resolve_left (inv_ne_zero hs)
  have he := congrArg (fun v : W => v ᵥ* M⁻¹) hvzero
  simpa [v,Matrix.vecMul_vecMul,Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)] using he

theorem coefficient_tangent_pairing_positive
    (M : Matrix (Fin 4) (Fin 4) ℝ) (hM : M.det ≠ 0) (ξ η : W)
    (hξ : ∑ i, ξ i = 1) (hη : ∑ i, η i = 0) (hηne : η ≠ 0)
    (hr : 0 < radius (ξ ᵥ* M)) (hd : delta (ξ ᵥ* M) ≠ 0) :
    0 < lorentz (η ᵥ* M) (η ᵥ* M)/radius (ξ ᵥ* M) +
      lorentz (ξ ᵥ* M) (η ᵥ* M)*lorentz (ξ ᵥ* M) (η ᵥ* M)/(radius (ξ ᵥ* M))^2 := by
  let U := ξ ᵥ* M
  let v := η ᵥ* M
  let z := (nativeMatrix U).mulVec v
  have hz : z ≠ 0 := by
    intro hzero
    exact hηne (coefficient_tangent_injective M hM ξ η hξ hη hr hd hzero)
  have hdot : 0 < dotProduct z z := by
    apply lt_of_le_of_ne
    · exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))
    · intro he
      exact hz (dotProduct_self_eq_zero.mp he.symm)
  have hheight : nativeMap U 2 ≠ 0 :=
    div_ne_zero (Real.sqrt_pos.mpr hr).ne' hd
  rw [← coordinate_pullback_pairing U v v hr hd]
  exact div_pos hdot (sq_pos_of_ne_zero hheight)

end CFMPOriginalNativeCoordinates435Transient
