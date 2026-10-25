import D5.S3.Geometry.Hyperideal.CFMPOriginalNativeMetricSpeed435Transient

noncomputable section
set_option autoImplicit false
open scoped Matrix BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open CFMPLorentzLiftSurface435Transient
open CFMPOriginalNativeCoordinates435Transient

namespace CFMPNativePlaneNormal435Transient

-- Coordinate vector of the normal whose lift differential is N.
def coordinateNormal (p : V) (N : W) : V :=
  ![p 2 * (N 0 + p 0 * (N 2 - N 3)),
    p 2 * (N 1 + p 1 * (N 2 - N 3)),
    (p 2)^2 * (N 2 - N 3)]

theorem coordinateNormal_lift (p : V) (N : W) (hp : p 2 ≠ 0)
    (hplane : lorentz (coordinateLift p) N = 0) :
    (liftMatrix p).mulVec (coordinateNormal p N) = N := by
  have hplane' :
      2 * p 0 * N 0 + 2 * p 1 * N 1 +
        ((p 0)^2 + (p 1)^2 + (p 2)^2 - 1) * N 2 -
        ((p 0)^2 + (p 1)^2 + (p 2)^2 + 1) * N 3 = 0 := by
    simp [coordinateLift, lorentz, Fin.sum_univ_four] at hplane
    field_simp [hp] at hplane
    nlinarith [hplane]
  ext i
  fin_cases i
  all_goals simp [liftMatrix, coordinateNormal, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]
  all_goals field_simp [hp]
  all_goals nlinarith [hplane']

theorem coordinateNormal_pairing (p a : V) (N : W) (hp : p 2 ≠ 0)
    (hplane : lorentz (coordinateLift p) N = 0) :
    dotProduct a (coordinateNormal p N) / (p 2)^2 =
      lorentz ((liftMatrix p).mulVec a) N := by
  rw [← liftMatrix_lorentz p a (coordinateNormal p N) hp,
    coordinateNormal_lift p N hp hplane]

theorem coordinateNormal_unit (p : V) (N : W) (hp : p 2 ≠ 0)
    (hplane : lorentz (coordinateLift p) N = 0) (hunit : lorentz N N = 1) :
    dotProduct (coordinateNormal p N) (coordinateNormal p N) / (p 2)^2 = 1 := by
  rw [coordinateNormal_pairing p _ N hp hplane, coordinateNormal_lift p N hp hplane,
    hunit]

theorem coordinateNormal_orthogonal (p a : V) (N : W) (hp : p 2 ≠ 0)
    (hplane : lorentz (coordinateLift p) N = 0)
    (ha : lorentz ((liftMatrix p).mulVec a) N = 0) :
    dotProduct a (coordinateNormal p N) / (p 2)^2 = 0 := by
  rw [coordinateNormal_pairing p a N hp hplane, ha]

-- The normal is at the same point of the original radial realization.
theorem original_native_plane_normal
    (l : Fin 6 → ℝ) (hl : ∀ k, 0 < l k)
    (M : Matrix (Fin 4) (Fin 4) ℝ) (f : cutBody l → HyperbolicThreeSpace)
    (hf : ∀ w, ∃ y : W, y = (radial l w.val) ᵥ* M ∧
      lorentz y y = -1 ∧ 0 < y 3 ∧
      (f w).coordinates.val = WithLp.toLp 2
        (Complex.mk (y 0/(y 3-y 2)) (y 1/(y 3-y 2)), 1/(y 3-y 2)))
    (ξ : cutBody l) (N : W)
    (hplane : lorentz (ξ.val ᵥ* M) N = 0) (hunit : lorentz N N = 1) :
    let p := nativeCoordinates (f ξ)
    (liftMatrix p).mulVec (coordinateNormal p N) = N ∧
      dotProduct (coordinateNormal p N) (coordinateNormal p N) / (p 2)^2 = 1 ∧
      ∀ a : V, lorentz ((liftMatrix p).mulVec a) N = 0 →
        dotProduct a (coordinateNormal p N) / (p 2)^2 = 0 := by
  let p := nativeCoordinates (f ξ)
  have hp : p 2 ≠ 0 := (f ξ).coordinates.property.ne'
  obtain ⟨y,hy,hu,ht,hc⟩ := hf ξ
  have hL : coordinateLift p = y := by
    change lift (f ξ) = y
    exact lift_of_coordinates _ y hu ht hc
  have hradial : radial l ξ.val =
      (Real.sqrt (-gramQuadratic l ξ.val))⁻¹ • ξ.val := by
    ext i
    simp [radial, div_eq_mul_inv, mul_comm]
  have horth : lorentz (coordinateLift p) N = 0 := by
    rw [hL,hy,hradial,Matrix.smul_vecMul]
    have he : ∀ (a : ℝ) (u : W), lorentz (a • u) N = a * lorentz u N := by
      intro a u
      simp [lorentz, Fin.sum_univ_four, smul_eq_mul]
      ring
    rw [he,hplane,mul_zero]
  exact ⟨coordinateNormal_lift p N hp horth,
    coordinateNormal_unit p N hp horth hunit,
    fun a ha => coordinateNormal_orthogonal p a N hp horth ha⟩

-- The positive height preserves whichever side of the plane was selected.
-- The weighted scalar identity by itself is not a surface-integral theorem.
theorem conformal_normal_flux_density (h : ℝ) (hh : h ≠ 0) (v n : V) :
    (dotProduct v (h • n) / h^2) * (h^2)⁻¹ =
      (dotProduct v n) / h^3 := by
  rw [dotProduct_smul]
  simp only [smul_eq_mul]
  field_simp [hh]
  <;> ring

end CFMPNativePlaneNormal435Transient
