/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicCubeStrippedTwist
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: An exact cubic-block quadratic twist removes the cube factor from the discriminant. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicCubeStrippedTwist
open WeierstrassCurve
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic

def stripped {R : Type*} [CommRing R] (l c r : R) : WeierstrassCurve R :=
  ⟨0,0,0,-3*c*r,2*r*l⟩

/-- Cubic block powers can be removed from the entire discriminant by one
quadratic twist followed by integral rescaling. -/
theorem stripped_discriminant {R : Type*} [CommRing R] (l c r : R)
    (h : l^2+3=c^3*r) :
    (stripped l c r).Δ = (72*r)^2 := by
  simp [stripped, WeierstrassCurve.Δ, b₂, b₄, b₆, b₈]
  linear_combination -(1728*r^2)*h

theorem is_twist_stripped {F : Type*} [Field F] (l c r : F)
    (hc : c ≠ 0) (h : l^2+3=c^3*r) :
    (⟨Units.mk0 c hc,0,0,0⟩ : VariableChange F) • model l c = stripped l c r := by
  rw [variableChange_def]
  ext <;> simp [model, stripped, Units.val_inv_eq_inv_val]
  · rw [h]
    field_simp
  · rw [h]
    field_simp

/-- In the hypothetical square-times-cube case, the actual Q-quadratic
twist has a short integral model with good reduction at Q, even though
the original model has Q in its discriminant. -/
theorem square_cube_twist_good_at_cube_prime {q : ℕ} [Fact q.Prime]
    (hq : 3 < q) (l p : ℤ) (hP : ¬ (q:ℤ) ∣ p)
    (h : l^2+3=p^2*(q:ℤ)^3) :
    (stripped l (q:ℤ) (p^2)).Δ = (72*p^2)^2 ∧
    ((stripped l (q:ℤ) (p^2)).map (Int.castRingHom (ZMod q))).Δ ≠ 0 := by
  have hh : l^2+3=(q:ℤ)^3*p^2 := by rw [h]; ring
  have H := stripped_discriminant l (q:ℤ) (p^2) hh
  refine ⟨H,?_⟩
  rw [WeierstrassCurve.map_Δ, H]
  have hp : (p:ZMod q) ≠ 0 := fun h =>
    hP ((ZMod.intCast_zmod_eq_zero_iff_dvd p q).mp h)
  have hsmall (x : ℕ) (hx : 0 < x) (hxq : x < q) : (x:ZMod q) ≠ 0 :=
    fun hx' => (Nat.not_dvd_of_pos_of_lt hx hxq) ((ZMod.natCast_eq_zero_iff x q).mp hx')
  have h72 : (72:ZMod q) ≠ 0 := by
    rw [show (72:ZMod q)=2^3*3^2 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ (hsmall 2 (by decide) (by omega)))
      (pow_ne_zero _ (hsmall 3 (by decide) hq))
  simpa only [Int.coe_castRingHom, Int.cast_pow, Int.cast_mul, Int.cast_ofNat] using
    (pow_ne_zero 2 (mul_ne_zero h72 (pow_ne_zero 2 hp)))

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicCubeStrippedTwist
