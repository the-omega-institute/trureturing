/- GID: D5/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel
   generality: I
   mirror-B: D5/B/S3/Factorization/QuadraticIdeals/GoldenCubicNativeCenteredEllipticModel
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: The centered native cubic is Eisenstein and gives exact elliptic model coefficients. -/

import D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange

set_option autoImplicit false
namespace D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCenteredEllipticModel
open D5.S1.Scale D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCyclic
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeElliptic
open D5.S3.Factorization.QuadraticIdeals.GoldenCubicThueEisenstein
open WeierstrassCurve

def centered {R : Type*} [CommRing R] (l : R) : Cubic R :=
  ⟨1,3*l,-9,-3*l⟩

theorem centered_value {R : Type*} [CommRing R] (l z : R) :
    equation l (l+z)=z^3+3*l*z^2-9*z-3*l := by
  unfold equation
  ring

theorem native_centered_eisenstein (j : ℕ) (hj : 1 ≤ j) :
    ((centered (goldenLucas (3^j))).toPoly).IsEisensteinAt (Ideal.span ({3}:Set ℤ)) := by
  let l := goldenLucas (3^j)
  have hm := (native_lucas_mod j hj).1
  have H : EisensteinCoeffs 3 (centered l) := by
    refine ⟨rfl, ⟨l,rfl⟩, ⟨-3,by norm_num [centered]⟩,
      ⟨-l,by simp [centered,neg_mul]⟩,?_⟩
    intro h
    obtain ⟨k,hk⟩ := h
    have hd : l%3=1 := by dsimp [l]; omega
    change -3*l=3^2*k at hk
    norm_num at hk
    omega
  exact H.isEisensteinAt (by rw [Int.isUnit_iff]; decide)

/-- Translating to the actual three-adic cubic root and using its square
as change-of-variable unit yields four exact coefficient identities. -/
theorem local_model_coefficients {F : Type*} [Field F] (l z : F)
    (hz : z ≠ 0) (hroot : equation l (l+z)=0) :
    let C : VariableChange F := ⟨Units.mk0 (z^2) (pow_ne_zero _ hz),l+z,0,0⟩
    let W := C • model l 1
    W.a₂ = ((z^2)⁻¹)^2*(3*(l+z)) ∧
      W.a₄ = ((z^2)⁻¹)^4*(3*((l+z)^2-(l^2+3))) ∧
      W.a₆ = 0 ∧
      W.Δ = ((z^2)⁻¹)^12*(72*(l^2+3))^2 := by
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · simp [variableChange_a₂, model, Units.val_inv_eq_inv_val]
  · simp [variableChange_a₄, model, Units.val_inv_eq_inv_val, hz]
    ring
  · simp [variableChange_a₆, model, Units.val_inv_eq_inv_val, hz]
    unfold equation at hroot
    linear_combination hroot
  · simp [variableChange_Δ, model_discriminant, Units.val_inv_eq_inv_val]

end D5.S3.Factorization.QuadraticIdeals.GoldenCubicNativeCenteredEllipticModel
