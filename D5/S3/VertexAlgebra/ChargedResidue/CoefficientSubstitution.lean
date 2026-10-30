/- GID: D5/S3/VertexAlgebra/ChargedResidue/CoefficientSubstitution
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/CoefficientSubstitution
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Coefficient change of variables includes its formal Jacobian. -/

import D5.S3.VertexAlgebra.ChargedResidue.JointDiagonal
import Mathlib.RingTheory.PowerSeries.Derivative

/-! Formal coefficients are invariant under a unit-linear coordinate change with Jacobian. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open scoped BigOperators
noncomputable section
open PowerSeries

private theorem inverse_power_derivative (u : (PowerSeries ℂ)ˣ) (n : ℕ) :
    derivative (((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^n) =
      -(n : ℂ) • ((((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(n+1)) *
        derivative (u : PowerSeries ℂ)) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [derivative_pow, derivative_inv]
    simp only [Nat.succ_sub_one, Algebra.smul_def, map_neg, map_natCast]
    ring

private theorem constant_jacobian (u : (PowerSeries ℂ)ˣ) (n : ℕ) :
    coeff (n+1) (((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(n+2) *
      derivative (X * (u : PowerSeries ℂ))) = 0 := by
  let w : PowerSeries ℂ := ((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)
  have wu : w * (u : PowerSeries ℂ) = 1 := by simp [w]
  have factor : w^(n+2) * derivative (X * (u : PowerSeries ℂ)) =
      w^(n+1) + X * (w^(n+2) * derivative (u : PowerSeries ℂ)) := by
    rw [derivative.leibniz, derivative_X]
    simp only [smul_eq_mul, mul_one]
    calc
      _ = w^(n+1) * (w * (u : PowerSeries ℂ)) +
          X * (w^(n+2) * derivative (u : PowerSeries ℂ)) := by ring
      _ = _ := by rw [wu, mul_one]
  change coeff (n+1) (w^(n+2) * derivative (X * (u : PowerSeries ℂ))) = 0
  rw [factor, map_add, show n+1 = n+1 by rfl, ← pow_one (X : PowerSeries ℂ), coeff_X_pow_mul]
  have h := congrArg (coeff n) (inverse_power_derivative u (n+1))
  change coeff n (derivative (w^(n+1))) =
    coeff n (-((n+1 : ℕ) : ℂ) • (w^(n+1+1) * derivative (u : PowerSeries ℂ))) at h
  rw [coeff_derivative, map_smul] at h
  simp only [Nat.cast_add, Nat.cast_one] at h
  have nonzero : (n+1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [smul_eq_mul] at h
  have hzero : (n+1 : ℂ) * (coeff (n+1) (w^(n+1)) +
      coeff n (w^(n+2) * derivative (u : PowerSeries ℂ))) = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp hzero).resolve_left nonzero

/- proof_shape: coeff_subst_jacobian: content
   admission_basis: escape-witness
   escape_witness: The constant-series Jacobian term vanishes in each positive
   degree by the derivative of the corresponding inverse unit power. Splitting
   off the constant term then inducts on the selected coefficient, with no
   restriction on the input series.
   literature_status: classical formal residue change of variables. -/
theorem coeff_subst_jacobian (f : PowerSeries ℂ) (u : (PowerSeries ℂ)ˣ) (n : ℕ) :
    coeff n (f.subst (X * (u : PowerSeries ℂ)) *
      (((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(n+1)) *
        derivative (X * (u : PowerSeries ℂ))) = coeff n f := by
  have hh : HasSubst (X * (u : PowerSeries ℂ)) := by
    apply HasSubst.of_constantCoeff_zero'
    simp
  induction n generalizing f with
  | zero =>
    simp only [Nat.zero_add, pow_one, coeff_zero_eq_constantCoeff, map_mul,
      derivative.leibniz, derivative_X, smul_eq_mul, mul_one, map_add,
      constantCoeff_X, zero_mul, add_zero]
    have hc : constantCoeff (f.subst (X * (u : PowerSeries ℂ))) = constantCoeff f := by
      apply constantCoeff_subst_of_constantCoeff_zero
      change constantCoeff (X * (u : PowerSeries ℂ)) = 0
      simp
    rw [hc, zero_add, mul_assoc, ← map_mul, show ((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) * (u : PowerSeries ℂ) = 1 from by simp, map_one, mul_one]
  | succ n ih =>
    let g := mk fun i => coeff (i+1) f
    have split : f = C (constantCoeff f) + X * g := by
      have h := eq_X_pow_mul_shift_add_trunc 1 f
      simpa [g, add_comm] using h
    conv_lhs => rw [split]
    rw [subst_add hh, subst_C, subst_mul hh, subst_X hh,
      add_mul, add_mul, map_add]
    have first : coeff (n+1) (C (constantCoeff f) *
        (((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(n+1+1)) *
        derivative (X * (u : PowerSeries ℂ))) = 0 := by
      rw [mul_assoc, coeff_C_mul, constant_jacobian, mul_zero]
    change coeff (n+1) (C (constantCoeff f) *
        (((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(n+1+1)) *
        derivative (X * (u : PowerSeries ℂ))) + _ = _
    rw [first, zero_add]
    have factor : (X * (u : PowerSeries ℂ) * g.subst (X * (u : PowerSeries ℂ))) *
        (((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(n+1+1)) *
        derivative (X * (u : PowerSeries ℂ)) =
      X * (g.subst (X * (u : PowerSeries ℂ)) *
        (((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(n+1)) *
        derivative (X * (u : PowerSeries ℂ))) := by
      rw [pow_succ]
      have uw : (u : PowerSeries ℂ) * ((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = 1 :=
        by simp
      linear_combination X * g.subst (X * (u : PowerSeries ℂ)) *
        (((u⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(n+1)) *
        derivative (X * (u : PowerSeries ℂ)) * uw
    rw [factor, ← pow_one (X : PowerSeries ℂ), coeff_X_pow_mul]
    simp only [pow_one]
    rw [ih]
    simp only [g, coeff_mk]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
