/- GID: D5/S3/VertexAlgebra/ChargedResidue/QuadraticResidue
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/ChargedResidue/QuadraticResidue
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The quadratic collision coordinate transports coefficients with its Jacobian. -/

import D5.S3.VertexAlgebra.ChargedResidue.CoefficientSubstitution

/-! The quadratic coordinate is applied to the actual collision coefficients. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
open LatticeHalfFockChargedCollision
open PowerSeries
noncomputable section

private theorem coordinate_facts :
    (∀ a : ℤ,
      (binomialSeries (R := ℂ) ℂ ((a : ℂ)/2)).subst
          (X * (2+X) : PowerSeries ℂ) = binomialSeries (R := ℤ) ℂ a) ∧
    (collisionUnit : PowerSeries ℂ).subst (X * (2+X) : PowerSeries ℂ) =
      1 + (2 : ℂ)⁻¹ • (X : PowerSeries ℂ) := by
  let S := PowerSeries.binomialSeries (R := ℂ) ℂ (1/2 : ℂ)
  have square : S*S = (1+PowerSeries.X : PowerSeries ℂ) := by
    dsimp only [S]
    rw [← PowerSeries.binomialSeries_add, show (1/2 : ℂ)+1/2 = 1 by norm_num]
    simpa using (PowerSeries.binomialSeries_nat (R := ℂ) (A := ℂ) 1)
  have unit_value : (collisionUnit : PowerSeries ℂ) = (2 : ℂ)⁻¹ • (S+1) := by
    unfold collisionUnit
    exact IsUnit.unit_spec _
  let h : PowerSeries ℂ := PowerSeries.X * (2+PowerSeries.X)
  have hh : PowerSeries.HasSubst h := by
    apply PowerSeries.HasSubst.of_constantCoeff_zero'
    simp [h]
  have hOne : (1 : PowerSeries ℂ).subst h = 1 := by
    rw [← PowerSeries.coe_substAlgHom hh, map_one]
  have sqrt_coordinate : S.subst h = (1+PowerSeries.X : PowerSeries ℂ) := by
    have squares : (S.subst h)^2 = (1+PowerSeries.X : PowerSeries ℂ)^2 := by
      rw [← PowerSeries.subst_pow hh]
      have square' : S^2 = (1+PowerSeries.X : PowerSeries ℂ) := by
        simpa [pow_two] using square
      rw [square', PowerSeries.subst_add hh, hOne,
        PowerSeries.subst_X hh]
      dsimp [h]
      ring
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp squares with positive | negative
    · exact positive
    · have constant := congrArg PowerSeries.constantCoeff negative
      have const_left : PowerSeries.constantCoeff (S.subst h) = 1 := by
        change MvPowerSeries.constantCoeff (S.subst h) = 1
        rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero]
        · simp [S]
        · change PowerSeries.constantCoeff h = 0
          simp [h]
      rw [const_left] at constant
      norm_num at constant
  have unit_coordinate : (collisionUnit : PowerSeries ℂ).subst h =
      1 + (2 : ℂ)⁻¹ • (PowerSeries.X : PowerSeries ℂ) := by
    rw [unit_value, PowerSeries.subst_smul hh, PowerSeries.subst_add hh,
      sqrt_coordinate, hOne]
    simp only [smul_add]
    module
  have half_step (a : ℤ) :
      (PowerSeries.binomialSeries (R := ℂ) ℂ (((a+1 : ℤ) : ℂ)/2)).subst h =
        (PowerSeries.binomialSeries (R := ℂ) ℂ ((a : ℂ)/2)).subst h *
          (1+PowerSeries.X) := by
    have exponent : (((a+1 : ℤ) : ℂ)/2) = (a : ℂ)/2 + (1/2 : ℂ) := by
      push_cast
      ring
    rw [exponent, PowerSeries.binomialSeries_add, PowerSeries.subst_mul hh]
    exact congrArg ((PowerSeries.binomialSeries (R := ℂ) ℂ ((a : ℂ)/2)).subst h * ·)
      sqrt_coordinate
  have integer_step (a : ℤ) :
      PowerSeries.binomialSeries (R := ℤ) ℂ (a+1) =
        PowerSeries.binomialSeries (R := ℤ) ℂ a * (1+PowerSeries.X) := by
    rw [PowerSeries.binomialSeries_add]
    congr 1
    simpa using (PowerSeries.binomialSeries_nat (R := ℤ) (A := ℂ) 1)
  have binomial_coordinate (a : ℤ) :
      (PowerSeries.binomialSeries (R := ℂ) ℂ ((a : ℂ)/2)).subst h =
        PowerSeries.binomialSeries (R := ℤ) ℂ a := by
    refine Int.induction_on a ?_ ?_ ?_
    · simp only [Int.cast_zero, zero_div, PowerSeries.binomialSeries_zero, hOne]
    · intro i ih
      rw [half_step, integer_step, ih]
    · intro i ih
      have nonzero : (1+PowerSeries.X : PowerSeries ℂ) ≠ 0 := by
        intro equality
        have constant := congrArg PowerSeries.constantCoeff equality
        norm_num at constant
      apply mul_right_cancel₀ nonzero
      rw [← half_step, ← integer_step, show -(i : ℤ)-1+1 = -(i : ℤ) by omega, ih]
  exact ⟨binomial_coordinate, unit_coordinate⟩

/-- The unnormalized factor h/X for h=X(2+X). -/
def quadraticCoordinateUnit : (PowerSeries ℂ)ˣ :=
  (isUnit_iff_constantCoeff.mpr (show IsUnit (constantCoeff (2+X : PowerSeries ℂ)) from
    by rw [map_add, constantCoeff_X, map_ofNat]; norm_num)).unit

private theorem coordinate_unit_value : (quadraticCoordinateUnit : PowerSeries ℂ) = 2+X :=
  IsUnit.unit_spec _

/-- The normalized factor (2+X)/2 appearing in the actual collision unit. -/
def normalizedCoordinateUnit : (PowerSeries ℂ)ˣ :=
  (isUnit_iff_constantCoeff.mpr
    (show IsUnit (constantCoeff (1+(2 : ℂ)⁻¹ • (X : PowerSeries ℂ))) from
      by norm_num)).unit

private theorem normalized_unit_value : (normalizedCoordinateUnit : PowerSeries ℂ) =
    1+(2 : ℂ)⁻¹ • (X : PowerSeries ℂ) := IsUnit.unit_spec _

/- proof_shape: collision_scalar_jacobian: content
   admission_basis: escape-witness
   escape_witness: The collision unit and every signed half exponent are
   transported under the quadratic coordinate, while coefficient invariance
   contributes the inverse (N+1)st coordinate-unit power and derivative.
   literature_status: classical formal residue substitution. -/
theorem collision_scalar_jacobian (a B : ℤ) (N : ℕ) :
    collisionScalar a B N = coeff N
      (binomialSeries (R := ℤ) ℂ a *
        ((normalizedCoordinateUnit ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
        (((quadraticCoordinateUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(N+1)) *
        (2*(1+X))) := by
  have hh : HasSubst (X * (2+X) : PowerSeries ℂ) := by
    apply HasSubst.of_constantCoeff_zero'
    simp
  have mapped : Units.map (substAlgHom hh).toMonoidHom collisionUnit =
      normalizedCoordinateUnit := by
    apply Units.ext
    change (substAlgHom hh) (collisionUnit : PowerSeries ℂ) = (normalizedCoordinateUnit : PowerSeries ℂ)
    rw [coe_substAlgHom, coordinate_facts.2, normalized_unit_value]
  have transported :
      (((collisionUnit ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)).subst
        (X * (2+X) : PowerSeries ℂ) =
      ((normalizedCoordinateUnit ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) := by
    have equality := congrArg (fun v : (PowerSeries ℂ)ˣ => (v : PowerSeries ℂ))
      (map_zpow (Units.map (substAlgHom hh).toMonoidHom) collisionUnit (-2*B))
    rw [mapped] at equality
    change (substAlgHom hh) (((collisionUnit ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)) = _ at equality
    rw [coe_substAlgHom] at equality
    exact equality
  have jac := coeff_subst_jacobian
    (binomialSeries (R := ℂ) ℂ ((a : ℂ)/2) *
      ((collisionUnit ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ))
    quadraticCoordinateUnit N
  rw [coordinate_unit_value, subst_mul hh, coordinate_facts.1,
    transported] at jac
  have derivative_value : derivative (X * (2+X) : PowerSeries ℂ) = 2*(1+X) := by
    have two : (2 : PowerSeries ℂ) = 1+1 := by ring
    rw [derivative.leibniz, map_add, two, map_add, derivative_one, derivative_X]
    simp only [smul_eq_mul]
    ring
  rw [derivative_value] at jac
  exact jac.symm

/- proof_shape: collision_scalar_coordinate: content
   admission_basis: escape-witness
   escape_witness: The quadratic Jacobian and inverse coordinate power are
   combined with the collision-unit normalization before taking a coefficient.
   literature_status: classical formal residue substitution. -/
theorem collision_scalar_coordinate (a B : ℤ) (N : ℕ) :
    collisionScalar a B N = (2 : ℂ)^(2*B+1) *
      coeff N (binomialSeries (R := ℤ) ℂ (a+1) *
        ((quadraticCoordinateUnit ^ (-2*B-(N : ℤ)-1) : (PowerSeries ℂ)ˣ) :
          PowerSeries ℂ)) := by
  let c : (PowerSeries ℂ)ˣ := Units.map (C : ℂ →+* PowerSeries ℂ).toMonoidHom
    (Units.mk0 (2 : ℂ) (by norm_num))
  have normalized : normalizedCoordinateUnit = c⁻¹ * quadraticCoordinateUnit := by
    apply Units.ext
    simp only [Units.val_mul, normalized_unit_value, coordinate_unit_value]
    have cinv : ((c⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) = C ((2 : ℂ)⁻¹) := by
      simp [c]
    rw [cinv, Algebra.smul_def]
    have C2 : C (2 : ℂ) = (2 : PowerSeries ℂ) := map_ofNat C 2
    rw [mul_add, ← C2, ← map_mul]
    norm_num
  have powers :
      ((normalizedCoordinateUnit ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
        (((quadraticCoordinateUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(N+1)) =
      C ((2 : ℂ)^(2*B)) *
        ((quadraticCoordinateUnit ^ (-2*B-(N : ℤ)-1) : (PowerSeries ℂ)ˣ) :
          PowerSeries ℂ) := by
    rw [normalized, mul_zpow, Units.val_mul]
    have constant_power : ((c⁻¹ ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) =
        C ((2 : ℂ)^(2*B)) := by
      rw [inv_zpow, ← zpow_neg, show -(-2*B) = 2*B by ring]
      dsimp only [c]
      rw [← map_zpow]
      change ((Units.map (C : ℂ →+* PowerSeries ℂ).toMonoidHom)
        ((Units.mk0 (2 : ℂ) (by norm_num))^(2*B)) : PowerSeries ℂ) = _
      rw [Units.coe_map]
      exact congrArg C (Units.val_zpow_eq_zpow_val
        (Units.mk0 (2 : ℂ) (by norm_num)) (2*B))
    rw [constant_power, mul_assoc]
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    rw [← zpow_natCast, inv_zpow, ← zpow_neg, ← zpow_add]
    congr 1
    push_cast
    ring
  have step : binomialSeries (R := ℤ) ℂ (a+1) =
      binomialSeries (R := ℤ) ℂ a * (1+X) := by
    rw [binomialSeries_add]
    congr 1
    simpa using (binomialSeries_nat (R := ℤ) (A := ℂ) 1)
  rw [collision_scalar_jacobian]
  have rearrange : binomialSeries (R := ℤ) ℂ a *
      ((normalizedCoordinateUnit ^ (-2*B) : (PowerSeries ℂ)ˣ) : PowerSeries ℂ) *
      (((quadraticCoordinateUnit⁻¹ : (PowerSeries ℂ)ˣ) : PowerSeries ℂ)^(N+1)) *
      (2*(1+X)) =
    C ((2 : ℂ)^(2*B+1)) *
      (binomialSeries (R := ℤ) ℂ (a+1) *
        ((quadraticCoordinateUnit ^ (-2*B-(N : ℤ)-1) : (PowerSeries ℂ)ˣ) :
          PowerSeries ℂ)) := by
    rw [mul_assoc (binomialSeries (R := ℤ) ℂ a), powers, step,
      zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), zpow_one, map_mul]
    have two : C (2 : ℂ) = (2 : PowerSeries ℂ) := map_ofNat C 2
    rw [two]
    ring
  rw [rearrange, coeff_C_mul]

end
end D5.S3.VertexAlgebra.LatticeHalfFockChargedResidue
