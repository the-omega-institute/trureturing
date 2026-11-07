/- GID: D5/S3/Arith/ModularForms/CubicThetaWeightedProduct
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaWeightedProduct
   mirror-E: none(waiver:formal-weighted-cubic-theta-product)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Constant Laurent projection identifies the weighted lattice theta with the actual Euler quotient. -/

import D5.S3.Arith.ModularForms.CubicThetaTwistedColumns

/-! The genuine twisted product and its complete Laurent constant column identify the actual weighted Euler quotient. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaWeightedProduct

open CubicThetaJacobi CubicThetaJacobiCube CubicThetaTwistedColumns
open CubicThetaWeightedNorm CubicThetaProductTwist CubicThetaCoreProduct CubicThetaLattice
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

/-- Laurent constant-column extraction commutes with multiplication by a scalar series. -/
theorem columnZero_mul_map {R : Type*} [CommRing R]
    (p : PowerSeries (LaurentPolynomial R)) (q : PowerSeries R) :
    columnZero (p * PowerSeries.map LaurentPolynomial.C q) = columnZero p * q := by
  classical
  ext n
  simp only [columnZero, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    PowerSeries.coeff_map, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    ← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.coeff_mul_single_zero]

/-- The cube-dilated Laurent variable has only its integer index zero in column zero. -/
theorem columnZero_jacobi_cube_variable {R : Type*} [CommRing R] (g : ℚ →+* R) :
    columnZero (jacobiEvaluation (LaurentPolynomial.C.comp g) (variableUnit R ^ 3)) = 1 := by
  classical
  letI : TopologicalSpace R := ⊥
  letI : DiscreteTopology R := ⟨rfl⟩
  letI : UniformSpace (LaurentPolynomial R) := ⊥
  letI : DiscreteUniformity (LaurentPolynomial R) := ⟨rfl⟩
  let f := LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp g) (variableUnit R ^ 3)
  have hterm (k : ℤ) : PowerSeries.map f (jacobiTerm k) =
      PowerSeries.C (AddMonoidAlgebra.single (3 * k) (g ((-1 : ℚ) ^ k.natAbs))) *
        PowerSeries.X ^ triangularExponent k := by
    simp only [jacobiTerm, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
    congr 2
    dsimp [f]
    rw [LaurentPolynomial.single_eq_C_mul_T, map_mul, LaurentPolynomial.eval₂_C,
      LaurentPolynomial.eval₂_T, ← zpow_natCast (variableUnit R) 3,
      ← zpow_mul, variable_zpow,
      LaurentPolynomial.single_eq_C_mul_T]
    simp only [RingHom.comp_apply, map_pow, Nat.cast_ofNat]
  ext degree
  simp only [columnZero, PowerSeries.coeff_mk, jacobiEvaluation]
  let project : LaurentPolynomial R →+ R :=
    { toFun := fun v => v.coeff 0
      map_zero' := by simp
      map_add' := by intro a b; simp }
  change project (PowerSeries.coeff degree (PowerSeries.map f jacobiSeries)) =
    PowerSeries.coeff degree (1 : PowerSeries R)
  have hraw := ((PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff _).mp
    (hasSum_map_jacobi f)) degree
  have hs := hraw.map project continuous_of_discreteTopology
  have hout (k : ℤ) (hk : k ∉ ({0} : Finset ℤ)) :
      project (PowerSeries.coeff degree (PowerSeries.map f (jacobiTerm k))) = 0 := by
    have hk0 : k ≠ 0 := by simpa only [Finset.mem_singleton] using hk
    have hne : 3 * k ≠ 0 := by omega
    rw [hterm, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp only [project, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      mul_one, mul_zero, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      hne, Ne.symm hne, ite_false, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have hf : HasSum (fun k : ℤ =>
      project (PowerSeries.coeff degree (PowerSeries.map f (jacobiTerm k))))
      (∑ k ∈ ({0} : Finset ℤ),
        project (PowerSeries.coeff degree (PowerSeries.map f (jacobiTerm k)))) :=
    hasSum_sum_of_ne_finset_zero hout
  have he := hs.unique hf
  have hz : project (PowerSeries.coeff degree (PowerSeries.map f (jacobiTerm 0))) =
      PowerSeries.coeff degree (1 : PowerSeries R) := by
    rw [hterm]
    simp only [project, hterm, triangularExponent, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      Int.natAbs_zero, pow_zero, map_one, mul_zero, Int.toNat_zero, le_refl, ite_true,
      Nat.choose_zero_succ, mul_one, PowerSeries.coeff_one]
    split_ifs with hd <;> simp [hd]
  rw [Finset.sum_singleton, hz] at he
  exact he


theorem columnZero_expand {R : Type*} [CommRing R]
    (p : PowerSeries (LaurentPolynomial R)) (d : ℕ) (hd : d ≠ 0) :
    columnZero (PowerSeries.expand d hd p) = PowerSeries.expand d hd (columnZero p) := by
  ext n
  by_cases hn : d ∣ n
  · obtain ⟨m, rfl⟩ := hn
    simp only [columnZero, PowerSeries.coeff_mk, PowerSeries.coeff_expand_mul]
  · simp only [columnZero, PowerSeries.coeff_mk,
      PowerSeries.coeff_expand_of_not_dvd d hd _ hn,
      AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- Taking the complete Laurent constant column proves the actual weighted product identity. -/
theorem weighted_theta_mul_euler {R : Type*} [CommRing R]
    (g : ℚ →+* R) (u : Rˣ) (hu : (u : R) ^ 2 + u + 1 = 0) :
    weightedNormTheta (LaurentPolynomial.eval₂ g u) *
      PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries R) =
      PowerSeries.pentagonalSeries R ^ 3 := by
  letI : UniformSpace (LaurentPolynomial R) := ⊥
  letI : DiscreteUniformity (LaurentPolynomial R) := ⟨rfl⟩
  have hu3 : (u : R) ^ 3 = 1 := by linear_combination ((u : R) - 1) * hu
  have hi : u⁻¹ = u ^ 2 := by
    apply Units.ext
    calc
      (↑(u⁻¹) : R) = (↑(u⁻¹) : R) * (u : R) ^ 3 := by rw [hu3]; ring
      _ = (u * (↑(u⁻¹) : R)) * (u : R) ^ 2 := by ring
      _ = (↑(u ^ 2) : R) := by simp
  have hw : (constantUnit u : LaurentPolynomial R) ^ 2 + constantUnit u + 1 = 0 := by
    change (LaurentPolynomial.C (u : R) : LaurentPolynomial R) ^ 2 +
      LaurentPolynomial.C (u : R) + 1 = 0
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg LaurentPolynomial.C hu
  have ht : twistedCube g u =
      jacobiEvaluation (LaurentPolynomial.C.comp g) (variableUnit R) *
        jacobiEvaluation (LaurentPolynomial.C.comp g) (constantUnit u * variableUnit R) *
        jacobiEvaluation (LaurentPolynomial.C.comp g) (constantUnit u ^ 2 * variableUnit R) := by
    simp only [twistedCube, twist, jacobiEvaluation, hi, constantUnit,
      map_pow, map_one, one_mul]
    ring
  have hp := three_jacobi_product (LaurentPolynomial.C.comp g)
    (constantUnit u) (variableUnit R) hw
  rw [← ht] at hp
  have hmap : PowerSeries.pentagonalSeries (LaurentPolynomial R) =
      PowerSeries.map LaurentPolynomial.C (PowerSeries.pentagonalSeries R) :=
    (map_pentagonal LaurentPolynomial.C).symm
  rw [hmap, ← PowerSeries.map_expand, ← map_pow] at hp
  have hc := congrArg columnZero hp
  rw [columnZero_mul_map, twisted_column_zero, mul_comm (PowerSeries.map _ _) _,
    columnZero_mul_map, columnZero_expand, columnZero_jacobi_cube_variable,
    map_one, one_mul] at hc
  exact hc

/-- The rational cubic dissection is identified with E(X)^3/E(X^3), not assumed. -/
theorem norm_dissection_mul_euler :
    (PowerSeries.expand 3 (by decide) normTheta -
      PowerSeries.C 3 * (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta)) *
      PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries ℚ) =
      PowerSeries.pentagonalSeries ℚ ^ 3 := by
  let g := algebraMap ℚ RootRing
  have h := weighted_theta_mul_euler g rootUnit root_equation
  have hf : (LaurentPolynomial.eval₂ g rootUnit).comp LaurentPolynomial.C = g := by
    apply RingHom.ext
    intro q
    exact LaurentPolynomial.eval₂_C g rootUnit q
  rw [weighted_norm_dissection (LaurentPolynomial.eval₂ g rootUnit)
    (by change rootEvaluation (LaurentPolynomial.T 1) ^ 2 +
          rootEvaluation (LaurentPolynomial.T 1) + 1 = 0
        rw [eval_T_one]
        exact root_equation)
    (by change rootEvaluation (LaurentPolynomial.T 3) = 1
        exact eval_T_three), hf] at h
  apply PowerSeries.map_injective g QuadraticAlgebra.C_injective
  simpa only [map_mul, map_pow, PowerSeries.map_expand, map_pentagonal] using h

end D5.S3.Arith.ModularForms.CubicThetaWeightedProduct
