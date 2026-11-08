/- GID: D5/S3/Arith/ModularForms/CubicThetaTwistedColumns
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaTwistedColumns
   mirror-E: none(waiver:formal-root-twisted-laurent-columns)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: The constant Laurent column of three twisted Jacobi series is the full weighted lattice theta. -/

import D5.S3.Arith.ModularForms.CubicThetaWeightedNorm
import D5.S3.Arith.ModularForms.CubicThetaProductTwist

/-! Local finiteness retains every integer triple, and Laurent constant projection gives the complete weighted lattice sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaTwistedColumns

open CubicThetaJacobi CubicThetaJacobiCube CubicThetaJacobiColumns CubicThetaLattice
open CubicThetaWeightedNorm CubicThetaProductTwist
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def variableUnit (R : Type*) [CommRing R] : (LaurentPolynomial R)ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [← LaurentPolynomial.T_add]; norm_num

noncomputable def constantUnit {R : Type*} [CommRing R] (u : Rˣ) : (LaurentPolynomial R)ˣ :=
  Units.map LaurentPolynomial.C.toMonoidHom u

theorem variable_zpow {R : Type*} [CommRing R] (k : ℤ) :
    (↑(variableUnit R ^ k) : LaurentPolynomial R) = LaurentPolynomial.T k := by
  cases k with
  | ofNat n =>
    rw [Int.ofNat_eq_natCast, zpow_natCast, Units.val_pow_eq_pow_val]
    change LaurentPolynomial.T 1 ^ n = _
    rw [LaurentPolynomial.T_pow]
    congr 1
    omega
  | negSucc n =>
    rw [show Int.negSucc n = -((n + 1 : ℕ) : ℤ) by omega,
      zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    change LaurentPolynomial.T (-1) ^ (n + 1) = _
    rw [LaurentPolynomial.T_pow]
    congr 1
    omega

noncomputable def twist {R : Type*} [CommRing R] (g : ℚ →+* R) (u : Rˣ) :
    LaurentPolynomial ℚ →+* LaurentPolynomial R :=
  LaurentPolynomial.eval₂ (LaurentPolynomial.C.comp g) (constantUnit u * variableUnit R)

theorem twist_single {R : Type*} [CommRing R] (g : ℚ →+* R) (u : Rˣ) (k : ℤ) (q : ℚ) :
    twist g u (AddMonoidAlgebra.single k q) =
      AddMonoidAlgebra.single k (g q * (↑(u ^ k) : R)) := by
  rw [LaurentPolynomial.single_eq_C_mul_T, twist, map_mul,
    LaurentPolynomial.eval₂_C, LaurentPolynomial.eval₂_T, mul_zpow, Units.val_mul,
    variable_zpow]
  have hc : (↑(constantUnit u ^ k) : LaurentPolynomial R) =
      LaurentPolynomial.C (↑(u ^ k) : R) := by
    rw [constantUnit, ← map_zpow, Units.coe_map]
    rfl
  rw [hc]
  change LaurentPolynomial.C (g q) * (LaurentPolynomial.C (↑(u ^ k) : R) *
    LaurentPolynomial.T k) = _
  rw [← mul_assoc, ← map_mul, LaurentPolynomial.single_eq_C_mul_T]

noncomputable def twistedCube {R : Type*} [CommRing R] (g : ℚ →+* R) (u : Rˣ) :
    PowerSeries (LaurentPolynomial R) :=
  PowerSeries.map (twist g u) jacobiSeries *
    PowerSeries.map (twist g u⁻¹) jacobiSeries * PowerSeries.map (twist g 1) jacobiSeries

noncomputable def columnZero {R : Type*} [CommRing R]
    (p : PowerSeries (LaurentPolynomial R)) : PowerSeries R :=
  PowerSeries.mk fun n => (PowerSeries.coeff n p).coeff 0

theorem twisted_triple_term {R : Type*} [CommRing R] (g : ℚ →+* R) (u : Rˣ)
    (p : (ℤ × ℤ) × ℤ) :
    PowerSeries.map (twist g u) (jacobiTerm p.1.1) *
      PowerSeries.map (twist g u⁻¹) (jacobiTerm p.1.2) *
      PowerSeries.map (twist g 1) (jacobiTerm p.2) =
    PowerSeries.C (AddMonoidAlgebra.single (p.1.1 + p.1.2 + p.2)
      (g ((-1 : ℚ) ^ (p.1.1 + p.1.2 + p.2).natAbs) *
        (↑(u ^ (p.1.1 - p.1.2)) : R))) *
      PowerSeries.X ^ (triangularExponent p.1.1 + triangularExponent p.1.2 +
        triangularExponent p.2) := by
  have hp : (↑(u ^ (p.1.1 - p.1.2)) : R) =
      (↑(u ^ p.1.1) : R) * (↑(u⁻¹ ^ p.1.2) : R) := by
    rw [inv_zpow, ← Units.val_mul, ← zpow_sub]
  have hm : PowerSeries.map (twist g u) (jacobiTerm p.1.1) *
      PowerSeries.map (twist g u⁻¹) (jacobiTerm p.1.2) *
      PowerSeries.map (twist g 1) (jacobiTerm p.2) =
      PowerSeries.C
        (AddMonoidAlgebra.single p.1.1
          (g ((-1 : ℚ) ^ p.1.1.natAbs) * (↑(u ^ p.1.1) : R)) *
        AddMonoidAlgebra.single p.1.2
          (g ((-1 : ℚ) ^ p.1.2.natAbs) * (↑(u⁻¹ ^ p.1.2) : R)) *
        AddMonoidAlgebra.single p.2 (g ((-1 : ℚ) ^ p.2.natAbs))) *
      PowerSeries.X ^ (triangularExponent p.1.1 + triangularExponent p.1.2 +
        triangularExponent p.2) := by
    simp only [jacobiTerm, map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X,
      twist_single, one_zpow, Units.val_one, mul_one, pow_add]
    ring
  rw [hm, AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single]
  apply congrArg (fun q : R => PowerSeries.C
    (AddMonoidAlgebra.single (p.1.1 + p.1.2 + p.2) q) *
      PowerSeries.X ^ (triangularExponent p.1.1 + triangularExponent p.1.2 +
        triangularExponent p.2))
  rw [← signs_add, map_mul, map_mul, hp]
  ring

/-- All integer pairs occur in the constant Laurent column, with their exact phase. -/
theorem hasSum_twisted_column_zero {R : Type*} [CommRing R] [TopologicalSpace R]
    (g : ℚ →+* R) (u : Rˣ) :
    HasSum (fun p : ℤ × ℤ => PowerSeries.C (↑(u ^ (p.1 - p.2)) : R) *
      PowerSeries.X ^ (eisensteinNorm p).toNat) (columnZero (twistedCube g u)) := by
  classical
  letI : UniformSpace (LaurentPolynomial R) := ⊥
  letI : DiscreteUniformity (LaurentPolynomial R) := ⟨rfl⟩
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro degree
  let project : LaurentPolynomial R →+ R :=
    { toFun := fun v => v.coeff 0
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hraw := ((PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff _).mp
    (hasSum_mapped_triple (twist g u) (twist g u⁻¹) (twist g 1))) degree
  have hproject := hraw.map project continuous_of_discreteTopology
  let e : ℤ × ℤ → (ℤ × ℤ) × ℤ := fun p => (p, -p.1 - p.2)
  have he : Function.Injective e := by
    intro p q h
    exact congrArg Prod.fst h
  have hout (p : (ℤ × ℤ) × ℤ) (hp : p ∉ Set.range e) :
      project (PowerSeries.coeff degree
        (PowerSeries.map (twist g u) (jacobiTerm p.1.1) *
          PowerSeries.map (twist g u⁻¹) (jacobiTerm p.1.2) *
          PowerSeries.map (twist g 1) (jacobiTerm p.2))) = 0 := by
    have hi : p.1.1 + p.1.2 + p.2 ≠ 0 := by
      intro hi
      apply hp
      exact ⟨p.1, Prod.ext rfl (by dsimp [e]; omega)⟩
    rw [twisted_triple_term, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp only [project, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      mul_one, mul_zero, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      hi, Ne.symm hi, ite_false, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have hpair := (he.hasSum_iff hout).2 hproject
  convert hpair using 1
  · ext p
    dsimp [e, Function.comp_def]
    rw [twisted_triple_term g u ((p.1, p.2), -p.1 - p.2)]
    have hi : p.1 + p.2 + (-p.1 - p.2) = 0 := by omega
    rw [hi, Int.natAbs_zero, pow_zero, map_one, one_mul, triangular_zero_sum,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp only [project, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      mul_one, mul_zero, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      ite_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  · simp only [columnZero, PowerSeries.coeff_mk]
    rfl

/-- The projected product is the full finite-fibre weighted theta. -/
theorem twisted_column_zero {R : Type*} [CommRing R] (g : ℚ →+* R) (u : Rˣ) :
    columnZero (twistedCube g u) = weightedNormTheta (LaurentPolynomial.eval₂ g u) := by
  letI : UniformSpace R := ⊥
  letI : DiscreteUniformity R := ⟨rfl⟩
  have h := hasSum_weighted_norm (LaurentPolynomial.eval₂ g u)
  simp only [LaurentPolynomial.eval₂_T] at h
  exact (hasSum_twisted_column_zero g u).unique h

end D5.S3.Arith.ModularForms.CubicThetaTwistedColumns
