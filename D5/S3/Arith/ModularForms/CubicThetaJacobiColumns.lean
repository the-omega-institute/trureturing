/- GID: D5/S3/Arith/ModularForms/CubicThetaJacobiColumns
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaJacobiColumns
   mirror-E: none(waiver:formal-jacobi-cube-columns)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Exact integer lattice sums for the Laurent columns of the actual Jacobi cube. -/

import D5.S3.Arith.ModularForms.CubicThetaJacobiCube

/-! Projection to a fixed Laurent column retains the complete integer-pair sum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaJacobiColumns

open CubicThetaJacobi CubicThetaJacobiCube CubicThetaLattice CubicThetaShifted
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def cubeColumn (index : ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun degree => (PowerSeries.coeff degree (jacobiSeries ^ 3)).coeff index

theorem signs_add (a b c : ℤ) :
    (-1 : ℚ) ^ a.natAbs * (-1 : ℚ) ^ b.natAbs * (-1 : ℚ) ^ c.natAbs =
      (-1 : ℚ) ^ (a + b + c).natAbs := by
  have h : a.negOnePow * b.negOnePow * c.negOnePow = (a + b + c).negOnePow := by
    rw [Int.negOnePow_add, Int.negOnePow_add]
  have hh := congrArg (fun u : ℤˣ => ((u : ℤ) : ℚ)) h
  simpa only [Units.val_mul, Int.cast_mul, Int.coe_negOnePow] using hh

private theorem triple_term (p : (ℤ × ℤ) × ℤ) :
    jacobiTerm p.1.1 * jacobiTerm p.1.2 * jacobiTerm p.2 =
      PowerSeries.C (AddMonoidAlgebra.single (p.1.1 + p.1.2 + p.2)
        ((-1 : ℚ) ^ (p.1.1 + p.1.2 + p.2).natAbs)) *
      PowerSeries.X ^ (triangularExponent p.1.1 + triangularExponent p.1.2 +
        triangularExponent p.2) := by
  rw [← signs_add, ← AddMonoidAlgebra.single_mul_single,
    ← AddMonoidAlgebra.single_mul_single]
  simp only [jacobiTerm, map_mul, pow_add]
  ring

/-- Each Laurent column of the genuine cube is the full sum over two free integers. -/
theorem hasSum_cube_column (index : ℤ) [TopologicalSpace ℚ] :
    HasSum (fun p : ℤ × ℤ =>
      PowerSeries.C ((-1 : ℚ) ^ index.natAbs) *
        PowerSeries.X ^ (triangularExponent p.1 + triangularExponent p.2 +
          triangularExponent (index - p.1 - p.2))) (cubeColumn index) := by
  classical
  letI : UniformSpace (LaurentPolynomial ℚ) := ⊥
  letI : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro degree
  let project : LaurentPolynomial ℚ →+ ℚ :=
    { toFun := fun v => v.coeff index
      map_zero' := by simp
      map_add' := by intro a b; simp }
  have hraw := ((PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff _).mp
    hasSum_jacobi_cube) degree
  have hproject := hraw.map project continuous_of_discreteTopology
  let g : ℤ × ℤ → (ℤ × ℤ) × ℤ := fun p => (p, index - p.1 - p.2)
  have hg : Function.Injective g := by
    intro p q h
    exact congrArg Prod.fst h
  have hout (p : (ℤ × ℤ) × ℤ) (hp : p ∉ Set.range g) :
      project (PowerSeries.coeff degree
        (jacobiTerm p.1.1 * jacobiTerm p.1.2 * jacobiTerm p.2)) = 0 := by
    have hindex : p.1.1 + p.1.2 + p.2 ≠ index := by
      intro heq
      apply hp
      refine ⟨p.1, ?_⟩
      change (p.1, index - p.1.1 - p.1.2) = p
      apply Prod.ext
      · rfl
      · omega
    rw [triple_term, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
    split_ifs <;> simp only [project, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      mul_one, mul_zero, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      hindex, Ne.symm hindex, ite_false, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  have hpair := (hg.hasSum_iff hout).2 hproject
  change HasSum _ (PowerSeries.coeff degree (cubeColumn index))
  convert hpair using 1
  ext p
  dsimp [g, Function.comp_def]
  rw [triple_term ((p.1, p.2), index - p.1 - p.2)]
  have heq : p.1 + p.2 + (index - p.1 - p.2) = index := by omega
  rw [heq, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  split_ifs <;> simp only [project, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    mul_one, mul_zero, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    ite_true, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  simp only [cubeColumn, PowerSeries.coeff_mk]
  rfl

theorem triangular_zero_sum (p : ℤ × ℤ) :
    triangularExponent p.1 + triangularExponent p.2 + triangularExponent (-p.1 - p.2) =
      (eisensteinNorm p).toNat := by
  have h1 := twice_triangular p.1
  have h2 := twice_triangular p.2
  have h3 := twice_triangular (-p.1 - p.2)
  have hn := CubicThetaLattice.norm_nonneg p
  have hh : (triangularExponent p.1 : ℤ) + triangularExponent p.2 +
      triangularExponent (-p.1 - p.2) = eisensteinNorm p := by
    dsimp [eisensteinNorm]
    nlinarith
  omega

theorem triangular_one_sum (p : ℤ × ℤ) :
    triangularExponent p.1 + triangularExponent p.2 + triangularExponent (1 - p.1 - p.2) =
      (shiftedExponent p).toNat := by
  have h1 := twice_triangular p.1
  have h2 := twice_triangular p.2
  have h3 := twice_triangular (1 - p.1 - p.2)
  have hn := shifted_exponent_nonneg p
  have hh : (triangularExponent p.1 : ℤ) + triangularExponent p.2 +
      triangularExponent (1 - p.1 - p.2) = shiftedExponent p := by
    dsimp [shiftedExponent, eisensteinNorm]
    nlinarith
  omega

/-- The index-zero column of the actual Jacobi cube is the complete norm theta. -/
theorem cube_column_zero : cubeColumn 0 = normTheta := by
  letI : UniformSpace ℚ := ⊥
  letI : DiscreteUniformity ℚ := ⟨rfl⟩
  have h := hasSum_cube_column 0
  simp only [Int.natAbs_zero, pow_zero, map_one, one_mul, zero_sub] at h
  simp_rw [triangular_zero_sum] at h
  exact h.unique hasSum_lattice_theta.1

/-- The index-one column includes all three affine cosets, with the exact negative sign. -/
theorem cube_column_one : cubeColumn 1 = -(PowerSeries.C 3 * coreTheta) := by
  letI : UniformSpace ℚ := ⊥
  letI : DiscreteUniformity ℚ := ⟨rfl⟩
  have h := hasSum_cube_column 1
  simp only [Int.natAbs_one, pow_one, map_neg, map_one, neg_one_mul] at h
  simp_rw [triangular_one_sum] at h
  rw [← shifted_theta_eq_three_core]
  exact h.unique hasSum_shifted_theta.neg

end D5.S3.Arith.ModularForms.CubicThetaJacobiColumns
