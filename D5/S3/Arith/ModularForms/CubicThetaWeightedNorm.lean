/- GID: D5/S3/Arith/ModularForms/CubicThetaWeightedNorm
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaWeightedNorm
   mirror-E: none(waiver:formal-root-weighted-norm-theta)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Six complete lattice cosets give the root-weighted norm theta dissection. -/

import D5.S3.Arith.ModularForms.CubicThetaRootEvaluation

/-! The full finite lattice fibres carry cubic phases, without a product identity as premise. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaWeightedNorm

open CubicThetaLattice CubicThetaRootEvaluation
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def weightedNormCoefficient {R : Type*} [CommRing R]
    (f : LaurentPolynomial ℚ →+* R) (n : ℕ) : R :=
  letI := Fintype.ofFinite (NormFiber n)
  ∑ p : NormFiber n, f (LaurentPolynomial.T (p.1.1 - p.1.2))

noncomputable def weightedNormTheta {R : Type*} [CommRing R]
    (f : LaurentPolynomial ℚ →+* R) : PowerSeries R :=
  PowerSeries.mk (weightedNormCoefficient f)

theorem phase_mod {R : Type*} [CommRing R] (f : LaurentPolynomial ℚ →+* R)
    (h3 : f (LaurentPolynomial.T 3) = 1) (k : ℤ) :
    f (LaurentPolynomial.T k) = f (LaurentPolynomial.T (k % 3)) := by
  convert map_T_residue f h3 (k / 3) (k % 3) using 1
  congr 2
  omega

/-- The entire root-weighted integer lattice sum has the finite-fibre coefficients. -/
theorem hasSum_weighted_norm {R : Type*} [CommRing R] [TopologicalSpace R]
    (f : LaurentPolynomial ℚ →+* R) :
    HasSum (fun p : ℤ × ℤ => PowerSeries.C (f (LaurentPolynomial.T (p.1 - p.2))) *
      PowerSeries.X ^ (eisensteinNorm p).toNat) (weightedNormTheta f) := by
  classical
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro degree
  letI := Fintype.ofFinite (NormFiber degree)
  let term (p : ℤ × ℤ) := PowerSeries.coeff degree
    (PowerSeries.C (f (LaurentPolynomial.T (p.1 - p.2))) *
      PowerSeries.X ^ (eisensteinNorm p).toNat)
  have hfinite : HasSum (fun p : NormFiber degree => term p.1)
      (weightedNormCoefficient f degree) := by
    have ht (p : NormFiber degree) : term p.1 = f (LaurentPolynomial.T (p.1.1 - p.1.2)) := by
      simp only [term, p.2, Int.toNat_natCast, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_X_pow, ite_true, mul_one]
    simp_rw [ht]
    exact hasSum_fintype _
  simp only [weightedNormTheta, PowerSeries.coeff_mk]
  exact (Subtype.val_injective.hasSum_iff (fun p hp => by
    have he : (eisensteinNorm p).toNat ≠ degree := by
      intro he
      apply hp
      exact ⟨⟨p, by have := Int.toNat_of_nonneg (norm_nonneg p); omega⟩, rfl⟩
    simp only [term, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow,
      if_neg (Ne.symm he), mul_zero])).1 hfinite

theorem weighted_norm_three_mul {R : Type*} [CommRing R]
    (f : LaurentPolynomial ℚ →+* R) (h3 : f (LaurentPolynomial.T 3) = 1) (n : ℕ) :
    weightedNormCoefficient f (3 * n) = (Nat.card (NormFiber n) : R) := by
  classical
  letI := Fintype.ofFinite (NormFiber (3 * n))
  have hphase (p : NormFiber (3 * n)) : f (LaurentPolynomial.T (p.1.1 - p.1.2)) = 1 := by
    have hm := norm_mod_three p.1
    rw [p.2] at hm
    have he : (p.1.1 - p.1.2) % 3 = 0 := by split_ifs at hm <;> omega
    rw [phase_mod f h3, he, LaurentPolynomial.T_zero, map_one]
  simp only [weightedNormCoefficient]
  simp_rw [hphase]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    ← Nat.card_eq_fintype_card, (norm_fiber_residue_counts n).1]

theorem weighted_norm_three_mul_add_one {R : Type*} [CommRing R]
    (f : LaurentPolynomial ℚ →+* R)
    (hw : f (LaurentPolynomial.T 1) ^ 2 + f (LaurentPolynomial.T 1) + 1 = 0)
    (h3 : f (LaurentPolynomial.T 3) = 1) (n : ℕ) :
    weightedNormCoefficient f (3 * n + 1) = -3 * (Nat.card (CoreFiber n) : R) := by
  classical
  letI := Fintype.ofFinite (NormFiber (3 * n + 1))
  letI := Fintype.ofFinite (CoreFiber n)
  have htwo : f (LaurentPolynomial.T 2) = f (LaurentPolynomial.T 1) ^ 2 := by
    rw [show (LaurentPolynomial.T 2 : LaurentPolynomial ℚ) =
      LaurentPolynomial.T 1 ^ 2 by rw [LaurentPolynomial.T_pow]; norm_num, map_pow]
  have hphase (p : Fin 6 × CoreFiber n) :
      f (LaurentPolynomial.T ((normCoreEquiv n p).1.1 - (normCoreEquiv n p).1.2)) =
        if p.1.val % 2 = 0 then f (LaurentPolynomial.T 2) else f (LaurentPolynomial.T 1) := by
    rw [phase_mod f h3, normCoreEquiv_coordinate_residue]
    split_ifs <;> rfl
  unfold weightedNormCoefficient
  rw [← (normCoreEquiv n).sum_comp]
  simp_rw [hphase]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  norm_num
  rw [htwo]
  linear_combination (3 * (Fintype.card (CoreFiber n) : R)) * hw

theorem weighted_norm_three_mul_add_two {R : Type*} [CommRing R]
    (f : LaurentPolynomial ℚ →+* R) (n : ℕ) : weightedNormCoefficient f (3 * n + 2) = 0 := by
  classical
  have hnone : IsEmpty (NormFiber (3 * n + 2)) := ⟨by
    intro p
    have hm := norm_mod_three p.1
    rw [p.2] at hm
    split_ifs at hm <;> omega⟩
  simp [weightedNormCoefficient]


/-- The full root-weighted lattice theta has the exact cubic dissection. -/
theorem weighted_norm_dissection {R : Type*} [CommRing R]
    (f : LaurentPolynomial ℚ →+* R)
    (hw : f (LaurentPolynomial.T 1) ^ 2 + f (LaurentPolynomial.T 1) + 1 = 0)
    (h3 : f (LaurentPolynomial.T 3) = 1) :
    weightedNormTheta f = PowerSeries.map (f.comp LaurentPolynomial.C)
      (PowerSeries.expand 3 (by decide) normTheta -
        PowerSeries.C 3 * (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta)) := by
  have hzero (m : ℕ) : PowerSeries.coeff (3 * m)
      (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta) = 0 := by
    cases m with
    | zero => simp
    | succ m =>
      rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega,
        PowerSeries.coeff_succ_X_mul]
      exact PowerSeries.coeff_expand_of_not_dvd 3 (by decide) coreTheta (by omega)
  have hone (m : ℕ) : PowerSeries.coeff (3 * m + 1)
      (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta) =
        PowerSeries.coeff m coreTheta := by
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_expand_mul]
  have htwo (m : ℕ) : PowerSeries.coeff (3 * m + 2)
      (PowerSeries.X * PowerSeries.expand 3 (by decide) coreTheta) = 0 := by
    rw [show 3 * m + 2 = (3 * m + 1) + 1 by omega,
      PowerSeries.coeff_succ_X_mul]
    exact PowerSeries.coeff_expand_of_not_dvd 3 (by decide) coreTheta (by omega)
  ext n
  have hc : (∃ m, n = 3 * m) ∨ (∃ m, n = 3 * m + 1) ∨ (∃ m, n = 3 * m + 2) := by
    have hlt := Nat.mod_lt n (by decide : 0 < 3)
    by_cases h0 : n % 3 = 0
    · exact Or.inl ⟨n / 3, by omega⟩
    by_cases h1 : n % 3 = 1
    · exact Or.inr (Or.inl ⟨n / 3, by omega⟩)
    · exact Or.inr (Or.inr ⟨n / 3, by omega⟩)
  rcases hc with ⟨m, rfl⟩ | ⟨m, rfl⟩ | ⟨m, rfl⟩
  · simp only [weightedNormTheta, PowerSeries.coeff_mk, PowerSeries.coeff_map]
    rw [map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_expand_mul, hzero,
      mul_zero, sub_zero, weighted_norm_three_mul f h3]
    simp only [normTheta, PowerSeries.coeff_mk, map_natCast]
  · simp only [weightedNormTheta, PowerSeries.coeff_mk, PowerSeries.coeff_map]
    rw [map_sub, PowerSeries.coeff_C_mul, hone,
      PowerSeries.coeff_expand_of_not_dvd 3 (by decide) normTheta (by omega),
      weighted_norm_three_mul_add_one f hw h3]
    simp only [coreTheta, PowerSeries.coeff_mk, zero_sub, map_neg, map_mul,
      map_ofNat, map_natCast]
    ring
  · simp only [weightedNormTheta, PowerSeries.coeff_mk, PowerSeries.coeff_map]
    rw [map_sub, PowerSeries.coeff_C_mul, htwo,
      PowerSeries.coeff_expand_of_not_dvd 3 (by decide) normTheta (by omega),
      mul_zero, sub_zero, map_zero, weighted_norm_three_mul_add_two]

end D5.S3.Arith.ModularForms.CubicThetaWeightedNorm
