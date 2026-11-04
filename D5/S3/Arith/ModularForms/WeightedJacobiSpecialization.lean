/- GID: D5/S3/Arith/ModularForms/WeightedJacobiSpecialization
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/WeightedJacobiSpecialization
   mirror-E: none(waiver:weighted-jacobi-product)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: The full integer Jacobi sum equals its positive weighted product limit. -/

import D5.S3.Combinatorics.PowerSeries.LaurentSpecialization
import D5.S3.Arith.ModularForms.CubicThetaJacobiCube

/-! The substitution t=q^(a+1+r), z=q^r is made through the support cone.
In particular no unrestricted Laurent series is evaluated at q inverse. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.WeightedJacobiSpecialization

open D5.S3.Combinatorics.PowerSeries.LaurentSpecialization
open CubicThetaJacobi CubicThetaJacobiCube
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

private local instance : UniformSpace ℚ := ⊥
private local instance : DiscreteUniformity ℚ := ⟨rfl⟩
private local instance : UniformSpace (LaurentPolynomial ℚ) := ⊥
private local instance : DiscreteUniformity (LaurentPolynomial ℚ) := ⟨rfl⟩

theorem triangular_add_index_nonnegative (k : ℤ) :
    0 ≤ (triangularExponent k : ℤ) + k := by
  have ht := twice_triangular k
  have hm : 0 ≤ k * (k + 1) := by
    by_cases hk : 0 ≤ k
    · exact mul_nonneg hk (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  nlinarith

def weightedExponent (a r : ℕ) (k : ℤ) : ℕ :=
  (a + 1) * triangularExponent k + r * ((triangularExponent k : ℤ) + k).toNat

theorem twice_weightedExponent (a r : ℕ) (k : ℤ) :
    (2 : ℤ) * weightedExponent a r k =
      ((a : ℤ) + 1 + r) * k * (k - 1) + 2 * r * k := by
  have ht := twice_triangular k
  have hn := Int.toNat_of_nonneg (triangular_add_index_nonnegative k)
  simp only [weightedExponent, Nat.cast_add, Nat.cast_mul, Nat.cast_one, hn]
  linear_combination ((a : ℤ) + 1 + r) * ht

noncomputable def J (a r : ℕ) : PowerSeries ℚ := specialize a r jacobiSeries

/-- Every integer index is retained, with its quadratic degree and exact sign. -/
theorem hasSum_J (a r : ℕ) :
    HasSum (fun k : ℤ => PowerSeries.C ((-1 : ℚ) ^ k.natAbs) *
      PowerSeries.X ^ weightedExponent a r k) (J a r) := by
  have h := hasSum_jacobi.map (specializeAdd a r) (continuous_specialize a r)
  change HasSum (fun k => specialize a r (jacobiTerm k)) (J a r) at h
  convert h using 1
  funext k
  rw [jacobiTerm, LaurentPolynomial.single_eq_C_mul_T,
    specialize_monomial a r _ _ _ (triangular_add_index_nonnegative k)]
  rfl

noncomputable def finiteProduct (a r N : ℕ) : PowerSeries ℚ :=
  (∏ i ∈ Finset.range N, (1 - PowerSeries.X ^ ((a + 1 + r) * (i + 1)))) *
  (∏ i ∈ Finset.range N, (1 - PowerSeries.X ^ ((a + 1 + r) * i + r))) *
  (∏ i ∈ Finset.range N, (1 - PowerSeries.X ^ ((a + 1 + r) * i + a + 1)))

private theorem specialize_factor_zero (a r n : ℕ) :
    specialize a r (1 - (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ n) =
      1 - PowerSeries.X ^ ((a + 1 + r) * n) := by
  have h := specialize_factor a r n 0 (by omega)
  simpa only [LaurentPolynomial.T_zero, map_one, one_mul, add_zero,
    Int.toNat_natCast, zero_add, Nat.add_mul] using h

private theorem admissible_factor_zero (n : ℕ) :
    Admissible (1 - (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ n) := by
  simpa only [LaurentPolynomial.T_zero, map_one, one_mul] using
    admissible_factor n 0 (by omega)

private theorem specialize_factor_positive (a r n : ℕ) :
    specialize a r (1 - PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ n) =
      1 - PowerSeries.X ^ ((a + 1 + r) * n + r) := by
  rw [specialize_factor a r n 1 (by omega)]
  congr 2
  have hn : ((n : ℤ) + 1).toNat = n + 1 := by omega
  rw [hn]
  ring

private theorem specialize_factor_negative (a r n : ℕ) :
    specialize a r (1 - PowerSeries.C (LaurentPolynomial.T (-1)) *
      PowerSeries.X ^ (n + 1)) =
      1 - PowerSeries.X ^ ((a + 1 + r) * n + a + 1) := by
  rw [specialize_factor a r (n + 1) (-1) (by omega)]
  congr 2
  have hn : (((n + 1 : ℕ) : ℤ) + -1).toNat = n := by omega
  rw [hn]
  ring

private theorem specialize_finite (a r N : ℕ) :
    specialize a r
      ((∏ i ∈ Finset.range N,
        (1 - PowerSeries.X ^ (i + 1) : PowerSeries (LaurentPolynomial ℚ))) *
        finiteEulerEvaluation N 0 (LaurentPolynomial.T 1) *
        finiteEulerEvaluation N 1 (LaurentPolynomial.T (-1))) = finiteProduct a r N := by
  rw [finiteEulerEvaluation_eq_prod, finiteEulerEvaluation_eq_prod]
  simp only [Nat.add_zero]
  have h0 : ∀ i ∈ Finset.range N,
      Admissible (1 - (PowerSeries.X : PowerSeries (LaurentPolynomial ℚ)) ^ (i + 1)) :=
    fun i _ => admissible_factor_zero (i + 1)
  have hp : ∀ i ∈ Finset.range N,
      Admissible (1 - PowerSeries.C (LaurentPolynomial.T 1) * PowerSeries.X ^ i) :=
    fun i _ => admissible_factor i 1 (by omega)
  have hn : ∀ i ∈ Finset.range N,
      Admissible (1 - PowerSeries.C (LaurentPolynomial.T (-1)) *
        PowerSeries.X ^ (i + 1)) := fun i _ => admissible_factor (i + 1) (-1) (by omega)
  rw [specialize_mul a r
      (admissible_mul (admissible_prod _ _ h0) (admissible_prod _ _ hp))
      (admissible_prod _ _ hn),
    specialize_mul a r (admissible_prod _ _ h0) (admissible_prod _ _ hp),
    specialize_prod a r _ _ h0, specialize_prod a r _ _ hp, specialize_prod a r _ _ hn]
  simp only [specialize_factor_zero, specialize_factor_positive, specialize_factor_negative,
    finiteProduct]

/-- The actual finite Jacobi factors converge to the full integer weighted sum. -/
theorem tendsto_finiteProduct (a r : ℕ) :
    Filter.Tendsto (finiteProduct a r) Filter.atTop (nhds (J a r)) := by
  have h := (continuous_specialize a r).continuousAt.tendsto.comp tendsto_finite_jacobi
  simpa only [Function.comp_def, specialize_finite, J] using h

end D5.S3.Arith.ModularForms.WeightedJacobiSpecialization
