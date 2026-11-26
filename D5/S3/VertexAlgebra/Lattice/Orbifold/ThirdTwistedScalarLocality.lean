import D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContractionReciprocity
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fin.VecNotation

/-!
Clearing the normalized order-three contraction at `T = y / x` and its
homogeneous form in the two cover coordinates.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction

open LatticeGeneratingFieldLocality (LatticeData Charge bilinear)
open scoped BigOperators LaurentSeries RatFunc

noncomputable section

variable (D : LatticeData) (g : Charge D ≃+ Charge D)

/-- The integral exponent of the factor indexed by `j`. -/
abbrev contractionOrbitExponent (a b : Charge D) (j : ℕ) : ℤ :=
  bilinear D ((g^[j]) a) b

/-- The largest negative part among the three integral orbit pairings. -/
def contractionLocalityOrder (a b : Charge D) : ℕ :=
  (Finset.range 3).sup fun j => (-contractionOrbitExponent D g a b j).toNat

theorem contractionLocalityOrder_add_nonneg (a b : Charge D) {j : ℕ}
    (hj : j ∈ Finset.range 3) :
    0 ≤ (contractionLocalityOrder D g a b : ℤ) + contractionOrbitExponent D g a b j := by
  have h : (-contractionOrbitExponent D g a b j).toNat ≤ contractionLocalityOrder D g a b :=
    Finset.le_sup (f := fun i => (-contractionOrbitExponent D g a b i).toNat) hj
  omega

/-- The two-variable numerator, with variable 0 for `x` and variable 1 for `y`.
At a sufficient order `N`, every displayed power is the exact exponent `N + e_j`. -/
def clearedContractionNumerator (u : ℂˣ) (a b : Charge D) (N : ℕ) :
    MvPolynomial (Fin 2) ℂ :=
  ∏ j ∈ Finset.range 3, (MvPolynomial.X 0 - MvPolynomial.C (↑(u ^ j) : ℂ) * MvPolynomial.X 1) ^
    ((N : ℤ) + contractionOrbitExponent D g a b j).toNat

theorem clearedContractionNumerator_eval {R : Type*} [CommRing R] (C : ℂ →+* R)
    (x y : R) (u : ℂˣ) (a b : Charge D) (N : ℕ) :
    MvPolynomial.eval₂Hom C ![x, y] (clearedContractionNumerator D g u a b N) =
      ∏ j ∈ Finset.range 3, (x - C (↑(u ^ j) : ℂ) * y) ^ ((N : ℤ) + contractionOrbitExponent D g a b j).toNat := by
  simp only [clearedContractionNumerator, map_prod, map_pow, map_sub, map_mul,
    MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, Matrix.cons_val_zero,
    Matrix.cons_val_one]

private theorem cubic_factorization {R : Type*} [CommRing R] (C : ℂ →+* R)
    {u : ℂˣ} (hu : IsPrimitiveRoot u 3) (x y : R) :
    x ^ 3 - y ^ 3 = ∏ j ∈ Finset.range 3, (x - C (↑(u ^ j) : ℂ) * y) := by
  have huC : IsPrimitiveRoot (u : ℂ) 3 := IsPrimitiveRoot.coe_units_iff.mpr hu
  have hsumC : 1 + (u : ℂ) + (u : ℂ) ^ 2 = 0 := by
    simpa only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one, zero_add]
      using huC.geom_sum_eq_zero (by decide : 1 < 3)
  have hsum : C (u : ℂ) + C (u : ℂ) ^ 2 = -1 := by
    have h : 1 + C (u : ℂ) + C (u : ℂ) ^ 2 = 0 := by
      simpa only [map_add, map_pow, map_one, map_zero] using congrArg C hsumC
    calc
      _ = (1 + C (u : ℂ) + C (u : ℂ) ^ 2) - 1 := by ring
      _ = _ := by rw [h, zero_sub]
  have hcube : C (u : ℂ) ^ 3 = 1 := by
    simpa only [map_pow, map_one] using congrArg C huC.pow_eq_one
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, pow_zero, pow_one,
    Units.val_one, Units.val_pow_eq_pow_val, map_pow, map_one]
  calc
    _ = (x - y) * (x ^ 2 + x * y + y ^ 2) := by ring
    _ = (x - y) * (x ^ 2 - x * y * (C (u : ℂ) + C (u : ℂ) ^ 2) +
          y ^ 2 * C (u : ℂ) ^ 3) := by rw [hsum, hcube]; ring
    _ = _ := by ring

/-- The actual locality multiplier clears the homogeneous rational contraction.
The field may contain independent indeterminates for the two cover variables. -/
theorem homogeneousContraction_clear {K : Type*} [Field K] (C : ℂ →+* K)
    (u : ℂˣ) (hu : IsPrimitiveRoot u 3) (a b : Charge D) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + contractionOrbitExponent D g a b j)
    (x y : K) (hxy : x ^ 3 - y ^ 3 ≠ 0) :
    (x ^ 3 - y ^ 3) ^ N * (∏ j ∈ Finset.range 3, (x - C (↑(u ^ j) : ℂ) * y) ^ contractionOrbitExponent D g a b j) =
      MvPolynomial.eval₂Hom C ![x, y] (clearedContractionNumerator D g u a b N) := by
  have hfactor := cubic_factorization C hu x y
  have hprod : (∏ j ∈ Finset.range 3, (x - C (↑(u ^ j) : ℂ) * y)) ≠ 0 := by
    rwa [← hfactor]
  rw [hfactor, ← Finset.prod_pow, ← Finset.prod_mul_distrib, clearedContractionNumerator_eval]
  apply Finset.prod_congr rfl
  intro j hj
  let f := x - C (↑(u ^ j) : ℂ) * y
  have hf : f ≠ 0 := Finset.prod_ne_zero_iff.mp hprod j hj
  change f ^ N * f ^ contractionOrbitExponent D g a b j = f ^ ((N : ℤ) + contractionOrbitExponent D g a b j).toNat
  calc
    _ = f ^ ((N : ℤ) + contractionOrbitExponent D g a b j) := by rw [zpow_add₀ hf, zpow_natCast]
    _ = _ := by
      rw [← zpow_natCast f ((N : ℤ) + contractionOrbitExponent D g a b j).toNat, Int.toNat_of_nonneg (hN j hj)]

/-- Restoring the factored cover monomial gives the homogeneous rational
contraction from the reciprocal product at `y / x`. -/
theorem rationalContraction_clear_homogeneous
    (u : ℂˣ) (hu : IsPrimitiveRoot u 3) (a b : Charge D) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + contractionOrbitExponent D g a b j)
    (x y : RatFunc ℂ) (hx : x ≠ 0) (hxy : x ^ 3 - y ^ 3 ≠ 0) :
    (x ^ 3 - y ^ 3) ^ N *
        (x ^ (∑ j ∈ Finset.range 3, contractionOrbitExponent D g a b j) * rationalContraction D g u a b (y / x)) =
      MvPolynomial.eval₂Hom RatFunc.C ![x, y] (clearedContractionNumerator D g u a b N) := by
  have hsplit (j : ℕ) :
      x - RatFunc.C (↑(u ^ j) : ℂ) * y = x * (1 - RatFunc.C (↑(u ^ j) : ℂ) * (y / x)) := by
    have hcancel : x * (RatFunc.C (↑(u ^ j) : ℂ) * (y / x)) = RatFunc.C (↑(u ^ j) : ℂ) * y := by
      rw [div_eq_mul_inv]
      calc
        _ = (x * x⁻¹) * (RatFunc.C (↑(u ^ j) : ℂ) * y) := by ac_rfl
        _ = _ := by rw [mul_inv_cancel₀ hx, one_mul]
    rw [mul_sub, mul_one, hcancel]
  have hhom :
      (∏ j ∈ Finset.range 3, (x - RatFunc.C (↑(u ^ j) : ℂ) * y) ^ contractionOrbitExponent D g a b j) =
        x ^ (∑ j ∈ Finset.range 3, contractionOrbitExponent D g a b j) * rationalContraction D g u a b (y / x) := by
    simp_rw [hsplit, mul_zpow]
    rw [Finset.prod_mul_distrib, rationalContraction]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_range_succ,
      Finset.sum_range_zero, one_mul, zero_add, zpow_add₀ hx]
  rw [← hhom]
  exact homogeneousContraction_clear D g RatFunc.C u hu a b N hN x y hxy

/-- The cleared numerator in the ratio coordinate, obtained by setting
`x = 1` and `y = X` in the two-variable polynomial. -/
def clearedContractionTaylorPolynomial (u : ℂˣ) (a b : Charge D) (N : ℕ) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C ![1, Polynomial.X] (clearedContractionNumerator D g u a b N)

theorem rationalContraction_X_clear
    (u : ℂˣ) (hu : IsPrimitiveRoot u 3) (a b : Charge D) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + contractionOrbitExponent D g a b j) :
    (1 - RatFunc.X ^ 3) ^ N * rationalContraction D g u a b RatFunc.X =
      (clearedContractionTaylorPolynomial D g u a b N : RatFunc ℂ) := by
  have hpoly : (1 - Polynomial.X ^ 3 : Polynomial ℂ) ≠ 0 := by
    intro h
    have hzero := congrArg (Polynomial.constantCoeff (R := ℂ)) h
    have hX : Polynomial.constantCoeff (Polynomial.X : Polynomial ℂ) = 0 :=
      Polynomial.coeff_X_zero
    simp only [map_sub, map_one, map_pow, map_zero, hX, zero_pow (by decide : (3 : ℕ) ≠ 0),
      sub_zero, one_ne_zero] at hzero
  have hne : (1 - RatFunc.X ^ 3 : RatFunc ℂ) ≠ 0 := by
    simpa only [map_sub, map_one, map_pow, map_zero, RatFunc.algebraMap_X]
      using (RatFunc.algebraMap_injective ℂ).ne hpoly
  have heval :
      (clearedContractionTaylorPolynomial D g u a b N : RatFunc ℂ) =
        MvPolynomial.eval₂Hom RatFunc.C ![1, RatFunc.X] (clearedContractionNumerator D g u a b N) := by
    simp only [clearedContractionTaylorPolynomial, clearedContractionNumerator_eval,
      RatFunc.coePolynomial_eq_algebraMap, map_prod, map_pow, map_sub, map_one, map_mul,
      RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  simpa only [one_pow, one_zpow, one_mul, div_one, ← heval] using
    rationalContraction_clear_homogeneous D g u hu a b N hN 1 RatFunc.X one_ne_zero
      (by simpa only [one_pow] using hne)

/-- The cleared Taylor expansion is the same numerator as in the rational
identity. The unexpanded scalar product uses the existing binomial units. -/
theorem binomialContraction_X_clear
    (u : ℂˣ) (hu : IsPrimitiveRoot u 3) (a b : Charge D) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + contractionOrbitExponent D g a b j) :
    (1 - PowerSeries.X ^ 3) ^ N *
        (↑(∏ j ∈ Finset.range 3, binomialUnit (↑(u ^ j) : ℂ) ^ contractionOrbitExponent D g a b j) : PowerSeries ℂ) =
      (clearedContractionTaylorPolynomial D g u a b N : PowerSeries ℂ) := by
  have hX : algebraMap (RatFunc ℂ) (LaurentSeries ℂ) RatFunc.X = HahnSeries.single 1 1 :=
    RatFunc.coe_X
  have hmult :
      HahnSeries.ofPowerSeries ℤ ℂ ((1 - PowerSeries.X ^ 3) ^ N) =
        algebraMap (RatFunc ℂ) (LaurentSeries ℂ) ((1 - RatFunc.X ^ 3) ^ N) := by
    simp only [map_pow, map_one, map_sub, hX, HahnSeries.ofPowerSeries_X]
  have hbin := rationalContraction_X_expansion D g u a b
  change algebraMap (RatFunc ℂ) (LaurentSeries ℂ) (rationalContraction D g u a b RatFunc.X) =
    HahnSeries.ofPowerSeries ℤ ℂ
      (↑(∏ j ∈ Finset.range 3, binomialUnit (↑(u ^ j) : ℂ) ^ contractionOrbitExponent D g a b j) : PowerSeries ℂ) at hbin
  have h := congrArg (algebraMap (RatFunc ℂ) (LaurentSeries ℂ))
    (rationalContraction_X_clear D g u hu a b N hN)
  rw [map_mul] at h
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ)
  rw [map_mul, hmult, ← hbin]
  exact h.trans (RatFunc.coe_coe _).symm

/-- The cleared expansion in any ring receiving the Taylor series at `y / x`.
The left coordinate is a unit, so the orbit-sum monomial can have either sign. -/
theorem binomialContraction_clear_homogeneous {R : Type*} [CommRing R]
    (F : PowerSeries ℂ →+* R) (x : Rˣ) (y : R) (hy : (x : R) * F PowerSeries.X = y)
    (u : ℂˣ) (hu : IsPrimitiveRoot u 3) (a b : Charge D) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + contractionOrbitExponent D g a b j) :
    ((x : R) ^ 3 - y ^ 3) ^ N *
        ((↑(x ^ (∑ j ∈ Finset.range 3, contractionOrbitExponent D g a b j)) : R) *
          F (↑(∏ j ∈ Finset.range 3,
            binomialUnit (↑(u ^ j) : ℂ) ^ contractionOrbitExponent D g a b j) : PowerSeries ℂ)) =
      MvPolynomial.eval₂Hom (F.comp PowerSeries.C) ![(x : R), y]
        (clearedContractionNumerator D g u a b N) := by
  let e := contractionOrbitExponent D g a b
  let v (j : ℕ) := binomialUnit (↑(u ^ j) : ℂ)
  let f (j : ℕ) : Rˣ := x * Units.map F.toMonoidHom (v j)
  have hf (j : ℕ) : (f j : R) = (x : R) - F (PowerSeries.C (↑(u ^ j) : ℂ)) * y := by
    change (x : R) * F (binomialUnit (↑(u ^ j) : ℂ) : PowerSeries ℂ) = _
    rw [coe_binomialUnit, map_sub, map_one, map_mul, mul_sub, mul_one, ← hy]
    ring
  have hprod :
      (↑(∏ j ∈ Finset.range 3, f j ^ e j) : R) =
        (↑(x ^ (∑ j ∈ Finset.range 3, e j)) : R) * F (↑(∏ j ∈ Finset.range 3, v j ^ e j)) := by
    have hxpow : (∏ j ∈ Finset.range 3, x ^ e j) = x ^ (∑ j ∈ Finset.range 3, e j) := by
      simp only [Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_range_succ,
        Finset.sum_range_zero, one_mul, zero_add, zpow_add]
    have hv : (∏ j ∈ Finset.range 3, Units.map F.toMonoidHom (v j) ^ e j) =
        Units.map F.toMonoidHom (∏ j ∈ Finset.range 3, v j ^ e j) := by
      simp only [map_prod, map_zpow]
    simp only [f, mul_zpow, Finset.prod_mul_distrib, hxpow, hv, Units.val_mul, Units.coe_map]
    rfl
  have hmult : (x : R) ^ 3 - y ^ 3 = (↑(∏ j ∈ Finset.range 3, f j) : R) := by
    rw [cubic_factorization (F.comp PowerSeries.C) hu, Units.coe_prod]
    simp only [hf, RingHom.comp_apply]
  change _ ^ N * ((↑(x ^ (∑ j ∈ Finset.range 3, e j)) : R) *
    F (↑(∏ j ∈ Finset.range 3, v j ^ e j))) = _
  rw [hmult, ← hprod, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, Units.coe_prod, clearedContractionNumerator_eval]
  apply Finset.prod_congr rfl
  intro j hj
  have hpow : f j ^ N * f j ^ e j = f j ^ ((N : ℤ) + e j).toNat := by
    calc
      _ = f j ^ ((N : ℤ) + e j) := by rw [zpow_add, zpow_natCast]
      _ = _ := by rw [← zpow_natCast (f j) ((N : ℤ) + e j).toNat, Int.toNat_of_nonneg (hN j hj)]
  rw [hpow]
  simp only [Units.val_pow_eq_pow_val, hf, RingHom.comp_apply, e]

open P48qTwistedChargeAction (lattice)

local notation "ζ" => ThirdTwistedChargeCocycle.zeta

/-- The native contraction exponential after clearing in the ratio coordinate. -/
theorem scalar_contraction_X_clear (a b : Charge lattice) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3,
      0 ≤ (N : ℤ) + bilinear lattice ((P48qTwistedChargeAction.g^[j]) a) b) :
    (1 - PowerSeries.X ^ 3) ^ N * (PowerSeries.exp ℂ).subst (contractionExponent a b) =
      (clearedContractionTaylorPolynomial lattice P48qTwistedChargeAction.g ζ a b N : PowerSeries ℂ) := by
  rw [scalar_contraction]
  simpa only [Units.val_pow_eq_pow_val] using
    binomialContraction_X_clear lattice P48qTwistedChargeAction.g ζ
      ThirdTwistedChargeCocycle.zeta_primitive a b N hN

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedContraction
