/- GID: D5/S3/Arith/ModularForms/CubicThetaJacobi
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaJacobi
   mirror-E: none(waiver:formal-jacobi-product-specialization)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Finite product realizations of the repository Jacobi construction. -/

import D5.S3.Combinatorics.InversionSeq.InversionSeq207TripleProduct

/-! Coefficientwise finite-product specializations of the supplied Jacobi construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ModularForms.CubicThetaJacobi

open D5.S3.Combinatorics.InversionSeq.InversionSeq207Euler
open D5.S3.Combinatorics.InversionSeq.InversionSeq207TripleProduct
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def finiteEulerPolynomial (cutoff : ℕ) : Polynomial (PowerSeries ℚ) :=
  ∏ earlier ∈ Finset.range cutoff,
    (1 - Polynomial.C (PowerSeries.X ^ earlier) * Polynomial.X)

private theorem finiteEuler_step (cutoff : ℕ) :
    finiteEulerPolynomial (cutoff + 1) = finiteEulerPolynomial cutoff *
      (1 - Polynomial.C (PowerSeries.X ^ cutoff) * Polynomial.X) :=
  Finset.prod_range_succ _ cutoff

private theorem finiteEuler_stable (base extra degree index : ℕ) (hsmall : degree < base) :
    PowerSeries.coeff degree ((finiteEulerPolynomial (base + extra)).coeff index) =
      PowerSeries.coeff degree ((finiteEulerPolynomial base).coeff index) := by
  induction extra with
  | zero => simp
  | succ extra ih =>
      rw [show base + (extra + 1) = base + extra + 1 by omega, finiteEuler_step,
        mul_sub, mul_one, Polynomial.coeff_sub, map_sub]
      have hterm : PowerSeries.coeff degree
          ((finiteEulerPolynomial (base + extra) *
            (Polynomial.C (PowerSeries.X ^ (base + extra)) * Polynomial.X)).coeff
              index) = 0 := by
        rw [show finiteEulerPolynomial (base + extra) *
            (Polynomial.C (PowerSeries.X ^ (base + extra)) * Polynomial.X) =
              Polynomial.C (PowerSeries.X ^ (base + extra)) *
                (finiteEulerPolynomial (base + extra) * Polynomial.X) by ring,
          Polynomial.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
      rw [hterm, sub_zero, ih]

/-- The supplied Euler construction agrees with every sufficiently long finite product,
not just with a chosen numerical truncation. -/
theorem euler_coefficient_finite (degree index cutoff : ℕ) (hlarge : degree < cutoff) :
    PowerSeries.coeff degree (eulerCoefficients index) =
      PowerSeries.coeff degree ((finiteEulerPolynomial cutoff).coeff index) := by
  have h := euler_coefficient_construction.2.2.2.1 index
  rw [h, PowerSeries.coeff_mk]
  change PowerSeries.coeff degree ((finiteEulerPolynomial (degree + 1)).coeff index) = _
  have hc : cutoff = degree + 1 + (cutoff - (degree + 1)) := by omega
  rw [hc, finiteEuler_stable (degree + 1) _ degree index (by omega)]

private theorem finiteEuler_degree (cutoff : ℕ) :
    (finiteEulerPolynomial cutoff).natDegree ≤ cutoff := by
  induction cutoff with
  | zero => simp [finiteEulerPolynomial]
  | succ cutoff ih =>
      rw [finiteEuler_step]
      apply (Polynomial.natDegree_mul_le ..).trans
      have hf : (1 - Polynomial.C (PowerSeries.X ^ cutoff) * Polynomial.X :
          Polynomial (PowerSeries ℚ)).natDegree ≤ 1 := by
        apply (Polynomial.natDegree_sub_le ..).trans
        simp
      omega

/-- Evaluation in the Laurent variable is performed only on finite polynomials.
The growing cutoff is subsequently justified coefficientwise. -/
noncomputable def finiteEulerEvaluation (cutoff shift : ℕ)
    (z : LaurentPolynomial ℚ) : PowerSeries (LaurentPolynomial ℚ) :=
  (finiteEulerPolynomial cutoff).eval₂ (PowerSeries.map LaurentPolynomial.C)
    (PowerSeries.C z * PowerSeries.X ^ shift)

theorem finiteEulerEvaluation_eq_prod (cutoff shift : ℕ) (z : LaurentPolynomial ℚ) :
    finiteEulerEvaluation cutoff shift z =
      ∏ earlier ∈ Finset.range cutoff,
        (1 - PowerSeries.C z * PowerSeries.X ^ (earlier + shift)) := by
  simp only [finiteEulerEvaluation, finiteEulerPolynomial, Polynomial.eval₂_finset_prod,
    Polynomial.eval₂_sub, Polynomial.eval₂_one, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  apply Finset.prod_congr rfl
  intro earlier _
  rw [map_pow, PowerSeries.map_X, pow_add]
  ring

noncomputable def eulerEvaluation (shift : ℕ) (z : LaurentPolynomial ℚ) :
    PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.mk fun degree => ∑ index ∈ Finset.range (degree + 2),
    PowerSeries.coeff degree
      (PowerSeries.map LaurentPolynomial.C (eulerCoefficients index) *
        (PowerSeries.C z * PowerSeries.X ^ shift) ^ index)

private theorem finiteEulerEvaluation_coeff (degree cutoff shift : ℕ)
    (z : LaurentPolynomial ℚ) (hlarge : degree + 2 ≤ cutoff) :
    PowerSeries.coeff degree (finiteEulerEvaluation cutoff shift z) =
      PowerSeries.coeff degree (eulerEvaluation shift z) := by
  classical
  have hp := Polynomial.as_sum_range' (finiteEulerPolynomial cutoff) (cutoff + 1)
    (by have := finiteEuler_degree cutoff; omega)
  rw [finiteEulerEvaluation, hp, Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_monomial, map_sum]
  have heq (index : ℕ) :
      PowerSeries.coeff degree
        (PowerSeries.map LaurentPolynomial.C ((finiteEulerPolynomial cutoff).coeff index) *
          (PowerSeries.C z * PowerSeries.X ^ shift) ^ index) =
      PowerSeries.coeff degree
        (PowerSeries.map LaurentPolynomial.C (eulerCoefficients index) *
          (PowerSeries.C z * PowerSeries.X ^ shift) ^ index) := by
    simp only [PowerSeries.coeff_mul, PowerSeries.coeff_map]
    apply Finset.sum_congr rfl
    intro pair hpair
    rw [← euler_coefficient_finite pair.1 index cutoff (by
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
      omega)]
  simp_rw [heq]
  rw [eulerEvaluation, PowerSeries.coeff_mk]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro index _ hout
  have hi : degree + 2 ≤ index := by simpa using hout
  have hchoose : index - 1 ≤ index.choose 2 := by
    induction index with
    | zero => simp
    | succ index ih =>
        rw [show (index + 1).choose 2 = index + index.choose 2 by
          simpa using Nat.choose_succ_succ index 1]
        omega
  simp only [PowerSeries.coeff_mul, PowerSeries.coeff_map]
  apply Finset.sum_eq_zero
  intro pair hpair
  have hfirst := Finset.HasAntidiagonal.mem_antidiagonal.mp hpair
  rw [euler_coefficient_construction.2.2.1 pair.1 index (by omega), map_zero, zero_mul]

/-- The formal Euler evaluation is the coefficientwise limit of its actual finite products.
No unrestricted power-series substitution is used. -/
theorem tendsto_finiteEulerEvaluation (shift : ℕ) (z : LaurentPolynomial ℚ)
    [TopologicalSpace (LaurentPolynomial ℚ)] :
    Filter.Tendsto (fun cutoff => finiteEulerEvaluation cutoff shift z)
      Filter.atTop (nhds (eulerEvaluation shift z)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto]
  intro degree
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [Filter.eventually_ge_atTop (degree + 2)] with cutoff hcutoff
  exact finiteEulerEvaluation_coeff degree cutoff shift z hcutoff

theorem eulerEvaluation_zero_T : eulerEvaluation 0 (LaurentPolynomial.T 1) =
    eulerLaurentExpansion := by
  apply PowerSeries.ext
  intro degree
  simp only [eulerEvaluation, eulerLaurentExpansion, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro index _
  simp [PowerSeries.coeff_mul_C, ← map_pow, LaurentPolynomial.T_pow]

theorem eulerEvaluation_one_T : eulerEvaluation 1 (LaurentPolynomial.T 1) =
    shiftedEulerFactor := by
  apply PowerSeries.ext
  intro degree
  simp only [eulerEvaluation, shiftedEulerFactor, PowerSeries.coeff_mk]
  apply Finset.sum_congr rfl
  intro index _
  rw [mul_pow, ← map_pow]
  simp only [pow_one]
  rw [show PowerSeries.map LaurentPolynomial.C (eulerCoefficients index) *
      (PowerSeries.C (LaurentPolynomial.T 1 ^ index) * PowerSeries.X ^ index) =
        PowerSeries.map LaurentPolynomial.C (PowerSeries.X ^ index * eulerCoefficients index) *
          PowerSeries.C (LaurentPolynomial.T 1 ^ index) by
      simp only [map_mul, map_pow, PowerSeries.map_X]; ring]
  by_cases hi : index ≤ degree <;>
    simp [PowerSeries.coeff_mul_C, LaurentPolynomial.T_pow,
      PowerSeries.coeff_X_pow_mul', hi]

theorem eulerEvaluation_invert (shift : ℕ) (z : LaurentPolynomial ℚ) :
    eulerEvaluation shift (LaurentPolynomial.invert z) =
      PowerSeries.map LaurentPolynomial.invert.toRingHom (eulerEvaluation shift z) := by
  apply PowerSeries.ext
  intro degree
  simp only [eulerEvaluation, PowerSeries.coeff_mk, PowerSeries.coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [← PowerSeries.coeff_map]
  congr 1
  simp only [map_mul, map_pow, PowerSeries.map_C, PowerSeries.map_X]
  congr 1
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_map]

/-- The actual Laurent product supplier equals two separately justified Euler evaluations. -/
theorem formalTheta_eq_eulerEvaluations :
    formalTheta = eulerEvaluation 0 (LaurentPolynomial.T 1) *
      eulerEvaluation 1 (LaurentPolynomial.T (-1)) := by
  rw [eulerEvaluation_zero_T,
    show LaurentPolynomial.T (-1) = LaurentPolynomial.invert
      (LaurentPolynomial.T 1 : LaurentPolynomial ℚ) by simp,
    eulerEvaluation_invert, eulerEvaluation_one_T]
  rfl

/-- The Jacobi series is normalized by the actual pentagonal Euler product. -/
noncomputable def jacobiSeries : PowerSeries (LaurentPolynomial ℚ) :=
  PowerSeries.map LaurentPolynomial.C (PowerSeries.pentagonalSeries ℚ) * formalTheta

theorem map_euler :
    PowerSeries.map LaurentPolynomial.C (PowerSeries.pentagonalSeries ℚ) =
      PowerSeries.pentagonalSeries (LaurentPolynomial ℚ) := by
  apply PowerSeries.ext
  intro degree
  simp only [PowerSeries.coeff_map, PowerSeries.pentagonalSeries, PowerSeries.coeff_mk]
  split_ifs <;> simp

/-- The normalized Laurent series is a limit of the actual three Jacobi factors. -/
theorem tendsto_finite_jacobi
    [TopologicalSpace (LaurentPolynomial ℚ)] [IsTopologicalRing (LaurentPolynomial ℚ)] :
    Filter.Tendsto (fun cutoff =>
      (∏ earlier ∈ Finset.range cutoff,
        (1 - PowerSeries.X ^ (earlier + 1) : PowerSeries (LaurentPolynomial ℚ))) *
      finiteEulerEvaluation cutoff 0 (LaurentPolynomial.T 1) *
      finiteEulerEvaluation cutoff 1 (LaurentPolynomial.T (-1)))
      Filter.atTop (nhds jacobiSeries) := by
  have hE := (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow
    (LaurentPolynomial ℚ)).tendsto_prod_nat
  have hlimit := (hE.mul (tendsto_finiteEulerEvaluation 0 (LaurentPolynomial.T 1))).mul
    (tendsto_finiteEulerEvaluation 1 (LaurentPolynomial.T (-1)))
  simpa only [jacobiSeries, map_euler, formalTheta_eq_eulerEvaluations, mul_assoc] using hlimit

/-- Keeping one additional zero-shift factor has the same genuine Jacobi limit. -/
theorem tendsto_finite_jacobi_successor [TopologicalSpace (LaurentPolynomial ℚ)]
    [T2Space (LaurentPolynomial ℚ)] [IsTopologicalRing (LaurentPolynomial ℚ)] :
    Filter.Tendsto (fun cutoff =>
      (∏ earlier ∈ Finset.range cutoff,
        (1 - PowerSeries.X ^ (earlier + 1) : PowerSeries (LaurentPolynomial ℚ))) *
      finiteEulerEvaluation (cutoff + 1) 0 (LaurentPolynomial.T 1) *
      finiteEulerEvaluation cutoff 1 (LaurentPolynomial.T (-1)))
      Filter.atTop (nhds jacobiSeries) := by
  have hE := (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow
    (LaurentPolynomial ℚ)).tendsto_prod_nat
  have hshift := (tendsto_finiteEulerEvaluation 0 (LaurentPolynomial.T 1)).comp
    (Filter.tendsto_add_atTop_nat 1)
  have hJ := (hE.mul hshift).mul
    (tendsto_finiteEulerEvaluation 1 (LaurentPolynomial.T (-1)))
  simpa only [jacobiSeries, map_euler, formalTheta_eq_eulerEvaluations,
    mul_assoc, Function.comp_def] using hJ

/-- Every Laurent column of the actual product is the corresponding single Jacobi monomial. -/
theorem jacobiSeries_column (index : ℤ) :
    PowerSeries.mk (fun degree => (PowerSeries.coeff degree jacobiSeries).coeff index) =
      PowerSeries.C ((-1 : ℚ) ^ index.natAbs) *
        PowerSeries.X ^ (if 0 ≤ index then index.toNat.choose 2
          else (index.natAbs + 1).choose 2) := by
  rw [← formal_triple_product index]
  apply PowerSeries.ext
  intro degree
  simp only [jacobiSeries, PowerSeries.coeff_mk, PowerSeries.coeff_mul,
    PowerSeries.coeff_map, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro pair _
  change (AddMonoidAlgebra.single (0 : ℤ) _ * _).coeff index = _
  rw [AddMonoidAlgebra.coeff_single_zero_mul]

end D5.S3.Arith.ModularForms.CubicThetaJacobi
