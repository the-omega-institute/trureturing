/- GID: D5/S3/Arith/ModularForms/CubicThetaProductTwist
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaProductTwist
   mirror-E: none(waiver:formal-jacobi-cubic-product-twist)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Three root-twisted actual Jacobi products factor by exact finite products. -/

import D5.S3.Arith.ModularForms.CubicThetaCoreProduct

/-! Root twists are ring evaluations on finite Laurent polynomials, followed by genuine limits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaProductTwist

open CubicThetaJacobi CubicThetaRootProduct
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

noncomputable def finiteFactor {R : Type*} [CommRing R] (cutoff shift : ℕ) (z : R) :
    PowerSeries R :=
  ∏ j ∈ Finset.range cutoff, (1 - PowerSeries.C z * PowerSeries.X ^ (j + shift))

noncomputable def finiteEuler (R : Type*) [CommRing R] (cutoff : ℕ) : PowerSeries R :=
  ∏ j ∈ Finset.range cutoff, (1 - PowerSeries.X ^ (j + 1))

noncomputable def finiteJacobi {R : Type*} [CommRing R]
    (g : ℚ →+* R) (z : Rˣ) (cutoff : ℕ) : PowerSeries R :=
  PowerSeries.map (LaurentPolynomial.eval₂ g z)
    (finiteEuler (LaurentPolynomial ℚ) cutoff *
      finiteEulerEvaluation (cutoff + 1) 0 (LaurentPolynomial.T 1) *
      finiteEulerEvaluation cutoff 1 (LaurentPolynomial.T (-1)))

noncomputable def jacobiEvaluation {R : Type*} [CommRing R]
    (g : ℚ →+* R) (z : Rˣ) : PowerSeries R :=
  PowerSeries.map (LaurentPolynomial.eval₂ g z) jacobiSeries

theorem finite_jacobi_eq {R : Type*} [CommRing R] (g : ℚ →+* R) (z : Rˣ) (cutoff : ℕ) :
    finiteJacobi g z cutoff = finiteEuler R cutoff *
      finiteFactor (cutoff + 1) 0 (z : R) * finiteFactor cutoff 1 (↑(z⁻¹) : R) := by
  simp only [finiteJacobi, finiteEuler, finiteFactor, finiteEulerEvaluation_eq_prod,
    map_mul, map_prod, map_sub, map_one, map_pow, PowerSeries.map_X, PowerSeries.map_C,
    LaurentPolynomial.eval₂_T, zpow_one, show (-1 : ℤ) = -(1 : ℤ) by rfl,
    zpow_neg]

/-- Finite factorization includes the zero-degree factor and both infinite-product directions. -/
theorem three_finite_factors {R : Type*} [CommRing R] (w z : R)
    (hw : w ^ 2 + w + 1 = 0) (cutoff shift : ℕ) :
    finiteFactor cutoff shift z * finiteFactor cutoff shift (w * z) *
      finiteFactor cutoff shift (w ^ 2 * z) =
      PowerSeries.expand 3 (by decide) (finiteFactor cutoff shift (z ^ 3)) := by
  classical
  have hwC : (PowerSeries.C w : PowerSeries R) ^ 2 + PowerSeries.C w + 1 = 0 := by
    simpa only [map_add, map_pow, map_one, map_zero] using congrArg PowerSeries.C hw
  unfold finiteFactor
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  simp only [map_sub, map_one, map_mul, map_pow, PowerSeries.expand_C, PowerSeries.expand_X]
  have h := cubic_factor (PowerSeries.C w) (PowerSeries.C z * PowerSeries.X ^ (j + shift)) hwC
  simpa only [map_mul, map_pow, mul_pow, ← pow_mul, mul_assoc,
    Nat.mul_comm 3 (j + shift)] using h

private theorem inverse_phase {R : Type*} [CommRing R] (w : Rˣ)
    (hw : (w : R) ^ 2 + w + 1 = 0) : (↑(w⁻¹) : R) = (w : R) ^ 2 := by
  have h3 : (w : R) ^ 3 = 1 := by linear_combination ((w : R) - 1) * hw
  calc
    (↑(w⁻¹) : R) = (↑(w⁻¹) : R) * (w : R) ^ 3 := by rw [h3]; ring
    _ = (w * (↑(w⁻¹) : R)) * (w : R) ^ 2 := by ring
    _ = (w : R) ^ 2 := by simp

theorem finite_three_jacobi {R : Type*} [CommRing R] (g : ℚ →+* R)
    (w z : Rˣ) (hw : (w : R) ^ 2 + w + 1 = 0) (cutoff : ℕ) :
    finiteJacobi g z cutoff * finiteJacobi g (w * z) cutoff *
      finiteJacobi g (w ^ 2 * z) cutoff *
      PowerSeries.expand 3 (by decide) (finiteEuler R cutoff) =
      finiteEuler R cutoff ^ 3 *
        PowerSeries.expand 3 (by decide) (finiteJacobi g (z ^ 3) cutoff) := by
  have h3 : (w : R) ^ 3 = 1 := by linear_combination ((w : R) - 1) * hw
  have hi := inverse_phase w hw
  have hi2 : (↑((w ^ 2)⁻¹) : R) = (w : R) := by
    rw [← inv_pow, Units.val_pow_eq_pow_val, hi]
    calc
      ((w : R) ^ 2) ^ 2 = (w : R) * (w : R) ^ 3 := by ring
      _ = (w : R) := by rw [h3, mul_one]
  simp only [finite_jacobi_eq, Units.val_mul, Units.val_pow_eq_pow_val,
    mul_inv_rev, hi, hi2]
  have hp := three_finite_factors (w : R) (z : R) hw (cutoff + 1) 0
  have hn := three_finite_factors (w : R) (↑(z⁻¹) : R) hw cutoff 1
  calc
    _ = finiteEuler R cutoff ^ 3 *
        (finiteFactor (cutoff + 1) 0 (z : R) *
          finiteFactor (cutoff + 1) 0 ((w : R) * z) *
          finiteFactor (cutoff + 1) 0 ((w : R) ^ 2 * z)) *
        (finiteFactor cutoff 1 (↑(z⁻¹) : R) *
          finiteFactor cutoff 1 ((w : R) * (↑(z⁻¹) : R)) *
          finiteFactor cutoff 1 ((w : R) ^ 2 * (↑(z⁻¹) : R))) *
        PowerSeries.expand 3 (by decide) (finiteEuler R cutoff) := by ring
    _ = _ := by
      rw [hp, hn]
      simp only [map_mul, ← inv_pow, Units.val_pow_eq_pow_val]
      ring

theorem tendsto_finite_jacobi_evaluation {R : Type*} [CommRing R]
    [TopologicalSpace R] (g : ℚ →+* R) (z : Rˣ) :
    Filter.Tendsto (finiteJacobi g z) Filter.atTop (nhds (jacobiEvaluation g z)) := by
  letI : TopologicalSpace (LaurentPolynomial ℚ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℚ) := ⟨rfl⟩
  exact map_tendsto (LaurentPolynomial.eval₂ g z) tendsto_finite_jacobi_successor

/-- The root-twisted product identity is obtained from finite factorizations without dividing. -/
theorem three_jacobi_product {R : Type*} [CommRing R]
    [TopologicalSpace R] [T2Space R] [IsTopologicalRing R]
    (g : ℚ →+* R) (w z : Rˣ) (hw : (w : R) ^ 2 + w + 1 = 0) :
    jacobiEvaluation g z * jacobiEvaluation g (w * z) *
      jacobiEvaluation g (w ^ 2 * z) *
      PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries R) =
      PowerSeries.pentagonalSeries R ^ 3 *
        PowerSeries.expand 3 (by decide) (jacobiEvaluation g (z ^ 3)) := by
  have hE := (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow R).tendsto_prod_nat
  have hleft := (((tendsto_finite_jacobi_evaluation g z).mul
    (tendsto_finite_jacobi_evaluation g (w * z))).mul
    (tendsto_finite_jacobi_evaluation g (w ^ 2 * z))).mul (tendsto_expand_three hE)
  have hright := (hE.pow 3).mul
    (tendsto_expand_three (tendsto_finite_jacobi_evaluation g (z ^ 3)))
  change Filter.Tendsto (fun n =>
    finiteJacobi g z n * finiteJacobi g (w * z) n * finiteJacobi g (w ^ 2 * z) n *
      PowerSeries.expand 3 (by decide) (finiteEuler R n)) Filter.atTop _ at hleft
  simp_rw [finite_three_jacobi g w z hw] at hleft
  exact tendsto_nhds_unique hleft hright

end D5.S3.Arith.ModularForms.CubicThetaProductTwist
