/- GID: D5/S3/Arith/ModularForms/CubicThetaRootProduct
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaRootProduct
   mirror-E: none(waiver:formal-cubic-root-jacobi-product)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: The actual Jacobi product at a cubic root reduces to a dilated Euler product. -/

import D5.S3.Arith.ModularForms.CubicThetaJacobi
import Mathlib.RingTheory.PowerSeries.Expand

/-! Cubic-root specialization by finite factors and coefficientwise convergence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ModularForms.CubicThetaRootProduct

open CubicThetaJacobi
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

theorem cubic_factor {R : Type*} [CommRing R] (w t : R)
    (hw : w ^ 2 + w + 1 = 0) :
    (1 - t) * (1 - w * t) * (1 - w ^ 2 * t) = 1 - t ^ 3 := by
  have h3 : w ^ 3 = 1 := by linear_combination (w - 1) * hw
  linear_combination (t ^ 2 - t) * hw + (t ^ 2 - t ^ 3) * h3

private theorem mapped_inverse {R : Type*} [CommRing R]
    (f : LaurentPolynomial ℚ →+* R)
    (hw : f (LaurentPolynomial.T 1) ^ 2 + f (LaurentPolynomial.T 1) + 1 = 0) :
    f (LaurentPolynomial.T (-1)) = f (LaurentPolynomial.T 1) ^ 2 := by
  let w := f (LaurentPolynomial.T 1)
  let v := f (LaurentPolynomial.T (-1))
  have hu : w * v = 1 := by
    dsimp [w, v]
    rw [← map_mul, ← LaurentPolynomial.T_add]
    norm_num [LaurentPolynomial.T_zero]
  have h3 : w ^ 3 = 1 := by dsimp [w]; linear_combination (f (LaurentPolynomial.T 1) - 1) * hw
  change v = w ^ 2
  calc
    v = v * w ^ 3 := by rw [h3]; ring
    _ = (w * v) * w ^ 2 := by ring
    _ = w ^ 2 := by rw [hu, one_mul]

/-- An exact finite factorization, before any limit or division is taken. -/
theorem finite_cubic_root_product {R : Type*} [CommRing R]
    (f : LaurentPolynomial ℚ →+* R)
    (hw : f (LaurentPolynomial.T 1) ^ 2 + f (LaurentPolynomial.T 1) + 1 = 0)
    (cutoff : ℕ) :
    PowerSeries.map f
      ((∏ earlier ∈ Finset.range cutoff,
          (1 - PowerSeries.X ^ (earlier + 1) : PowerSeries (LaurentPolynomial ℚ))) *
        finiteEulerEvaluation (cutoff + 1) 0 (LaurentPolynomial.T 1) *
        finiteEulerEvaluation cutoff 1 (LaurentPolynomial.T (-1))) =
      PowerSeries.C (1 - f (LaurentPolynomial.T 1)) *
        ∏ earlier ∈ Finset.range cutoff,
          (1 - PowerSeries.X ^ (3 * (earlier + 1)) : PowerSeries R) := by
  classical
  rw [finiteEulerEvaluation_eq_prod, finiteEulerEvaluation_eq_prod]
  simp only [map_mul, map_prod, map_sub, map_one, map_pow, PowerSeries.map_X,
    PowerSeries.map_C, Nat.add_zero, mapped_inverse f hw]
  rw [Finset.prod_range_succ']
  simp only [pow_zero, mul_one]
  have hf (earlier : ℕ) :
      (1 - PowerSeries.X ^ (earlier + 1)) *
        (1 - PowerSeries.C (f (LaurentPolynomial.T 1)) * PowerSeries.X ^ (earlier + 1)) *
        (1 - PowerSeries.C (f (LaurentPolynomial.T 1) ^ 2) * PowerSeries.X ^ (earlier + 1)) =
      (1 - PowerSeries.X ^ (3 * (earlier + 1)) : PowerSeries R) := by
    have hwC : (PowerSeries.C (f (LaurentPolynomial.T 1)) : PowerSeries R) ^ 2 +
        PowerSeries.C (f (LaurentPolynomial.T 1)) + 1 = 0 := by
      simpa only [map_add, map_pow, map_one, map_zero] using congrArg PowerSeries.C hw
    simpa only [map_pow, ← pow_mul, Nat.mul_comm (earlier + 1) 3] using
      cubic_factor (PowerSeries.C (f (LaurentPolynomial.T 1)))
        ((PowerSeries.X : PowerSeries R) ^ (earlier + 1)) hwC
  rw [show (1 - PowerSeries.C (f (LaurentPolynomial.T 1)) : PowerSeries R) =
    PowerSeries.C (1 - f (LaurentPolynomial.T 1)) by simp]
  calc
    _ = PowerSeries.C (1 - f (LaurentPolynomial.T 1)) *
        ((∏ earlier ∈ Finset.range cutoff, (1 - PowerSeries.X ^ (earlier + 1))) *
         (∏ earlier ∈ Finset.range cutoff,
           (1 - PowerSeries.C (f (LaurentPolynomial.T 1)) * PowerSeries.X ^ (earlier + 1))) *
         (∏ earlier ∈ Finset.range cutoff,
           (1 - PowerSeries.C (f (LaurentPolynomial.T 1) ^ 2) * PowerSeries.X ^ (earlier + 1)))) := by
      simp only [map_pow]
      ring
    _ = _ := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      simp_rw [hf]

theorem map_tendsto {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace S]
    (f : R →+* S) {g : ℕ → PowerSeries R} {a : PowerSeries R}
    (hg : Filter.Tendsto g Filter.atTop (nhds a)) :
    Filter.Tendsto (fun n => PowerSeries.map f (g n)) Filter.atTop
      (nhds (PowerSeries.map f a)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hg ⊢
  intro degree
  have hf : Continuous f := continuous_of_discreteTopology
  simpa only [PowerSeries.coeff_map, Function.comp_def] using (hf.tendsto _).comp (hg degree)

theorem tendsto_expand_three {R : Type*} [CommRing R] [TopologicalSpace R]
    {g : ℕ → PowerSeries R} {a : PowerSeries R}
    (hg : Filter.Tendsto g Filter.atTop (nhds a)) :
    Filter.Tendsto (fun n => PowerSeries.expand 3 (by decide) (g n)) Filter.atTop
      (nhds (PowerSeries.expand 3 (by decide) a)) := by
  rw [PowerSeries.WithPiTopology.tendsto_iff_coeff_tendsto] at hg ⊢
  intro degree
  by_cases hd : 3 ∣ degree
  · obtain ⟨k, rfl⟩ := hd
    simpa only [PowerSeries.coeff_expand_mul] using hg k
  · simp only [PowerSeries.coeff_expand_of_not_dvd 3 (by decide) _ hd]
    exact tendsto_const_nhds

/-- Jacobi's actual formal product at a cubic root is (1-w)E(X^3).
The algebraic root condition is used only to factor finite products. -/
theorem jacobi_cubic_root_product {R : Type*} [CommRing R]
    [TopologicalSpace R] [T2Space R] [IsTopologicalRing R]
    (f : LaurentPolynomial ℚ →+* R)
    (hw : f (LaurentPolynomial.T 1) ^ 2 + f (LaurentPolynomial.T 1) + 1 = 0) :
    PowerSeries.map f jacobiSeries =
      PowerSeries.C (1 - f (LaurentPolynomial.T 1)) *
        PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries R) := by
  letI : TopologicalSpace (LaurentPolynomial ℚ) := ⊥
  letI : DiscreteTopology (LaurentPolynomial ℚ) := ⟨rfl⟩
  have hleft := map_tendsto f tendsto_finite_jacobi_successor
  simp_rw [finite_cubic_root_product f hw] at hleft
  have hright := (tendsto_expand_three
    (PowerSeries.WithPiTopology.hasProd_one_sub_X_pow R).tendsto_prod_nat).const_mul
      (PowerSeries.C (1 - f (LaurentPolynomial.T 1)))
  simp only [map_prod, map_sub, map_one, map_pow, PowerSeries.expand_X, ← pow_mul,
    Nat.mul_comm _ 3] at hright
  exact tendsto_nhds_unique hleft (by simpa only [map_sub, map_one] using hright)

end D5.S3.Arith.ModularForms.CubicThetaRootProduct
