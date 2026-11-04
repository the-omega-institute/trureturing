/- GID: D5/S3/Arith/ModularForms/CubicThetaRootEvaluation
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaRootEvaluation
   mirror-E: none(waiver:formal-cubic-root-evaluation)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: Complete Laurent-column grouping evaluates the Jacobi cube at a cubic root. -/

import D5.S3.Arith.ModularForms.CubicThetaResidueSums
import D5.S3.Arith.ModularForms.CubicThetaRootProduct
import Mathlib.Algebra.Ring.Periodic

/-! Cubic-root evaluation is justified coefficientwise by finite Laurent support. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaRootEvaluation

open CubicThetaJacobi CubicThetaJacobiColumns CubicThetaCubeDissection
open CubicThetaResidueSums CubicThetaLattice
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

def indexEquiv : (Fin 3 × ℤ) ≃ ℤ where
  toFun p := 3 * p.2 + p.1.val
  invFun k := (⟨(k % 3).toNat, by omega⟩, k / 3)
  left_inv p := by
    apply Prod.ext
    · apply Fin.ext
      dsimp
      have := p.1.isLt
      omega
    · dsimp
      have := p.1.isLt
      omega
  right_inv k := by dsimp; omega

theorem map_T_residue {R : Type*} [CommRing R] (f : LaurentPolynomial ℚ →+* R)
    (h3 : f (LaurentPolynomial.T 3) = 1) (m : ℤ) (r : ℤ) :
    f (LaurentPolynomial.T (3 * m + r)) = f (LaurentPolynomial.T r) := by
  have hp : Function.Periodic (fun k : ℤ => f (LaurentPolynomial.T k)) 3 := by
    intro k
    change f (LaurentPolynomial.T (k + 3)) = f (LaurentPolynomial.T k)
    rw [LaurentPolynomial.T_add, map_mul, h3, mul_one]
  have h := (hp.int_mul m) r
  simpa [mul_comm, add_comm] using h

/-- Evaluation of every Laurent column reconstructs the actual Jacobi cube. -/
theorem hasSum_evaluated_columns {R : Type*} [CommRing R] [TopologicalSpace R]
    (f : LaurentPolynomial ℚ →+* R) :
    HasSum (fun index : ℤ => PowerSeries.C (f (LaurentPolynomial.T index)) *
      PowerSeries.map (f.comp LaurentPolynomial.C) (cubeColumn index))
      (PowerSeries.map f (jacobiSeries ^ 3)) := by
  classical
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff]
  intro degree
  let v := PowerSeries.coeff degree (jacobiSeries ^ 3)
  have hv : (∑ k ∈ v.coeff.support, AddMonoidAlgebra.single k (v.coeff k)) = v :=
    AddMonoidAlgebra.sum_coeff_single v
  have hfinite : HasSum (fun k : ℤ => f (AddMonoidAlgebra.single k (v.coeff k)))
      (f v) := by
    have h := hasSum_sum_of_ne_finset_zero (L := .unconditional ℤ) (s := v.coeff.support)
      (f := fun k : ℤ => f (AddMonoidAlgebra.single k (v.coeff k))) (by
        intro k hk
        have hz : v.coeff k = 0 := Finsupp.notMem_support_iff.mp hk
        simp only [hz, AddMonoidAlgebra.single_zero, map_zero])
    simpa only [← map_sum, hv] using h
  convert hfinite using 1
  · funext k
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map,
      cubeColumn, PowerSeries.coeff_mk]
    change f (LaurentPolynomial.T k) * f (LaurentPolynomial.C (v.coeff k)) = _
    rw [← map_mul, mul_comm, ← LaurentPolynomial.single_eq_C_mul_T]
  · rfl

theorem hasSum_map {R : Type*} [CommRing R] [TopologicalSpace R]
    [TopologicalSpace ℚ] [DiscreteTopology ℚ]
    (g : ℚ →+* R) {a : PowerSeries ℚ} {p : ℤ → PowerSeries ℚ}
    (h : HasSum p a) : HasSum (fun m => PowerSeries.map g (p m)) (PowerSeries.map g a) := by
  rw [PowerSeries.WithPiTopology.hasSum_iff_hasSum_coeff] at h ⊢
  intro degree
  simp only [PowerSeries.coeff_map]
  convert (h degree).map g.toAddMonoidHom continuous_of_discreteTopology using 1
  funext m
  rfl

/-- The full evaluated cube uses all three residue sums, with their exact phases and signs. -/
theorem evaluated_jacobi_cube {R : Type*} [CommRing R] [TopologicalSpace R]
    [T2Space R] [IsTopologicalRing R] (f : LaurentPolynomial ℚ →+* R)
    (h3 : f (LaurentPolynomial.T 3) = 1) :
    PowerSeries.map f (jacobiSeries ^ 3) =
      PowerSeries.C (3 * (f (LaurentPolynomial.T 2) - f (LaurentPolynomial.T 1))) *
        PowerSeries.map (f.comp LaurentPolynomial.C)
          (coreTheta * PowerSeries.pentagonalSeries ℚ) := by
  letI : TopologicalSpace ℚ := ⊥
  letI : DiscreteTopology ℚ := ⟨rfl⟩
  have hzero (m : ℤ) : f (LaurentPolynomial.T (3 * m)) = 1 := by
    simpa only [add_zero, LaurentPolynomial.T_zero, map_one] using map_T_residue f h3 m 0
  let g := f.comp LaurentPolynomial.C
  let column (k : ℤ) := PowerSeries.C (f (LaurentPolynomial.T k)) *
    PowerSeries.map g (cubeColumn k)
  let total (r : Fin 3) : PowerSeries R :=
    if r = 0 then 0
    else if r = 1 then -(PowerSeries.C (f (LaurentPolynomial.T 1)) *
      PowerSeries.map g ((PowerSeries.C 3 * coreTheta) * PowerSeries.pentagonalSeries ℚ))
    else PowerSeries.C (f (LaurentPolynomial.T 2)) *
      PowerSeries.map g ((PowerSeries.C 3 * coreTheta) * PowerSeries.pentagonalSeries ℚ)
  have hfiber (r : Fin 3) : HasSum (fun m : ℤ => column (indexEquiv (r, m))) (total r) := by
    fin_cases r
    · have h := hasSum_map g hasSum_residue_zero
      have ht := h.mul_right (PowerSeries.map g normTheta)
      simpa [column, indexEquiv, Equiv.coe_fn_mk, Fin.val_zero, Nat.cast_zero,
        add_zero, cube_column_three_mul, map_mul, map_zero, zero_mul,
        hzero, LaurentPolynomial.T_zero, map_one, one_mul,
        total, ite_true, residueTerm, mul_assoc] using ht
    · have h := (hasSum_map g hasSum_residue_one).mul_right
        (PowerSeries.map g (PowerSeries.C 3 * coreTheta))
      have ht := (h.mul_left (PowerSeries.C (f (LaurentPolynomial.T 1)))).neg
      convert ht using 1
      · funext m
        simp only [column, indexEquiv, Equiv.coe_fn_mk, Fin.val_one, Nat.cast_one,
          cube_column_three_mul_add_one, map_neg, map_mul, map_T_residue f h3,
          residueTerm, mul_neg]
      · norm_num [total]
        ring
    · have h := (hasSum_map g hasSum_residue_two).mul_right
        (PowerSeries.map g (PowerSeries.C 3 * coreTheta))
      have ht := h.mul_left (PowerSeries.C (f (LaurentPolynomial.T 2)))
      convert ht using 1
      · funext m
        simp only [column, indexEquiv, Equiv.coe_fn_mk, Fin.val_ofNat, Nat.cast_ofNat,
          cube_column_three_mul_add_two, map_mul, map_T_residue f h3, residueTerm]
      · norm_num [total]
        ring
  have hall := indexEquiv.hasSum_iff.mpr (hasSum_evaluated_columns f)
  have hgroup := hall.prod_fiberwise hfiber
  have heq := hgroup.unique (hasSum_fintype total)
  simp [total, Fin.sum_univ_succ] at heq
  simp only [map_pow]
  rw [heq]
  dsimp [g]
  simp only [map_mul, map_ofNat, map_sub]
  ring

end D5.S3.Arith.ModularForms.CubicThetaRootEvaluation
