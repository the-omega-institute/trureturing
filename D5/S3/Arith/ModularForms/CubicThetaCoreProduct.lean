/- GID: D5/S3/Arith/ModularForms/CubicThetaCoreProduct
   generality: G
   mirror-B: D5/B/S3/Arith/ModularForms/CubicThetaCoreProduct
   mirror-E: none(waiver:formal-three-core-product)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries]
   utility: none
   digest: The actual Euler quotient is the complete nonnegative three-core lattice theta. -/

import D5.S3.Arith.ModularForms.CubicThetaRootEvaluation
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.RingTheory.PowerSeries.Inverse

/-! The three-core product theorem follows from the complete cubic-root evaluation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Arith.ModularForms.CubicThetaCoreProduct

open CubicThetaJacobi CubicThetaRootProduct CubicThetaRootEvaluation CubicThetaLattice
open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

theorem map_pentagonal {S R : Type*} [CommRing S] [CommRing R] (g : S →+* R) :
    PowerSeries.map g (PowerSeries.pentagonalSeries S) = PowerSeries.pentagonalSeries R := by
  ext degree
  simp only [PowerSeries.coeff_map, PowerSeries.pentagonalSeries, PowerSeries.coeff_mk]
  split_ifs <;> simp only [Int.coe_negOnePow, map_pow, map_neg, map_one, map_zero]

abbrev RootRing := QuadraticAlgebra ℚ (-1) (-1)
abbrev w : RootRing := QuadraticAlgebra.omega

theorem root_equation : w ^ 2 + w + 1 = 0 := by
  rw [QuadraticAlgebra.omega_pow_two_eq_add]
  simp only [neg_smul, one_smul]
  ring

theorem root_cube : w ^ 3 = 1 := by
  calc
    w ^ 3 = (w - 1) * (w ^ 2 + w + 1) + 1 := by ring
    _ = 1 := by rw [root_equation]; ring

def rootUnit : RootRingˣ where
  val := w
  inv := w ^ 2
  val_inv := by simpa only [← pow_succ'] using root_cube
  inv_val := by simpa only [← pow_succ] using root_cube

noncomputable def rootEvaluation : LaurentPolynomial ℚ →+* RootRing :=
  LaurentPolynomial.eval₂ (algebraMap ℚ RootRing) rootUnit

theorem eval_T_one : rootEvaluation (LaurentPolynomial.T 1) = w := by
  simp only [rootEvaluation, LaurentPolynomial.eval₂_T, zpow_one]
  rfl

theorem eval_T_two : rootEvaluation (LaurentPolynomial.T 2) = w ^ 2 := by
  rw [show (LaurentPolynomial.T 2 : LaurentPolynomial ℚ) =
    LaurentPolynomial.T 1 ^ 2 by rw [LaurentPolynomial.T_pow]; norm_num]
  rw [map_pow, eval_T_one]

theorem eval_T_three : rootEvaluation (LaurentPolynomial.T 3) = 1 := by
  rw [show (LaurentPolynomial.T 3 : LaurentPolynomial ℚ) =
    LaurentPolynomial.T 1 ^ 3 by rw [LaurentPolynomial.T_pow]; norm_num]
  rw [map_pow, eval_T_one, root_cube]

private theorem root_scalar_unit : IsUnit (3 * (w ^ 2 - w)) := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  apply isUnit_iff_ne_zero.mpr
  norm_num [QuadraticAlgebra.norm_def, w, pow_two,
    QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]

private theorem root_scalar_cube : (1 - w) ^ 3 = 3 * (w ^ 2 - w) := by
  calc
    (1 - w) ^ 3 = 1 - w ^ 3 + 3 * (w ^ 2 - w) := by ring
    _ = 3 * (w ^ 2 - w) := by rw [root_cube]; ring

/-- The complete lattice theta times the actual Euler product is E(X^3)^3. -/
theorem coreTheta_mul_euler :
    coreTheta * PowerSeries.pentagonalSeries ℚ =
      (PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries ℚ)) ^ 3 := by
  letI : TopologicalSpace RootRing := ⊥
  letI : DiscreteTopology RootRing := ⟨rfl⟩
  let f := rootEvaluation
  let g := algebraMap ℚ RootRing
  have hfg : f.comp LaurentPolynomial.C = g := by
    apply RingHom.ext
    intro a
    exact LaurentPolynomial.eval₂_C (algebraMap ℚ RootRing) rootUnit a
  have hj := jacobi_cubic_root_product f (by rw [eval_T_one]; exact root_equation)
  have hc := evaluated_jacobi_cube f eval_T_three
  rw [eval_T_one] at hj
  rw [hfg, eval_T_one, eval_T_two, map_pow, hj, mul_pow, ← map_pow, root_scalar_cube] at hc
  have he : (PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries RootRing)) ^ 3 =
      PowerSeries.map g (coreTheta * PowerSeries.pentagonalSeries ℚ) :=
    (root_scalar_unit.map PowerSeries.C).mul_left_cancel hc
  apply (PowerSeries.map_injective g QuadraticAlgebra.C_injective)
  rw [← he, map_pow, PowerSeries.map_expand, map_pentagonal]

theorem euler_constant_one : PowerSeries.constantCoeff (PowerSeries.pentagonalSeries ℚ) = 1 := by
  calc
    _ = PowerSeries.coeff 0 (PowerSeries.pentagonalSeries ℚ) :=
      (PowerSeries.coeff_zero_eq_constantCoeff_apply _).symm
    _ = 1 := by
      have h := PowerSeries.coeff_pentagonalSeries_pentagonal ℚ 0
      rw [show _root_.pentagonal (0 : ℤ) = 0 by decide] at h
      simpa only [Int.coe_negOnePow, Int.natAbs_zero, pow_zero] using h

/-- This is the actual quotient, rather than a series defined to have nonnegative coefficients. -/
theorem core_product_eq_theta :
    (PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries ℚ)) ^ 3 *
      PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1 = coreTheta := by
  rw [← coreTheta_mul_euler, mul_assoc,
    PowerSeries.mul_invOfUnit _ 1 euler_constant_one, mul_one]

/-- Every normalized quotient coefficient counts the entire finite integer lattice fibre. -/
theorem coeff_core_product (n : ℕ) :
    PowerSeries.coeff n
      ((PowerSeries.expand 3 (by decide) (PowerSeries.pentagonalSeries ℚ)) ^ 3 *
        PowerSeries.invOfUnit (PowerSeries.pentagonalSeries ℚ) 1) =
      (Nat.card (CoreFiber n) : ℚ) := by
  rw [core_product_eq_theta]
  simp only [coreTheta, PowerSeries.coeff_mk]

end D5.S3.Arith.ModularForms.CubicThetaCoreProduct
