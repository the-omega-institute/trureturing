/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeCocycle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The order-three charge multiplier and the divisibility criterion for its moving-charge commutator. -/

import D5.S3.VertexAlgebra.LatticeActualProductKernel
import D5.S3.VertexAlgebra.Lattice.CyclicIsometryLift
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
The formulas for `B` and `c` use the native integral form and lattice sign.
They are defined for any additive equivalence `g`.
For an order-three lattice isometry, `B` is the
product factor in (4.37) and `c(a,b) = ε(a,b) B(a,b)⁻¹`
is the coefficient in (4.42) of
Bojko Bakalov and Victor G. Kac, *Twisted Modules over Lattice Vertex Algebras*,
arXiv:math/0402315v3. Section 3.1 gives `ζ = exp(2πi/3)`, and (4.43) uses the
commutator order `U_a U_b U_a⁻¹ U_b⁻¹`.

For an isometry `g` with `g³ = 1`, write `N = 1 + g + g²`. The charge
`a - g a` has commutator phase `ζ^(-(N a,b))` against `b`. The phase is one
exactly when three divides the integral pairing `(N a,b)`.

For the order-three twist with the compatible normalized lift of (4.18)–(4.19),
the quotient relation (4.46) uses `U_(g a)⁻¹ U_a`, of charge `a - g a`.
Its commutator phase cancels the conjugation phase from the fixed part `N a / 3`
because their exponents have opposite signs.
-/

set_option autoImplicit false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle

open LatticeGeneratingFieldLocality
open LatticeActualGeneratorLocality
  (bilinear_add_right epsilon_add_left epsilon_add_right epsilon_skew)
open LatticeFiniteNegativeGeneration (bilinear_symmetric)
open CyclicIsometryLift (orbitNorm)

noncomputable section

/-- The primitive root in the Bakalov–Kac convention. -/
def zeta : ℂˣ :=
  Units.mk0 (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)) (Complex.exp_ne_zero _)

private theorem zeta_coe_primitive : IsPrimitiveRoot (zeta : ℂ) 3 := by
  simpa only [zeta, Units.val_mk0, Nat.cast_ofNat] using Complex.isPrimitiveRoot_exp 3 (by decide)

theorem zeta_primitive : IsPrimitiveRoot zeta 3 :=
  IsPrimitiveRoot.coe_units_iff.mp zeta_coe_primitive

private def firstFactor : ℂˣ :=
  Units.mk0 (1 - (zeta : ℂ)) (sub_ne_zero.mpr (zeta_coe_primitive.ne_one (by decide)).symm)

private def secondFactor : ℂˣ :=
  Units.mk0 (1 - (zeta : ℂ) ^ 2)
    (sub_ne_zero.mpr (zeta_coe_primitive.pow_ne_one_of_pos_of_lt
      (by decide : (2 : ℕ) ≠ 0) (by decide)).symm)

private def three : ℂˣ := Units.mk0 3 (by norm_num)

private def minusOne : ℂˣ := Units.mk0 (-1) (by norm_num)

private theorem coe_minusOne : (minusOne : ℂ) = -1 := rfl

private theorem secondFactor_eq : secondFactor = firstFactor * (minusOne * zeta⁻¹) := by
  have hinv : zeta⁻¹ = zeta ^ 2 := by
    symm
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, zeta_primitive.pow_eq_one]
  apply Units.ext
  change 1 - (zeta : ℂ) ^ 2 = (1 - (zeta : ℂ)) * ((-1 : ℂ) * (↑(zeta⁻¹) : ℂ))
  rw [hinv, Units.val_pow_eq_pow_val]
  calc
    1 - (zeta : ℂ) ^ 2 = (zeta : ℂ) ^ 3 - (zeta : ℂ) ^ 2 := by
      rw [zeta_coe_primitive.pow_eq_one]
    _ = _ := by ring

/-- The native epsilon viewed as a unit. -/
def epsilonUnit (D : LatticeData) (a b : Charge D) : ℂˣ :=
  minusOne ^ lowerCocycleExponent D a b

@[simp] theorem coe_epsilonUnit (D : LatticeData) (a b : Charge D) :
    (epsilonUnit D a b : ℂ) = epsilon D a b := by
  simp only [epsilonUnit, Units.val_zpow_eq_zpow_val, coe_minusOne, neg_one_zpow_eq_ite,
    epsilon, paritySign]

/-- The product factor in (4.37) when `g` is an order-three lattice isometry. -/
def B (D : LatticeData) (g : Charge D ≃+ Charge D) (a b : Charge D) : ℂˣ :=
  three ^ (-bilinear D a b) * firstFactor ^ bilinear D (g a) b *
    secondFactor ^ bilinear D (g (g a)) b

/-- The coefficient of `U_(a+b)` in (4.42) when `g` is an order-three lattice isometry. -/
def c (D : LatticeData) (g : Charge D ≃+ Charge D) (a b : Charge D) : ℂˣ :=
  epsilonUnit D a b * (B D g a b)⁻¹

private theorem bilinear_add_left (D : LatticeData) (a b t : Charge D) :
    bilinear D (a + b) t = bilinear D a t + bilinear D b t := by
  rw [bilinear_symmetric D (a + b) t, bilinear_add_right,
    bilinear_symmetric D t a, bilinear_symmetric D t b]

private theorem bilinear_sub_left (D : LatticeData) (a b t : Charge D) :
    bilinear D (a - b) t = bilinear D a t - bilinear D b t := by
  simp [bilinear, sub_mul, Finset.sum_sub_distrib]

theorem c_normalized (D : LatticeData) (g : Charge D ≃+ Charge D) (a : Charge D) :
    c D g 0 a = 1 ∧ c D g a 0 = 1 := by
  simp [c, B, epsilonUnit, lowerCocycleExponent, bilinear]

theorem c_add_left (D : LatticeData) (g : Charge D ≃+ Charge D) (a b t : Charge D) :
    c D g (a + b) t = c D g a t * c D g b t := by
  have hε : epsilonUnit D (a + b) t = epsilonUnit D a t * epsilonUnit D b t := by
    apply Units.ext
    simpa only [Units.val_mul, coe_epsilonUnit] using epsilon_add_left D a b t
  have hB : B D g (a + b) t = B D g a t * B D g b t := by
    simp only [B, map_add, bilinear_add_left, Int.neg_add, zpow_add]
    exact (congrArg (· * _) (mul_mul_mul_comm _ _ _ _)).trans (mul_mul_mul_comm _ _ _ _)
  simp only [c, hε, hB, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

theorem c_add_right (D : LatticeData) (g : Charge D ≃+ Charge D) (a b t : Charge D) :
    c D g a (b + t) = c D g a b * c D g a t := by
  have hε : epsilonUnit D a (b + t) = epsilonUnit D a b * epsilonUnit D a t := by
    apply Units.ext
    simpa only [Units.val_mul, coe_epsilonUnit] using epsilon_add_right D a b t
  have hB : B D g a (b + t) = B D g a b * B D g a t := by
    simp only [B, bilinear_add_right, Int.neg_add, zpow_add]
    exact (congrArg (· * _) (mul_mul_mul_comm _ _ _ _)).trans (mul_mul_mul_comm _ _ _ _)
  simp only [c, hε, hB, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

section Isometry

variable (D : LatticeData) (g : Charge D ≃+ Charge D)
variable (hg : ∀ a b, bilinear D (g a) (g b) = bilinear D a b)
variable (h3 : ∀ a, g (g (g a)) = a)

include hg in
/-- Applying the isometry to both charges preserves the product factor. -/
theorem B_isometry (a b : Charge D) : B D g (g a) (g b) = B D g a b := by
  simp only [B, hg a b, hg (g a) b, hg (g (g a)) b]

include hg h3 in
theorem pairing_shift_one (a b : Charge D) :
    bilinear D a (g b) = bilinear D (g (g a)) b := by
  simpa only [h3 a] using hg (g (g a)) b

include hg h3 in
theorem pairing_shift_two (a b : Charge D) :
    bilinear D a (g (g b)) = bilinear D (g a) b := by
  simpa only [h3 b] using (hg a (g (g b))).symm

include hg h3 in
private theorem B_swap_div (a b : Charge D) :
    B D g b a / B D g a b = (minusOne * zeta⁻¹) ^
      (bilinear D (g a) b - bilinear D (g (g a)) b) := by
  let common := three ^ (-bilinear D a b) * firstFactor ^ bilinear D (g a) b *
    firstFactor ^ bilinear D (g (g a)) b
  calc
    _ = (common * (minusOne * zeta⁻¹) ^ bilinear D (g a) b) /
        (common * (minusOne * zeta⁻¹) ^ bilinear D (g (g a)) b) := by
      simp only [B, common, bilinear_symmetric D b a, bilinear_symmetric D (g b) a,
        bilinear_symmetric D (g (g b)) a, pairing_shift_one D g hg h3 a b,
        pairing_shift_two D g hg h3 a b, secondFactor_eq,
        mul_zpow firstFactor (minusOne * zeta⁻¹)]
      simp only [← mul_assoc]
      rw [mul_right_comm (three ^ (-bilinear D a b))
        (firstFactor ^ bilinear D (g (g a)) b) (firstFactor ^ bilinear D (g a) b)]
    _ = _ := by
      rw [mul_div_mul_comm, zpow_sub]
      simp [div_eq_mul_inv]

private theorem epsilonUnit_swap_div (a b : Charge D) :
    epsilonUnit D a b / epsilonUnit D b a = minusOne ^ bilinear D a b := by
  have h : epsilonUnit D a b = minusOne ^ bilinear D a b * epsilonUnit D b a := by
    apply Units.ext
    simpa only [Units.val_mul, coe_epsilonUnit, Units.val_zpow_eq_zpow_val, coe_minusOne,
      neg_one_zpow_eq_ite, paritySign] using epsilon_skew D a b
  rw [h, mul_div_cancel_right]

include hg h3 in
private theorem c_swap_div (a b : Charge D) :
    c D g a b / c D g b a =
      minusOne ^ (bilinear D a b + (bilinear D (g a) b - bilinear D (g (g a)) b)) *
        zeta ^ (-(bilinear D (g a) b - bilinear D (g (g a)) b)) := by
  simp only [c]
  rw [mul_div_mul_comm, inv_div_inv, epsilonUnit_swap_div, B_swap_div D g hg h3,
    mul_zpow, inv_zpow', ← mul_assoc, ← zpow_add]

theorem orbitNorm_three (a : Charge D) :
    orbitNorm D g 3 a = a + g a + g (g a) := by
  simp [orbitNorm, Finset.sum_range_succ, Function.iterate_succ_apply']

include hg h3 in
/-- The commutator of a difference charge with an arbitrary lattice charge. -/
theorem commutator_difference (a b : Charge D) :
    c D g (a - g a) b / c D g b (a - g a) =
      zeta ^ (-bilinear D (orbitNorm D g 3 a) b) := by
  rw [c_swap_div D g hg h3, orbitNorm_three]
  simp only [map_sub, h3, bilinear_sub_left, bilinear_add_left]
  let x := bilinear D a b
  let y := bilinear D (g a) b
  let z := bilinear D (g (g a)) b
  change minusOne ^ ((x - y) + ((y - z) - (z - x))) *
    zeta ^ (-((y - z) - (z - x))) = zeta ^ (-(x + y + z))
  have hsign : minusOne ^ (2 : ℤ) = 1 := by
    apply Units.ext
    change ((minusOne ^ (2 : ℤ) : ℂˣ) : ℂ) = 1
    rw [Units.val_zpow_eq_zpow_val, coe_minusOne]
    norm_num
  have hcube : zeta ^ (3 : ℤ) = 1 := zeta_primitive.zpow_eq_one
  have hparity : (x - y) + ((y - z) - (z - x)) = 2 * (x - z) := by ring
  have hphase : -((y - z) - (z - x)) = 3 * z + (-(x + y + z)) := by ring
  simp only [hparity, hphase, zpow_add, zpow_mul, hsign, hcube, one_zpow, one_mul]

include hg h3 in
theorem commutator_difference_eq_one_iff (a b : Charge D) :
    c D g (a - g a) b / c D g b (a - g a) = 1 ↔
      (3 : ℤ) ∣ bilinear D (orbitNorm D g 3 a) b := by
  simp only [commutator_difference D g hg h3, zeta_primitive.zpow_eq_one_iff_dvd,
    Nat.cast_ofNat, dvd_neg]

include hg h3 in
theorem orbitNorm_pairing (a b : Charge D) :
    bilinear D (orbitNorm D g 3 a) b = bilinear D a (orbitNorm D g 3 b) := by
  simp only [orbitNorm_three, bilinear_add_left, bilinear_add_right,
    pairing_shift_one D g hg h3 a b, pairing_shift_two D g hg h3 a b]
  abel

include hg h3 in
/-- The phase descends modulo the fixed lattice in `a` and through the fixed projection
`N b / 3` in `b`, expressed integrally by equality of orbit norms. -/
theorem commutator_difference_congr {a a' b b' : Charge D}
    (ha : g (a - a') = a - a') (hb : orbitNorm D g 3 b = orbitNorm D g 3 b') :
    c D g (a - g a) b / c D g b (a - g a) =
      c D g (a' - g a') b' / c D g b' (a' - g a') := by
  have hd : a - g a = a' - g a' := by
    apply sub_eq_zero.mp
    calc
      (a - g a) - (a' - g a') = (a - a') - (g a - g a') := by abel
      _ = 0 := by rw [← map_sub g a a', ha, sub_self]
  rw [hd, commutator_difference D g hg h3 a' b, commutator_difference D g hg h3 a' b',
    orbitNorm_pairing D g hg h3 a' b, orbitNorm_pairing D g hg h3 a' b', hb]

end Isometry

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedChargeCocycle
