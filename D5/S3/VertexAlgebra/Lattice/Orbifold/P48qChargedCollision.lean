/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedCollision
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Regularized charged-field collision and orbit factors in the diagonal coordinate. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedLocality
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qTwistedCurrentDiagonal
import Batteries.Tactic.OpenPrivate

/-!
The charged collision in the coordinate `t = (x/y)^3 - 1`. The variable of
the power and Laurent series in the scalar calculation is `t`. The orbit
factors are the factors of the contraction in Bakalov–Kac, Lemmas 4.2–4.3
(arXiv:math/0402315v3), with the root convention of `orderedContraction`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear epsilon)
open P48qTwistedChargeAction (lattice g Momentum)
open PowerSeries (C X constantCoeff)
open scoped BigOperators LaurentSeries

open private formalExp formalExp_add from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedExponentialReordering

open private homogeneousContraction_clear from
  D5.S3.VertexAlgebra.Lattice.Orbifold.ThirdTwistedScalarLocality

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "q" => P48qTwistedHeisenberg.diagonalCoverRatio
local notation "ι" => (HahnSeries.ofPowerSeries ℤ ℂ)
local notation "e" => ThirdTwistedContraction.contractionOrbitExponent lattice g
local notation "shift" => ThirdTwistedChargeAction.shift lattice g

/-- The branch of `x/y` with constant term one. The current calculation uses
its reciprocal `q = y/x`. -/
def diagonalXOverY : PowerSeries ℂ :=
  PowerSeries.binomialSeries (R := ℂ) ℂ (1 / 3)

@[simp] theorem constantCoeff_diagonalXOverY : constantCoeff diagonalXOverY = 1 := by
  simp [diagonalXOverY]

private theorem q_const : constantCoeff q = 1 :=
  P48qTwistedHeisenberg.diagonalCoverRatio_branch.1

theorem diagonalXOverY_mul_q : diagonalXOverY * q = 1 := by
  rw [diagonalXOverY, P48qTwistedHeisenberg.diagonalCoverRatio,
    ← PowerSeries.binomialSeries_add, add_neg_cancel, PowerSeries.binomialSeries_zero]

theorem diagonalXOverY_cube : diagonalXOverY ^ 3 = 1 + X := by
  calc
    diagonalXOverY ^ 3 = diagonalXOverY ^ 3 * (q ^ 3 * (1 + X)) := by
      rw [P48qTwistedHeisenberg.diagonalCoverRatio_branch.2, mul_one]
    _ = (diagonalXOverY * q) ^ 3 * (1 + X) := by rw [mul_pow, mul_assoc]
    _ = _ := by rw [diagonalXOverY_mul_q, one_pow, one_mul]

private theorem X_dvd_one_sub_q : (X : PowerSeries ℂ) ∣ 1 - q := by
  apply PowerSeries.X_dvd_iff.mpr
  simp only [map_sub, map_one, q_const, sub_self]

private def diagonalLinearFactor : PowerSeries ℂ := X_dvd_one_sub_q.choose

private theorem one_sub_q : 1 - q = X * diagonalLinearFactor :=
  X_dvd_one_sub_q.choose_spec

private theorem constantCoeff_diagonalLinearFactor :
    constantCoeff diagonalLinearFactor = (3 : ℂ)⁻¹ := by
  have hc : (1 - q) * (1 + q + q ^ 2) = X * q ^ 3 := by
    calc
      _ = 1 - q ^ 3 := by ring
      _ = q ^ 3 * (1 + X) - q ^ 3 := by
        rw [P48qTwistedHeisenberg.diagonalCoverRatio_branch.2]
      _ = _ := by ring
  rw [one_sub_q, mul_assoc] at hc
  have h := congrArg (constantCoeff (R := ℂ))
    (mul_left_cancel₀ PowerSeries.X_ne_zero hc)
  have h' : constantCoeff diagonalLinearFactor * 3 = 1 := by
    simpa only [map_mul, map_add, map_one, map_pow, q_const, one_pow,
      show (1 : ℂ) + 1 + 1 = 3 by norm_num] using h
  rw [← one_div]
  exact (eq_div_iff (by norm_num : (3 : ℂ) ≠ 0)).mpr h'

private theorem zeta_primitive_complex : IsPrimitiveRoot ζ 3 :=
  IsPrimitiveRoot.coe_units_iff.mpr ThirdTwistedChargeCocycle.zeta_primitive

private def diagonalLinearUnit : (PowerSeries ℂ)ˣ :=
  ((PowerSeries.isUnit_iff_constantCoeff (φ := diagonalLinearFactor)).mpr (by
    rw [constantCoeff_diagonalLinearFactor]
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (by norm_num)))).unit

private theorem coe_diagonalLinearUnit :
    (diagonalLinearUnit : PowerSeries ℂ) = diagonalLinearFactor :=
  IsUnit.unit_spec _

private def diagonalMovingUnit (j : ℕ) (hj : j ≠ 0) (hj' : j < 3) : (PowerSeries ℂ)ˣ :=
  ((PowerSeries.isUnit_iff_constantCoeff (φ := 1 - C (ζ ^ j) * q)).mpr (by
    have h : ζ ^ j ≠ 1 := zeta_primitive_complex.pow_ne_one_of_pos_of_lt hj hj'
    simpa only [map_sub, map_mul, map_one, PowerSeries.constantCoeff_C, q_const, mul_one,
      isUnit_iff_ne_zero] using (sub_ne_zero.mpr h.symm : 1 - ζ ^ j ≠ 0))).unit

private theorem coe_diagonalMovingUnit (j : ℕ) (hj : j ≠ 0) (hj' : j < 3) :
    (diagonalMovingUnit j hj hj' : PowerSeries ℂ) = 1 - C (ζ ^ j) * q :=
  IsUnit.unit_spec _

private theorem embed_unit_zpow (u : (PowerSeries ℂ)ˣ) (n : ℤ) :
    ι (↑(u ^ n) : PowerSeries ℂ) = (ι (u : PowerSeries ℂ)) ^ n := by
  change (↑(Units.map (HahnSeries.ofPowerSeries ℤ ℂ).toMonoidHom (u ^ n)) :
    LaurentSeries ℂ) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

private theorem embed_X_ne_zero : (ι X : LaurentSeries ℂ) ≠ 0 := by
  rw [← map_zero ι]
  exact fun h => PowerSeries.X_ne_zero (HahnSeries.ofPowerSeries_injective h)

private theorem constantCoeff_unit_zpow (u : (PowerSeries ℂ)ˣ) (n : ℤ) :
    constantCoeff (↑(u ^ n) : PowerSeries ℂ) = (constantCoeff (u : PowerSeries ℂ)) ^ n := by
  change (↑(Units.map (constantCoeff (R := ℂ)).toMonoidHom (u ^ n)) : ℂ) = _
  rw [map_zpow, Units.val_zpow_eq_zpow_val]
  rfl

/-- Evaluate the native rational orbit factors in a Laurent field. At the
radial variable they recover the factors in `orderedContraction`. -/
def contractionAtCoverRatio (a b : Charge lattice) (s : LaurentSeries ℂ) : LaurentSeries ℂ :=
  ∏ j ∈ Finset.range 3, (1 - ι (C (ζ ^ j)) * s) ^ e a b j

theorem contractionAtCoverRatio_radial (a b : Charge lattice) :
    contractionAtCoverRatio a b (ι X) = ι
      (↑(∏ j ∈ Finset.range 3, ThirdTwistedContraction.binomialUnit (ζ ^ j) ^ e a b j) :
        PowerSeries ℂ) := by
  rw [contractionAtCoverRatio, Units.coe_prod, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [embed_unit_zpow, ThirdTwistedContraction.coe_binomialUnit, map_sub, map_one, map_mul]

/-- The product re-expanded under the diagonal branch `y/x = (1+t)^(-1/3)`. -/
def diagonalChargedContraction (a b : Charge lattice) : LaurentSeries ℂ :=
  contractionAtCoverRatio a b (ι q)

/-- The three regular units, with `t` extracted from orbit factor zero. -/
def regularChargedContraction (a b : Charge lattice) : (PowerSeries ℂ)ˣ :=
  diagonalLinearUnit ^ e a b 0 * diagonalMovingUnit 1 (by decide) (by decide) ^ e a b 1 *
    diagonalMovingUnit 2 (by decide) (by decide) ^ e a b 2

theorem diagonalChargedContraction_factor (a b : Charge lattice) :
    diagonalChargedContraction a b = (ι X) ^ bilinear lattice a b *
      ι (regularChargedContraction a b : PowerSeries ℂ) := by
  have hzero : 1 - ι q = ι X * ι (diagonalLinearUnit : PowerSeries ℂ) := by
    rw [coe_diagonalLinearUnit, ← map_mul, ← one_sub_q, map_sub, map_one]
  simp only [diagonalChargedContraction, contractionAtCoverRatio, regularChargedContraction,
    ThirdTwistedContraction.contractionOrbitExponent, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul, pow_zero, map_one, pow_one,
    Units.val_mul, map_mul, embed_unit_zpow, coe_diagonalMovingUnit, map_sub, hzero,
    mul_zpow, Function.iterate_zero_apply]
  ac_rfl

/-- The regular factor has precisely the original BK normalization. -/
theorem constantCoeff_regularChargedContraction (a b : Charge lattice) :
    constantCoeff (regularChargedContraction a b : PowerSeries ℂ) =
      (ThirdTwistedChargeCocycle.B lattice g a b : ℂ) := by
  simp only [regularChargedContraction, Units.val_mul, map_mul, constantCoeff_unit_zpow,
    coe_diagonalLinearUnit, constantCoeff_diagonalLinearFactor, coe_diagonalMovingUnit,
    map_sub, map_one, PowerSeries.constantCoeff_C, q_const, mul_one, pow_one,
    ThirdTwistedContraction.contractionOrbitExponent, ThirdTwistedChargeCocycle.B,
    Units.val_zpow_eq_zpow_val, Function.iterate_succ_apply',
    Function.iterate_zero_apply]
  change ((3 : ℂ)⁻¹) ^ bilinear lattice a b * _ * _ =
    (3 : ℂ) ^ (-bilinear lattice a b) * (1 - ζ) ^ bilinear lattice (g a) b *
      (1 - ζ ^ 2) ^ bilinear lattice (g (g a)) b
  rw [inv_zpow']

theorem diagonalChargedContraction_regularize (a b : Charge lattice) :
    (ι X) ^ (-bilinear lattice a b) * diagonalChargedContraction a b =
      ι (regularChargedContraction a b : PowerSeries ℂ) := by
  rw [diagonalChargedContraction_factor, ← mul_assoc, ← zpow_add₀ embed_X_ne_zero,
    neg_add_cancel, zpow_zero, one_mul]

/-- Removing the complete integral power of `t` gives a power series with
constant coefficient `B a b`. In particular this coefficient is nonzero. -/
theorem diagonalChargedContraction_regularization (a b : Charge lattice) :
    ∃ R : PowerSeries ℂ,
      (ι X) ^ (-bilinear lattice a b) * diagonalChargedContraction a b = ι R ∧
      constantCoeff R = (ThirdTwistedChargeCocycle.B lattice g a b : ℂ) :=
  ⟨regularChargedContraction a b, diagonalChargedContraction_regularize a b,
    constantCoeff_regularChargedContraction a b⟩

theorem diagonalChargedContraction_regularized_coeff_zero (a b : Charge lattice) :
    ((ι X) ^ (-bilinear lattice a b) * diagonalChargedContraction a b).coeff 0 =
      (ThirdTwistedChargeCocycle.B lattice g a b : ℂ) := by
  obtain ⟨R, hR, hR₀⟩ := diagonalChargedContraction_regularization a b
  rw [hR]
  have h := HahnSeries.ofPowerSeries_apply_coeff (Γ := ℤ) R 0
  simpa only [Nat.cast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, hR₀] using h

/-- After clearing, the diagonal product uses the same finite scalar numerator
as charged locality, evaluated at the ratio `x/y` and at `1`. -/
theorem diagonalChargedContraction_clear (a b : Charge lattice) (N : ℕ)
    (hN : ∀ j ∈ Finset.range 3, 0 ≤ (N : ℤ) + e a b j) :
    (ι X) ^ N * ((ι diagonalXOverY) ^ (∑ j ∈ Finset.range 3, e a b j) *
        diagonalChargedContraction a b) =
      MvPolynomial.eval₂Hom ((HahnSeries.ofPowerSeries ℤ ℂ).comp C) ![ι diagonalXOverY, 1]
        (ThirdTwistedContraction.clearedContractionNumerator lattice g
          ThirdTwistedChargeCocycle.zeta a b N) := by
  let r : LaurentSeries ℂ := ι diagonalXOverY
  let scalar : ℂ →+* LaurentSeries ℂ := (HahnSeries.ofPowerSeries ℤ ℂ).comp C
  have hrq : r * ι q = 1 := by
    change ι diagonalXOverY * ι q = 1
    rw [← map_mul, diagonalXOverY_mul_q, map_one]
  have hr : r ≠ 0 := by
    intro he
    rw [he, zero_mul] at hrq
    exact zero_ne_one hrq
  have hc : r ^ 3 - 1 = ι X := by
    change (ι diagonalXOverY) ^ 3 - 1 = ι X
    rw [← map_pow, diagonalXOverY_cube, map_add, map_one, add_sub_cancel_left]
  have hs (j : ℕ) : r - scalar (↑(ThirdTwistedChargeCocycle.zeta ^ j) : ℂ) * 1 =
      r * (1 - ι (C (ζ ^ j)) * ι q) := by
    simp only [scalar, RingHom.comp_apply, Units.val_pow_eq_pow_val, mul_one, mul_sub]
    rw [mul_left_comm r, hrq, mul_one]
  have hp : (∏ j ∈ Finset.range 3, r ^ e a b j) = r ^ (∑ j ∈ Finset.range 3, e a b j) := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, Finset.sum_range_succ,
      Finset.sum_range_zero, one_mul, zero_add, zpow_add₀ hr]
  have h := homogeneousContraction_clear lattice g scalar
    ThirdTwistedChargeCocycle.zeta ThirdTwistedChargeCocycle.zeta_primitive a b N hN r 1
    (by rw [one_pow, hc]; exact embed_X_ne_zero)
  simpa only [one_pow, hc, hs, mul_zpow, Finset.prod_mul_distrib, hp,
    diagonalChargedContraction, contractionAtCoverRatio] using h

private theorem creationSeries_add_charge (bases : FixedDualBases) (a b : Charge lattice) :
    creationSeries bases (a + b) = creationSeries bases a + creationSeries bases b := by
  have hv : chargeVector (a + b) = chargeVector a + chargeVector b := by
    funext i
    exact Int.cast_add (a i) (b i)
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp only [map_add, creationSeries, PowerSeries.coeff_mk, add_zero]
  | succ n =>
    simp only [map_add, coeff_creationSeries_succ, creationCoordinate, hv, LinearMap.add_apply,
      add_smul, Finset.sum_add_distrib, smul_add]

private theorem creationExponential_mul_charge (bases : FixedDualBases) (a b : Charge lattice) :
    creationExponential bases a * creationExponential bases b =
      creationExponential bases (a + b) := by
  have h (d : Charge lattice) : constantCoeff (creationSeries bases d) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, creationSeries, PowerSeries.coeff_mk]
  simpa only [creationExponential, creationSeries_add_charge, formalExp] using
    (formalExp_add (h a) (h b)).symm

/-- On the unit Fock vector the finite annihilation substitution fixes `1`.
This displays the actual radial expansion in the factors used below. -/
theorem orderedChargedProduct_ground_factors
    (bases : FixedDualBases) (a b : Charge lattice) (p : Momentum) :
    orderedChargedProduct bases a b (Finsupp.single p 1) =
      Finsupp.single (shift (a + b) p)
        (coverMonomial
            (momentumExponent (a + b) p + 3 * bilinear lattice a b - momentumExponent b p)
            (momentumExponent b p)
            (algebraMap ℂ Fock ((ThirdTwistedChargeCocycle.c lattice g a b : ℂ) *
              chargePhase (a + b) p)) *
          orderedContraction a b * creationProduct bases a b) := by
  have h := orderedChargedProduct_single bases a b p (1 : Fock)
  simpa only [map_one, mul_one, coverMonomial, creationProduct, mul_assoc] using h

private def diagonalXOverYUnit : (PowerSeries ℂ)ˣ :=
  ((PowerSeries.isUnit_iff_constantCoeff (φ := diagonalXOverY)).mpr (by
    rw [constantCoeff_diagonalXOverY]
    exact isUnit_one)).unit

private theorem coe_diagonalXOverYUnit :
    (diagonalXOverYUnit : PowerSeries ℂ) = diagonalXOverY :=
  IsUnit.unit_spec _

/-- The scalar on a ground momentum line after the change of cover ratio and
removal of the collision power and the total momentum monomial. -/
def groundDiagonalScalar (a b : Charge lattice) (p : Momentum) : PowerSeries ℂ :=
  C (chargePhase a (shift b p) * chargePhase b p) *
    (↑(diagonalXOverYUnit ^ momentumExponent a (shift b p)) : PowerSeries ℂ) *
    (regularChargedContraction a b : PowerSeries ℂ)

theorem groundDiagonalScalar_eq (a b : Charge lattice) (p : Momentum) :
    ι (groundDiagonalScalar a b p) =
      ι (C ((ThirdTwistedChargeCocycle.c lattice g a b : ℂ) * chargePhase (a + b) p)) *
        (ι diagonalXOverY) ^ momentumExponent a (shift b p) *
        ((ι X) ^ (-bilinear lattice a b) * diagonalChargedContraction a b) := by
  rw [groundDiagonalScalar, chargePhase_ordered, map_mul, map_mul, embed_unit_zpow,
    coe_diagonalXOverYUnit, diagonalChargedContraction_regularize]

private theorem groundDiagonalScalar_const (a b : Charge lattice) (p : Momentum) :
    constantCoeff (groundDiagonalScalar a b p) = epsilon lattice a b * chargePhase (a + b) p := by
  let B₀ := ThirdTwistedChargeCocycle.B lattice g a b
  have hc : (ThirdTwistedChargeCocycle.c lattice g a b : ℂ) * (B₀ : ℂ) = epsilon lattice a b := by
    change (↑((ThirdTwistedChargeCocycle.epsilonUnit lattice a b * B₀⁻¹) * B₀) : ℂ) = _
    rw [mul_assoc, inv_mul_cancel, mul_one, ThirdTwistedChargeCocycle.coe_epsilonUnit]
  simp only [groundDiagonalScalar, map_mul, PowerSeries.constantCoeff_C, constantCoeff_unit_zpow,
    coe_diagonalXOverYUnit, constantCoeff_diagonalXOverY, one_zpow, mul_one,
    constantCoeff_regularChargedContraction, chargePhase_ordered]
  change (_ * chargePhase (a + b) p) * (B₀ : ℂ) = _
  rw [mul_right_comm, hc]

private def mapScalarToFock : PowerSeries ℂ →+* PowerSeries Fock :=
  PowerSeries.map (algebraMap ℂ Fock)

/-- The regular expansion on the ground line after removing `(x³-y³)^⟨a,b⟩`
and the remaining momentum monomial `y ^ momentumExponent (a+b) p`.
The outer variable is `y` and the inner one is `t`. The rescale substitutes
`x = y (1+t)^(1/3)` in the first creation exponential. The factor of
`y ^ (3 * ⟨a,b⟩)` used in the regularization is accounted for by
`momentumExponent_ordered`. -/
def groundDiagonalRegular (bases : FixedDualBases) (a b : Charge lattice) (p : Momentum) :
    PowerSeries (PowerSeries Fock) :=
  C (mapScalarToFock (groundDiagonalScalar a b p)) *
    PowerSeries.rescale (mapScalarToFock diagonalXOverY)
      ((creationExponential bases a).map C) *
    (creationExponential bases b).map C

private theorem groundDiagonalRegular_eval (bases : FixedDualBases) (a b : Charge lattice)
    (p : Momentum) :
    (groundDiagonalRegular bases a b p).map (constantCoeff (R := Fock)) =
      C (algebraMap ℂ Fock (epsilon lattice a b * chargePhase (a + b) p)) *
        creationExponential bases (a + b) := by
  have h (S : PowerSeries ℂ) : constantCoeff (mapScalarToFock S) =
      algebraMap ℂ Fock (constantCoeff S) := by
    simp only [mapScalarToFock, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      PowerSeries.coeff_map]
  have hm (S : PowerSeries Fock) :
      (S.map (C (R := Fock))).map (constantCoeff (R := Fock)) = S := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, PowerSeries.constantCoeff_C]
  have hr (S : PowerSeries Fock) :
      (PowerSeries.rescale (mapScalarToFock diagonalXOverY) (S.map (C (R := Fock)))).map
        (constantCoeff (R := Fock)) = S := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_rescale, map_mul, map_pow, h,
      constantCoeff_diagonalXOverY, map_one, one_pow, PowerSeries.constantCoeff_C, one_mul]
  rw [groundDiagonalRegular, map_mul, map_mul, PowerSeries.map_C, h,
    groundDiagonalScalar_const, hr, hm, mul_assoc, creationExponential_mul_charge]

/-- On each ground momentum vector, the leading coefficient of the physical
collision is the actual charged field of `a+b`, multiplied by `ε(a,b)`.
The coefficient index restores the remaining cover monomial in `y`. -/
theorem groundDiagonalRegular_coeff (bases : FixedDualBases) (a b : Charge lattice)
    (p : Momentum) (k : ℤ) :
    Finsupp.single (shift (a + b) p)
      ((HahnSeries.ofPowerSeries ℤ Fock
        ((groundDiagonalRegular bases a b p).map (constantCoeff (R := Fock)))).coeff
        (k - momentumExponent (a + b) p)) =
      epsilon lattice a b • fieldCoeff bases (a + b) k (Finsupp.single p 1) := by
  have h (d : ℤ) : (HahnSeries.ofPowerSeries ℤ Fock (creationExponential bases (a + b))).coeff d =
      creationCoeff bases (a + b) d := by
    rw [PowerSeries.coeff_coe, creationCoeff]
    cases d with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, ite_eq_right (Int.natCast_nonneg n).not_gt,
        Int.natAbs_natCast, Int.toNat_natCast]
    | negSucc n => simp only [Int.negSucc_lt_zero, ite_true]
  rw [groundDiagonalRegular_eval, fieldCoeff_single, oscillatorCoeff_one, Finsupp.smul_single,
    smul_smul, Algebra.smul_def, map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.C_apply,
    HahnSeries.coeff_single_zero_mul, h]

/-- The same identity on every finite linear combination of ground momentum
vectors, with the cover monomial shift on each input momentum summand. -/
theorem groundDiagonalRegular_coeff_sum (bases : FixedDualBases) (a b : Charge lattice)
    (k : ℤ) (s : Finset Momentum) (z : Momentum → ℂ) :
    (∑ p ∈ s, z p • Finsupp.single (shift (a + b) p)
      ((HahnSeries.ofPowerSeries ℤ Fock
        ((groundDiagonalRegular bases a b p).map (constantCoeff (R := Fock)))).coeff
        (k - (momentumExponent a (shift b p) + momentumExponent b p - 3 * bilinear lattice a b)))) =
    epsilon lattice a b • ((HahnModule.of ℂ).symm
      (chargedField bases (a + b) (∑ p ∈ s, z p • Finsupp.single p 1))).coeff k := by
  rw [chargedField_coeff]
  simp only [momentumExponent_ordered, add_sub_cancel_right, groundDiagonalRegular_coeff,
    map_sum, map_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p _
  exact smul_comm (z p) (epsilon lattice a b) _

#print axioms contractionAtCoverRatio_radial
#print axioms diagonalChargedContraction_factor
#print axioms constantCoeff_regularChargedContraction
#print axioms diagonalChargedContraction_regularization
#print axioms diagonalChargedContraction_regularized_coeff_zero
#print axioms diagonalChargedContraction_clear
#print axioms orderedChargedProduct_ground_factors
#print axioms groundDiagonalScalar_eq
#print axioms groundDiagonalRegular_coeff
#print axioms groundDiagonalRegular_coeff_sum

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
