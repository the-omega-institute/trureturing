import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision

/-!
The coefficient of `t` in the concrete charged ground scalar in the coordinate
`t = (x/y)^3 - 1`. The orbit-zero factor here is the unit left after extracting
the full collision power. The root convention is that of `orderedContraction`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge epsilon)
open P48qTwistedChargeAction (lattice g Momentum)
open PowerSeries (C X coeff constantCoeff)

open private diagonalLinearFactor one_sub_q constantCoeff_diagonalLinearFactor
  diagonalLinearUnit coe_diagonalLinearUnit diagonalMovingUnit coe_diagonalMovingUnit
  diagonalXOverYUnit coe_diagonalXOverYUnit groundDiagonalScalar_const from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "q" => P48qTwistedHeisenberg.diagonalCoverRatio
local notation "e" => ThirdTwistedContraction.contractionOrbitExponent lattice g
local notation "shift" => ThirdTwistedChargeAction.shift lattice g

private def linearRatio (f : PowerSeries ℂ) : ℂ := coeff 1 f / constantCoeff f

private theorem linearRatio_mul (f h : PowerSeries ℂ)
    (hf : constantCoeff f ≠ 0) (hh : constantCoeff h ≠ 0) :
    linearRatio (f * h) = linearRatio f + linearRatio h := by
  simp only [linearRatio, PowerSeries.coeff_one_mul, map_mul,
    div_add_div (coeff 1 f) (coeff 1 h) hf hh,
    mul_comm (coeff 1 h) (constantCoeff f)]

private theorem linearRatio_one : linearRatio (1 : PowerSeries ℂ) = 0 := by
  simp [linearRatio]

private theorem linearRatio_C (c : ℂ) : linearRatio (C c) = 0 := by
  simp [linearRatio, PowerSeries.coeff_C]

private theorem constantCoeff_coe_unit_ne_zero (u : (PowerSeries ℂ)ˣ) :
    constantCoeff (u : PowerSeries ℂ) ≠ 0 :=
  (Units.map (constantCoeff (R := ℂ)).toMonoidHom u).ne_zero

private theorem linearRatio_unit_mul (u v : (PowerSeries ℂ)ˣ) :
    linearRatio (↑(u * v) : PowerSeries ℂ) =
      linearRatio (u : PowerSeries ℂ) + linearRatio (v : PowerSeries ℂ) :=
  linearRatio_mul _ _ (constantCoeff_coe_unit_ne_zero u) (constantCoeff_coe_unit_ne_zero v)

private theorem linearRatio_unit_pow (u : (PowerSeries ℂ)ˣ) (n : ℕ) :
    linearRatio (↑(u ^ n) : PowerSeries ℂ) = (n : ℂ) * linearRatio (u : PowerSeries ℂ) := by
  induction n with
  | zero => simp only [pow_zero, Units.val_one, linearRatio_one, Nat.cast_zero, zero_mul]
  | succ n ih => rw [pow_succ, linearRatio_unit_mul, ih, Nat.cast_succ, add_mul, one_mul]

private theorem linearRatio_unit_inv (u : (PowerSeries ℂ)ˣ) :
    linearRatio (↑(u⁻¹) : PowerSeries ℂ) = -linearRatio (u : PowerSeries ℂ) := by
  have h := linearRatio_unit_mul u⁻¹ u
  rw [inv_mul_cancel, Units.val_one, linearRatio_one] at h
  simpa only [add_sub_cancel_right, zero_sub] using
    congrArg (fun z : ℂ => z - linearRatio (u : PowerSeries ℂ)) h.symm

private theorem linearRatio_unit_zpow (u : (PowerSeries ℂ)ˣ) (n : ℤ) :
    linearRatio (↑(u ^ n) : PowerSeries ℂ) = (n : ℂ) * linearRatio (u : PowerSeries ℂ) := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, Int.cast_natCast]
      exact linearRatio_unit_pow u n
  | negSucc n =>
      rw [zpow_negSucc, linearRatio_unit_inv, linearRatio_unit_pow, Int.cast_negSucc, neg_mul]

private theorem coeff_one_diagonalCoverRatio : coeff 1 q = -(1 / 3 : ℂ) := by
  simp only [P48qTwistedHeisenberg.diagonalCoverRatio, PowerSeries.binomialSeries_coeff,
    Ring.choose_one_right, smul_eq_mul, mul_one]

private theorem coeff_two_diagonalCoverRatio : coeff 2 q = (2 / 9 : ℂ) := by
  have hchoose : Ring.choose (-(1 / 3 : ℂ)) 2 =
      (-(1 / 3 : ℂ)) * (-(1 / 3 : ℂ) - 1) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    rw [mul_comm (Ring.choose (-(1 / 3 : ℂ)) 2) 2]
    simpa only [Nat.choose_one_right, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_one,
      show (2 : ℕ) - 1 = 1 by decide, Ring.choose_one_right] using
      (Ring.choose_smul_choose (-(1 / 3 : ℂ)) (n := 2) (k := 1) (by decide))
  rw [P48qTwistedHeisenberg.diagonalCoverRatio, PowerSeries.binomialSeries_coeff,
    smul_eq_mul, mul_one, hchoose] <;> norm_num

private theorem coeff_one_diagonalLinearFactor :
    coeff 1 diagonalLinearFactor = -(2 / 9 : ℂ) := by
  have h := congrArg (coeff (R := ℂ) 2) one_sub_q
  change coeff 2 (1 - q) = coeff (1 + 1) (X * diagonalLinearFactor) at h
  simpa only [map_sub, PowerSeries.coeff_one, if_neg (by decide : (2 : ℕ) ≠ 0),
    PowerSeries.coeff_succ_X_mul, coeff_two_diagonalCoverRatio, zero_sub] using h.symm

private theorem linearRatio_diagonalLinearUnit :
    linearRatio (diagonalLinearUnit : PowerSeries ℂ) = -(2 / 3 : ℂ) := by
  rw [coe_diagonalLinearUnit, linearRatio, coeff_one_diagonalLinearFactor,
    constantCoeff_diagonalLinearFactor]
  norm_num

private theorem linearRatio_diagonalMovingUnit (j : ℕ) (hj : j ≠ 0) (hj' : j < 3) :
    linearRatio (diagonalMovingUnit j hj hj' : PowerSeries ℂ) = ζ ^ j / (3 * (1 - ζ ^ j)) := by
  simp only [coe_diagonalMovingUnit, linearRatio, map_sub, PowerSeries.coeff_one,
    if_neg (by decide : (1 : ℕ) ≠ 0), PowerSeries.coeff_C_mul, coeff_one_diagonalCoverRatio,
    map_one, map_mul, PowerSeries.constantCoeff_C,
    P48qTwistedHeisenberg.diagonalCoverRatio_branch.1, mul_one, zero_sub]
  rw [mul_neg, neg_neg, ← mul_div_assoc, mul_one, div_div]

private theorem linearRatio_diagonalXOverYUnit :
    linearRatio (diagonalXOverYUnit : PowerSeries ℂ) = (1 / 3 : ℂ) := by
  rw [coe_diagonalXOverYUnit, linearRatio, constantCoeff_diagonalXOverY, div_one]
  simp only [diagonalXOverY, PowerSeries.binomialSeries_coeff, Ring.choose_one_right,
    smul_eq_mul, mul_one]

/-- The first coefficient of the regularized native orbit product, divided by its constant. -/
theorem regularChargedContraction_coeff_one_div_constantCoeff (a b : Charge lattice) :
    coeff 1 (regularChargedContraction a b : PowerSeries ℂ) /
        constantCoeff (regularChargedContraction a b : PowerSeries ℂ) =
      -(2 / 3 : ℂ) * (e a b 0 : ℂ) +
        (e a b 1 : ℂ) * (ζ / (3 * (1 - ζ))) +
        (e a b 2 : ℂ) * (ζ ^ 2 / (3 * (1 - ζ ^ 2))) := by
  change linearRatio (regularChargedContraction a b : PowerSeries ℂ) = _
  simp only [regularChargedContraction, linearRatio_unit_mul, linearRatio_unit_zpow,
    linearRatio_diagonalLinearUnit, linearRatio_diagonalMovingUnit, pow_one,
    mul_comm (e a b 0 : ℂ) (-(2 / 3 : ℂ))]

theorem groundDiagonalScalar_constantCoeff_ne_zero (a b : Charge lattice) (p : Momentum) :
    constantCoeff (groundDiagonalScalar a b p) ≠ 0 := by
  rw [groundDiagonalScalar_const, ← ThirdTwistedChargeCocycle.coe_epsilonUnit lattice a b]
  exact mul_ne_zero (ThirdTwistedChargeCocycle.epsilonUnit lattice a b).ne_zero
    (chargePhase_ne_zero (a + b) p)

/-- The normalized coefficient of `t` on the concrete ground momentum line. -/
theorem groundDiagonalScalar_coeff_one_div_constantCoeff (a b : Charge lattice) (p : Momentum) :
    coeff 1 (groundDiagonalScalar a b p) / constantCoeff (groundDiagonalScalar a b p) =
      (momentumExponent a (shift b p) : ℂ) / 3 - (2 / 3 : ℂ) * (e a b 0 : ℂ) +
        (e a b 1 : ℂ) * (ζ / (3 * (1 - ζ))) +
        (e a b 2 : ℂ) * (ζ ^ 2 / (3 * (1 - ζ ^ 2))) := by
  let phase := chargePhase a (shift b p) * chargePhase b p
  let cover := diagonalXOverYUnit ^ momentumExponent a (shift b p)
  let orbit := regularChargedContraction a b
  have hphase : constantCoeff (C phase) ≠ 0 := by
    rw [PowerSeries.constantCoeff_C]
    exact mul_ne_zero (chargePhase_ne_zero a (shift b p)) (chargePhase_ne_zero b p)
  change linearRatio (C phase * (cover : PowerSeries ℂ) * (orbit : PowerSeries ℂ)) = _
  rw [mul_assoc, ← Units.val_mul cover orbit,
    linearRatio_mul (C phase) _ hphase (constantCoeff_coe_unit_ne_zero (cover * orbit)),
    linearRatio_C, zero_add, linearRatio_unit_mul]
  change linearRatio (cover : PowerSeries ℂ) +
    coeff 1 (regularChargedContraction a b : PowerSeries ℂ) /
      constantCoeff (regularChargedContraction a b : PowerSeries ℂ) = _
  simp only [cover, linearRatio_unit_zpow, linearRatio_diagonalXOverYUnit,
    regularChargedContraction_coeff_one_div_constantCoeff,
    ← mul_div_assoc (momentumExponent a (shift b p) : ℂ) 1 3, mul_one, sub_eq_add_neg,
    neg_mul, ← add_assoc]

/-- The first scalar coefficient with the native leading phase restored. -/
theorem coeff_one_groundDiagonalScalar (a b : Charge lattice) (p : Momentum) :
    coeff 1 (groundDiagonalScalar a b p) =
      (epsilon lattice a b * chargePhase (a + b) p) *
        ((momentumExponent a (shift b p) : ℂ) / 3 - (2 / 3 : ℂ) * (e a b 0 : ℂ) +
          (e a b 1 : ℂ) * (ζ / (3 * (1 - ζ))) +
          (e a b 2 : ℂ) * (ζ ^ 2 / (3 * (1 - ζ ^ 2)))) := by
  have h := (div_eq_iff (groundDiagonalScalar_constantCoeff_ne_zero a b p)).mp
    (groundDiagonalScalar_coeff_one_div_constantCoeff a b p)
  rw [groundDiagonalScalar_const] at h
  exact h.trans (mul_comm _ _)

#print axioms coeff_one_groundDiagonalScalar

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
