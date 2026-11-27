/- GID: D5/S3/VertexAlgebra/Lattice/Orbifold/P48qChargedDiagonalScalar
   generality: I
   mirror-B: none(waiver:internal-proof-component)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The all-degree diagonal scalar from the three regular orbit factors. -/

import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision
import D5.S3.VertexAlgebra.Lattice.Orbifold.P48qIntegratedJetKernels

/-!
The all-degree scalar in the regular diagonal expansion of two charged
P48q fields. The three regular orbit factors give the Fourier components
of the integrated current kernel in the coordinate `X = (x/y)^3 - 1`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField

open LatticeGeneratingFieldLocality (Charge bilinear epsilon)
open P48qTwistedChargeAction (lattice g Momentum)
open P48qTwistedHeisenberg (projectAt projectAt_eq_fourier)
open ThirdEigenspacePairing (p48qAction p48qForm)
open P48qIntegratedJetKernels (integratedScalarKernel derivative_integratedScalarKernel)
open P48qJetContractions (scalarKernel scalarKernel_mul_X)
open PowerSeries (C X constantCoeff derivative)
open scoped BigOperators

open private diagonalLinearFactor one_sub_q diagonalLinearUnit coe_diagonalLinearUnit
  diagonalMovingUnit coe_diagonalMovingUnit diagonalXOverYUnit coe_diagonalXOverYUnit
  zeta_primitive_complex groundDiagonalScalar_const from
  D5.S3.VertexAlgebra.Lattice.Orbifold.P48qChargedCollision

open private action_chargeVector from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
open private gram_on_charges from D5.S3.VertexAlgebra.Lattice.Orbifold.P48qMomentumEnergy

noncomputable section

local notation "ζ" => (ThirdTwistedChargeCocycle.zeta : ℂ)
local notation "t" => diagonalXOverY
local notation "q" => P48qTwistedHeisenberg.diagonalCoverRatio
local notation "U" => diagonalXOverYUnit
local notation "e" => ThirdTwistedContraction.contractionOrbitExponent lattice g
local notation "shift" => ThirdTwistedChargeAction.shift lattice g
local notation "A" => fun a b (j : ℕ) =>
  p48qForm (projectAt (j : ℤ) (chargeVector a)) (chargeVector b)

/-- The primitive of the diagonal scalar kernel, with the zero mode acting
on the input momentum. -/
def chargedIterateLog (a b : Charge lattice) (p : Momentum) : PowerSeries ℂ :=
  C ((momentumExponent a p : ℂ) / 3) * PowerSeries.log ℂ +
    ∑ j ∈ Finset.range 3,
      C (p48qForm (projectAt (j : ℤ) (chargeVector a)) (chargeVector b)) *
        integratedScalarKernel ((j : ℂ) / 3)

private def logDerivative (u : (PowerSeries ℂ)ˣ) : PowerSeries ℂ :=
  derivative (u : PowerSeries ℂ) * ↑u⁻¹

private theorem logDerivative_mul (u v : (PowerSeries ℂ)ˣ) :
    logDerivative (u * v) = logDerivative u + logDerivative v := by
  simp only [logDerivative, mul_inv_rev, Units.val_mul, Derivation.leibniz, smul_eq_mul]
  calc
    _ = ((v : PowerSeries ℂ) * ↑v⁻¹) * (derivative ↑u * ↑u⁻¹) +
        ((u : PowerSeries ℂ) * ↑u⁻¹) * (derivative ↑v * ↑v⁻¹) := by ring
    _ = _ := by rw [Units.mul_inv, Units.mul_inv, one_mul, one_mul]

private theorem logDerivative_one : logDerivative (1 : (PowerSeries ℂ)ˣ) = 0 := by
  simp [logDerivative]

private theorem logDerivative_zpow (u : (PowerSeries ℂ)ˣ) (n : ℤ) :
    logDerivative (u ^ n) = C (n : ℂ) * logDerivative u := by
  have hpow (k : ℕ) : logDerivative (u ^ k) = C (k : ℂ) * logDerivative u := by
    induction k with
    | zero => simp [logDerivative_one]
    | succ k hk =>
      rw [pow_succ, logDerivative_mul, hk, Nat.cast_succ, map_add, map_one, add_mul, one_mul]
  have hinv (v : (PowerSeries ℂ)ˣ) : logDerivative v⁻¹ = -logDerivative v := by
    simp only [logDerivative, PowerSeries.derivative_inv, inv_inv]
    calc
      _ = ((v : PowerSeries ℂ) * ↑v⁻¹) * -(derivative ↑v * ↑v⁻¹) := by ring
      _ = _ := by rw [Units.mul_inv, one_mul]
  cases n with
  | ofNat k => simpa only [Int.ofNat_eq_natCast, zpow_natCast, Int.cast_natCast] using hpow k
  | negSucc k =>
    have hk : Int.negSucc k = -((k + 1 : ℕ) : ℤ) := by omega
    rw [hk, zpow_neg, zpow_natCast, hinv, hpow,
      Int.cast_neg, Int.cast_natCast, map_neg, neg_mul]

private theorem val_mul_logDerivative (u : (PowerSeries ℂ)ˣ) :
    (u : PowerSeries ℂ) * logDerivative u = derivative (u : PowerSeries ℂ) := by
  rw [logDerivative, mul_left_comm, Units.mul_inv, mul_one]

private theorem derivative_diagonalXOverY : derivative t = C ((3 : ℂ)⁻¹) * q ^ 2 := by
  have h := congrArg (fun f : PowerSeries ℂ => derivative f) diagonalXOverY_cube
  simp only [PowerSeries.derivative_pow, Nat.reduceSub, map_add, PowerSeries.derivative_one,
    PowerSeries.derivative_X, zero_add, Nat.cast_ofNat] at h
  calc
    derivative t = (C ((3 : ℂ)⁻¹) * ((t * q) ^ 2) * 3) * derivative t := by
      rw [diagonalXOverY_mul_q, one_pow, mul_one, ← map_ofNat (C (R := ℂ)) 3,
        ← map_mul, inv_mul_cancel₀ (by norm_num : (3 : ℂ) ≠ 0), map_one, one_mul]
    _ = C ((3 : ℂ)⁻¹) * q ^ 2 * (3 * t ^ 2 * derivative t) := by ring
    _ = _ := by rw [h, mul_one]

private theorem logDerivative_cover : logDerivative U =
    C ((3 : ℂ)⁻¹) * derivative (PowerSeries.log ℂ) := by
  have hq : (↑U⁻¹ : PowerSeries ℂ) = q := by
    apply Units.inv_eq_of_mul_eq_one_right (u := U)
    rw [coe_diagonalXOverYUnit]
    exact diagonalXOverY_mul_q
  rw [logDerivative, coe_diagonalXOverYUnit, hq, derivative_diagonalXOverY, mul_assoc, ← pow_succ]
  congr 1
  apply mul_right_cancel₀ (show (1 + X : PowerSeries ℂ) ≠ 0 by
    intro h
    have := congrArg (constantCoeff (R := ℂ)) h
    simp at this)
  rw [P48qTwistedHeisenberg.diagonalCoverRatio_branch.2,
    PowerSeries.derivative_log_mul_one_add_X]

private def orbitPolynomial (z : ℂ) : PowerSeries ℂ :=
  t ^ 2 + C z * t + C z ^ 2

private theorem orbitPolynomial_factor (z : ℂ) (hz : z ^ 3 = 1) :
    (t - C z) * orbitPolynomial z = X := by
  calc
    _ = t ^ 3 - C z ^ 3 := by unfold orbitPolynomial; ring
    _ = _ := by rw [diagonalXOverY_cube, ← map_pow, hz, map_one]; ring

private theorem scaledLogDerivative_linear :
    X * logDerivative (U * diagonalLinearUnit) = derivative t * orbitPolynomial 1 - 1 := by
  let u := U * diagonalLinearUnit
  have hu : X * (u : PowerSeries ℂ) = t - 1 := by
    change X * ((U : PowerSeries ℂ) * (diagonalLinearUnit : PowerSeries ℂ)) = _
    rw [coe_diagonalXOverYUnit, coe_diagonalLinearUnit, mul_left_comm, ← one_sub_q,
      mul_sub, mul_one, diagonalXOverY_mul_q]
  have hinv : (↑u⁻¹ : PowerSeries ℂ) = orbitPolynomial 1 := by
    apply u.inv_eq_of_mul_eq_one_left
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ))
    rw [mul_comm (orbitPolynomial 1), ← mul_assoc, hu, mul_one]
    simpa only [map_one] using orbitPolynomial_factor 1 (by simp)
  have hd := congrArg (fun f : PowerSeries ℂ => derivative f) hu
  simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X, mul_one, map_sub,
    PowerSeries.derivative_one, sub_zero] at hd
  change X * (derivative (u : PowerSeries ℂ) * (↑u⁻¹ : PowerSeries ℂ)) = _
  rw [← mul_assoc, show X * derivative (u : PowerSeries ℂ) = derivative t - (u : PowerSeries ℂ) by
    rw [← hd]; ring, sub_mul, Units.mul_inv, hinv]

private theorem scaledLogDerivative_moving (k : ℕ) (hk : k ≠ 0) (hk' : k < 3) :
    X * logDerivative (U * diagonalMovingUnit k hk hk') =
      derivative t * orbitPolynomial (ζ ^ k) := by
  let u := U * diagonalMovingUnit k hk hk'
  have hu : (u : PowerSeries ℂ) = t - C (ζ ^ k) := by
    change (U : PowerSeries ℂ) * (diagonalMovingUnit k hk hk' : PowerSeries ℂ) = _
    rw [coe_diagonalXOverYUnit, coe_diagonalMovingUnit, mul_sub, mul_one, mul_left_comm,
      diagonalXOverY_mul_q, mul_one]
  have hf := orbitPolynomial_factor (ζ ^ k) (by
    rw [pow_right_comm, zeta_primitive_complex.pow_eq_one, one_pow])
  rw [← hu] at hf
  change X * (derivative (u : PowerSeries ℂ) * (↑u⁻¹ : PowerSeries ℂ)) = _
  rw [← hf, hu, map_sub, PowerSeries.derivative_C, sub_zero, ← hu]
  calc
    _ = ((u : PowerSeries ℂ) * ↑u⁻¹) * (derivative t * orbitPolynomial (ζ ^ k)) := by ring
    _ = _ := by rw [Units.mul_inv, one_mul]

private theorem orbit_pairing_sum (a b : Charge lattice) :
    bilinear lattice (ThirdTwistedChargeAction.N lattice g a) b =
      e a b 0 + e a b 1 + e a b 2 := by
  simp only [ThirdTwistedChargeAction.N_apply, ThirdTwistedContraction.contractionOrbitExponent,
    Function.iterate_succ_apply', Function.iterate_zero_apply]
  simp only [LatticeFiniteNegativeGeneration.bilinear_symmetric lattice _ b,
    LatticeActualGeneratorLocality.bilinear_add_right]

private theorem fourier_pairing (a b : Charge lattice) (j : ℕ) (hj : j < 3) :
    A a b j = (3 : ℂ)⁻¹ * ((e a b 0 : ℂ) + ζ ^ j * (e a b 1 : ℂ) +
      (ζ ^ j) ^ 2 * (e a b 2 : ℂ)) := by
  have hmod : (((j : ℤ) % 3).toNat) = j := by omega
  have hpair (a' b' : Charge lattice) :
      p48qForm (chargeVector a') (chargeVector b') = (bilinear lattice a' b' : ℂ) :=
    gram_on_charges ℂ a' b'
  change p48qForm (projectAt (j : ℤ) (chargeVector a)) (chargeVector b) = _
  rw [projectAt_eq_fourier, hmod]
  simp only [P48qTwistedHeisenberg.project, LinearMap.BilinForm.smul_left,
    LinearMap.BilinForm.add_left, action_chargeVector, hpair,
    ThirdTwistedContraction.contractionOrbitExponent, Function.iterate_succ_apply',
    Function.iterate_zero_apply]

private theorem zeta_sum : (1 : ℂ) + ζ + ζ ^ 2 = 0 := by
  simpa only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, pow_one] using
    zeta_primitive_complex.geom_sum_eq_zero (by decide : 1 < 3)

private theorem zeta_square_square : (ζ ^ 2) ^ 2 = ζ := by
  calc
    _ = ζ ^ 3 * ζ := by ring
    _ = _ := by rw [zeta_primitive_complex.pow_eq_one, one_mul]

private theorem fourier_pairing_sum (a b : Charge lattice) :
    ∑ j ∈ Finset.range 3, A a b j = (e a b 0 : ℂ) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    fourier_pairing a b 0 (by decide), fourier_pairing a b 1 (by decide),
    fourier_pairing a b 2 (by decide), pow_zero, pow_one, one_pow, zeta_square_square]
  linear_combination ((3 : ℂ)⁻¹ * ((e a b 1 : ℂ) + (e a b 2 : ℂ))) * zeta_sum

private theorem derivative_mul_orbitPolynomial (z : ℂ) :
    derivative t * orbitPolynomial z = C ((3 : ℂ)⁻¹) * (1 + C z * q + C z ^ 2 * q ^ 2) := by
  have h₂ : t ^ 2 * q ^ 2 = 1 := by rw [← mul_pow, diagonalXOverY_mul_q, one_pow]
  have h₁ : t * q ^ 2 = q := by rw [pow_two, ← mul_assoc, diagonalXOverY_mul_q, one_mul]
  rw [derivative_diagonalXOverY, orbitPolynomial]
  linear_combination C ((3 : ℂ)⁻¹) * h₂ + C ((3 : ℂ)⁻¹) * C z * h₁

private theorem orbit_fourier (a b : Charge lattice) :
    C (e a b 0 : ℂ) * (derivative t * orbitPolynomial 1) +
    C (e a b 1 : ℂ) * (derivative t * orbitPolynomial ζ) +
    C (e a b 2 : ℂ) * (derivative t * orbitPolynomial (ζ ^ 2)) =
      ∑ j ∈ Finset.range 3, C (A a b j) * q ^ j := by
  simp only [derivative_mul_orbitPolynomial, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    fourier_pairing a b 0 (by decide), fourier_pairing a b 1 (by decide),
    fourier_pairing a b 2 (by decide), pow_zero, pow_one, one_pow, zeta_square_square,
    map_add, map_mul, map_one]
  simp only [← map_pow, zeta_square_square]
  ring

private theorem coverRatio_pow (j : ℕ) :
    q ^ j = PowerSeries.binomialSeries ℂ (-((j : ℂ) / 3)) := by
  induction j with
  | zero => simp
  | succ j hj =>
    rw [pow_succ, hj, P48qTwistedHeisenberg.diagonalCoverRatio,
      ← PowerSeries.binomialSeries_add, Nat.cast_succ]
    congr 1
    ring

private theorem logDerivative_orbit (a b : Charge lattice) :
    logDerivative ((U * diagonalLinearUnit) ^ e a b 0 *
      (U * diagonalMovingUnit 1 (by decide) (by decide)) ^ e a b 1 *
      (U * diagonalMovingUnit 2 (by decide) (by decide)) ^ e a b 2) =
      ∑ j ∈ Finset.range 3, C (A a b j) * scalarKernel ((j : ℂ) / 3) := by
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ))
  rw [logDerivative_mul, logDerivative_mul, logDerivative_zpow, logDerivative_zpow,
    logDerivative_zpow]
  simp only [mul_add, Finset.mul_sum]
  simp only [mul_left_comm X (C _), mul_comm X (scalarKernel _), scalarKernel_mul_X,
    ← coverRatio_pow, scaledLogDerivative_linear, scaledLogDerivative_moving, pow_one]
  simp only [mul_sub, mul_one, Finset.sum_sub_distrib, ← map_sum]
  rw [fourier_pairing_sum, ← orbit_fourier]
  ring

private theorem derivative_groundDiagonalScalar (a b : Charge lattice) (p : Momentum) :
    derivative (groundDiagonalScalar a b p) =
      groundDiagonalScalar a b p * derivative (chargedIterateLog a b p) := by
  let v := (U * diagonalLinearUnit) ^ e a b 0 *
    (U * diagonalMovingUnit 1 (by decide) (by decide)) ^ e a b 1 *
    (U * diagonalMovingUnit 2 (by decide) (by decide)) ^ e a b 2
  let u := U ^ momentumExponent a p * v
  have hu : u = U ^ momentumExponent a (shift b p) * regularChargedContraction a b := by
    simp only [u, v, regularChargedContraction, momentumExponent_shift, orbit_pairing_sum,
      zpow_add, mul_zpow, mul_assoc, mul_left_comm, mul_comm]
  have hg : groundDiagonalScalar a b p =
      C (chargePhase a (shift b p) * chargePhase b p) * (u : PowerSeries ℂ) := by
    rw [hu, Units.val_mul, groundDiagonalScalar, mul_assoc]
  have hd : logDerivative u = derivative (chargedIterateLog a b p) := by
    simp only [u, logDerivative_mul, logDerivative_zpow U, logDerivative_cover]
    rw [show logDerivative v = _ from logDerivative_orbit a b]
    simp only [chargedIterateLog, map_add, map_sum, Derivation.leibniz, smul_eq_mul,
      PowerSeries.derivative_C, mul_zero, add_zero, derivative_integratedScalarKernel,
      div_eq_mul_inv, map_mul, mul_assoc]
  calc
    derivative (groundDiagonalScalar a b p) =
        C (chargePhase a (shift b p) * chargePhase b p) * derivative (u : PowerSeries ℂ) := by
      rw [hg, Derivation.leibniz, PowerSeries.derivative_C, smul_eq_mul, smul_eq_mul,
        mul_zero, add_zero]
    _ = _ := by rw [← val_mul_logDerivative u, hd, hg, mul_assoc]

/-- The native charged diagonal scalar is the substituted exponential of
the integrated Fourier kernels and the input-momentum logarithm. -/
theorem groundDiagonalScalar_eq_exp (a b : Charge lattice) (p : Momentum) :
    groundDiagonalScalar a b p =
      C (epsilon lattice a b * chargePhase (a + b) p) *
        (PowerSeries.exp ℂ).subst (chargedIterateLog a b p) := by
  let L := chargedIterateLog a b p
  let E : PowerSeries ℂ := (PowerSeries.exp ℂ).subst L
  have hj (r : ℂ) : constantCoeff (integratedScalarKernel r) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      P48qIntegratedJetKernels.coeff_integratedScalarKernel, ite_eq_left rfl]
  have hL : constantCoeff L = 0 := by
    simp only [L, chargedIterateLog, map_add, map_mul, map_sum, PowerSeries.constantCoeff_log,
      hj, mul_zero, Finset.sum_const_zero, add_zero]
  have hE : constantCoeff E = 1 := by
    change constantCoeff ((PowerSeries.exp ℂ).subst L) = 1
    rw [PowerSeries.constantCoeff_eq, PowerSeries.constantCoeff_subst_of_constantCoeff_zero hL,
      PowerSeries.constantCoeff_exp, map_one]
  have hunit : IsUnit E := PowerSeries.isUnit_iff_constantCoeff.mpr (hE ▸ isUnit_one)
  let u := hunit.unit
  have hu : (u : PowerSeries ℂ) = E := IsUnit.unit_spec _
  have hd : derivative (u : PowerSeries ℂ) = (u : PowerSeries ℂ) * derivative L := by
    rw [hu]
    change derivative ((PowerSeries.exp ℂ).subst L) = E * derivative L
    rw [PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hL),
      PowerSeries.derivative_exp]
  have hc : constantCoeff (↑u⁻¹ : PowerSeries ℂ) = 1 := by
    have h := congrArg (constantCoeff (R := ℂ)) (Units.mul_inv u)
    rw [map_mul, hu, hE, one_mul, map_one] at h
    exact h
  have hratio : groundDiagonalScalar a b p * (↑u⁻¹ : PowerSeries ℂ) =
      C (epsilon lattice a b * chargePhase (a + b) p) := by
    let : HasUniqueDiv ℂ := .of_module_rat ℂ
    apply derivative.ext
    · rw [Derivation.leibniz, PowerSeries.derivative_inv, derivative_groundDiagonalScalar,
        PowerSeries.derivative_C, hd, smul_eq_mul, smul_eq_mul]
      change _ * (-_ ^ 2 * (_ * derivative L)) + _ * (_ * derivative L) = 0
      calc
        _ = (groundDiagonalScalar a b p * ↑u⁻¹ * derivative L) *
              (1 - (u : PowerSeries ℂ) * ↑u⁻¹) := by ring
        _ = 0 := by rw [Units.mul_inv, sub_self, mul_zero]
    · rw [map_mul, hc, mul_one, groundDiagonalScalar_const, PowerSeries.constantCoeff_C]
  change groundDiagonalScalar a b p = C _ * E
  rw [← hu]
  rw [← hratio, Units.inv_mul_cancel_right]

#print axioms groundDiagonalScalar_eq_exp

end

end D5.S3.VertexAlgebra.Lattice.Orbifold.P48qThirdTwistedField
