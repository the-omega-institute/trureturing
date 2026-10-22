/- GID: D5/S3/VertexAlgebra/LatticeHalfFockRegularChargedScalar
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockRegularChargedScalar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Two-sheet closed form of the actual original charged exponential scalar. -/

import D5.S3.VertexAlgebra.LatticeHalfFockFormalTwoSheetSubstitution

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeHalfFockRegularChargedScalar

open LatticeGeneratingFieldLocality LatticeHalfFockFiniteCorrection
open LatticeHalfFockCreationEnergyContraction LatticeHalfFockChargedTensorCoefficients
open LatticeHalfFockFormalTwoSheetSubstitution
open scoped BigOperators

noncomputable section

local macro "weighted_energy_log_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction.weighted_energy_log))

local macro "scaled_binomial_derivative_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.scaled_binomial_derivative))

local macro "scalar_ode_uniqueness_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
    `D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients.solution_unique))

local macro "charged_log_substitution_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction.charged_log_has_substitution))

local macro "charged_gaussian_initial_supplier" : term =>
  pure (Lean.mkIdent (Lean.mkPrivateNameCore
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction
    `D5.S3.VertexAlgebra.LatticeHalfFockCreationEnergyContraction.charged_gaussian_initial))

private theorem root_coefficient (degree : ℕ) :
    PowerSeries.coeff degree halfRoot = halfBinomial degree := by
  have evaluation : (descPochhammer ℤ degree).smeval (-1 / 2 : ℂ) =
      ∏ offset ∈ Finset.range degree, (-1 / 2 - (offset : ℂ)) := by
    rw [← Polynomial.eval₂_smulOneHom_eq_smeval]
    have hom : (RingHom.smulOneHom : ℤ →+* ℂ) = Int.castRingHom ℂ := by
      ext scalar
      simp [RingHom.smulOneHom_apply, zsmul_eq_mul]
    rw [hom]
    rw [← Polynomial.eval_map, descPochhammer_map, descPochhammer_eval_eq_prod_range]
  rw [halfRoot, PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one,
    Ring.choose_eq_smul, smul_eq_mul, evaluation]
  unfold halfBinomial
  ring

private theorem root_positive_coefficient (degree : ℕ) :
    PowerSeries.coeff (degree + 1) (halfRoot - 1) = halfBinomial (degree + 1) := by
  simp [map_sub, PowerSeries.coeff_one, root_coefficient]

private theorem root_positive_constant : PowerSeries.coeff 0 (halfRoot - 1) = 0 := by
  simp [halfRoot]

private theorem positive_square_coefficient (degree : ℕ) :
    PowerSeries.coeff (degree + 1) ((halfRoot - 1) ^ 2) =
      ∑ frequency ∈ Finset.range degree,
        halfBinomial (frequency + 1) * halfBinomial (degree - frequency) := by
  cases degree with
  | zero => simp [pow_two, PowerSeries.coeff_one_mul, halfRoot]
  | succ degree =>
    rw [pow_two, PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
    simp only [root_positive_constant, zero_mul, zero_add]
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp only [root_positive_constant, mul_zero, zero_add]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    apply Finset.sum_congr rfl
    intro frequency member
    have bound := Finset.mem_range.mp member
    rw [root_positive_coefficient, root_positive_coefficient,
      show degree - frequency + 1 = degree + 1 - frequency by omega]

private theorem original_logarithmic_driver (D : LatticeData)
    (first second : Charge D) :
    PowerSeries.X * PowerSeries.derivative ℂ (chargedEnergyLog D first second) =
      PowerSeries.C ((bilinear D first first : ℂ) + bilinear D first second) *
        (halfRoot - 1) +
      PowerSeries.C ((bilinear D first first : ℂ) / 2) * (halfRoot - 1) ^ 2 := by
  apply PowerSeries.ext
  intro degree
  cases degree with
  | zero => simp [halfRoot, pow_two]
  | succ degree =>
    rw [mul_comm PowerSeries.X, PowerSeries.coeff_succ_mul_X,
      PowerSeries.coeff_derivative]
    simp only [chargedEnergyLog, PowerSeries.coeff_mk]
    rw [mul_comm, weighted_energy_log_supplier]
    simp only [map_add, add_mul, PowerSeries.coeff_C_mul, root_positive_coefficient,
      positive_square_coefficient]

def regularScalarOnSheet (D : LatticeData) (first second : Charge D) : PowerSeries ℂ :=
  PowerSeries.rescale (-1 : ℂ)
      (PowerSeries.binomialSeries (R := ℤ) ℂ
        (chargeNorm D first + 2 * bilinear D first second)) *
    PowerSeries.binomialSeries (R := ℤ) ℂ (-chargeNorm D first)

private theorem minus_constant :
    PowerSeries.constantCoeff (1 - PowerSeries.X : PowerSeries ℂ) ≠ 0 := by simp

private theorem plus_constant :
    PowerSeries.constantCoeff (1 + PowerSeries.X : PowerSeries ℂ) ≠ 0 := by simp

private theorem sheet_constant : PowerSeries.constantCoeff twoSheetSeries = 0 := by
  simp [twoSheetSeries]

private theorem sheet_apply (series : PowerSeries ℂ) :
    sheetSubstitution series = series.subst twoSheetSeries := by
  exact congrFun (PowerSeries.coe_substAlgHom
    (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant)) series

private theorem sheet_X : sheetSubstitution PowerSeries.X = twoSheetSeries :=
  PowerSeries.substAlgHom_X _

private theorem sheet_C (scalar : ℂ) :
    sheetSubstitution (PowerSeries.C scalar) = PowerSeries.C scalar :=
  sheetSubstitution.commutes scalar

private theorem sheet_derivative :
    PowerSeries.derivative ℂ twoSheetSeries =
      4 * (1 + PowerSeries.X) * ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 3 := by
  have inverse := PowerSeries.mul_inv_cancel (1 - PowerSeries.X : PowerSeries ℂ) minus_constant
  have fourDerivative : PowerSeries.derivative ℂ (4 : PowerSeries ℂ) = 0 := by
    simpa only [map_ofNat] using PowerSeries.derivative_C (R := ℂ) (r := (4 : ℂ))
  have expanded : PowerSeries.derivative ℂ twoSheetSeries =
      4 * ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 2 +
        8 * PowerSeries.X * ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 3 := by
    simp [twoSheetSeries, Derivation.leibniz, Derivation.leibniz_pow,
      PowerSeries.derivative_inv', smul_eq_mul, fourDerivative]
    ring
  rw [expanded]
  linear_combination -4 * ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 2 * inverse

def regularScalarDriver (D : LatticeData) (first second : Charge D) : PowerSeries ℂ :=
  PowerSeries.C (-((chargeNorm D first + 2 * bilinear D first second : ℤ) : ℂ)) *
      (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ +
    PowerSeries.C (-(chargeNorm D first : ℂ)) * (1 + PowerSeries.X : PowerSeries ℂ)⁻¹

private theorem original_log_two_sheet_derivative (D : LatticeData)
    (first second : Charge D) :
    PowerSeries.derivative ℂ (sheetSubstitution (chargedEnergyLog D first second)) =
      regularScalarDriver D first second := by
  have minus := PowerSeries.mul_inv_cancel (1 - PowerSeries.X : PowerSeries ℂ) minus_constant
  have plus := PowerSeries.mul_inv_cancel (1 + PowerSeries.X : PowerSeries ℂ) plus_constant
  have difference : (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ -
      (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ =
        2 * PowerSeries.X * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ *
          (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ := by
    linear_combination (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ * minus -
      (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ * plus
  have half : 2 * PowerSeries.C ((bilinear D first first : ℂ) / 2) =
      (PowerSeries.C (bilinear D first first : ℂ) : PowerSeries ℂ) := by
    have equality : (2 : ℂ) * ((bilinear D first first : ℂ) / 2) =
        (bilinear D first first : ℂ) := by ring
    simpa only [map_mul, map_ofNat] using
      congrArg (PowerSeries.C : ℂ →+* PowerSeries ℂ) equality
  have root_minus_one : sheetSubstitution halfRoot - 1 =
      -2 * PowerSeries.X * (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ := by
    rw [original_half_root_two_sheet]
    linear_combination plus
  have pulled := congrArg sheetSubstitution (original_logarithmic_driver D first second)
  simp only [map_mul, map_add, map_sub, map_pow, map_one, sheet_C, sheet_X] at pulled
  rw [root_minus_one] at pulled
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ))
  calc
    PowerSeries.X * PowerSeries.derivative ℂ
        (sheetSubstitution (chargedEnergyLog D first second)) =
      (twoSheetSeries * sheetSubstitution
          (PowerSeries.derivative ℂ (chargedEnergyLog D first second))) *
        (1 + PowerSeries.X) * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ := by
      rw [sheet_apply, PowerSeries.derivative_subst
        (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant),
        ← sheet_apply, sheet_derivative]
      unfold twoSheetSeries
      ring
    _ = PowerSeries.X * regularScalarDriver D first second := by
      rw [pulled]
      simp only [regularScalarDriver, chargeNorm, Int.cast_add, Int.cast_mul,
        Int.cast_ofNat, map_add, map_mul, map_neg, map_ofNat]
      linear_combination
        (-2 * (PowerSeries.C (bilinear D first first : ℂ) +
            PowerSeries.C (bilinear D first second : ℂ)) * PowerSeries.X *
              (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ +
          4 * PowerSeries.C ((bilinear D first first : ℂ) / 2) * PowerSeries.X ^ 2 *
            (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ *
              (1 + PowerSeries.X : PowerSeries ℂ)⁻¹) * plus -
        PowerSeries.C (bilinear D first first : ℂ) * PowerSeries.X * difference +
        2 * PowerSeries.X ^ 2 * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ *
          (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ * half

private theorem regular_scalar_derivative (D : LatticeData) (first second : Charge D) :
    PowerSeries.derivative ℂ (regularScalarOnSheet D first second) =
      regularScalarOnSheet D first second * regularScalarDriver D first second := by
  let minus := PowerSeries.rescale (-1 : ℂ)
    (PowerSeries.binomialSeries (R := ℤ) ℂ
      (chargeNorm D first + 2 * bilinear D first second))
  let plus := PowerSeries.binomialSeries (R := ℤ) ℂ (-chargeNorm D first)
  have minusLaw : PowerSeries.derivative ℂ minus =
      (PowerSeries.C (-((chargeNorm D first + 2 * bilinear D first second : ℤ) : ℂ)) *
        minus) * (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ := by
    apply (PowerSeries.eq_mul_inv_iff_mul_eq minus_constant).2
    have original := scaled_binomial_derivative_supplier
      (chargeNorm D first + 2 * bilinear D first second) (-1 : ℂ)
    simpa only [minus, map_neg, map_one, neg_one_mul, mul_neg_one,
      ← sub_eq_add_neg] using original
  have plusLaw : PowerSeries.derivative ℂ plus =
      (PowerSeries.C (-(chargeNorm D first : ℂ)) * plus) *
        (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ := by
    apply (PowerSeries.eq_mul_inv_iff_mul_eq plus_constant).2
    have original := scaled_binomial_derivative_supplier (-chargeNorm D first) (1 : ℂ)
    simpa [plus] using original
  change PowerSeries.derivative ℂ (minus * plus) =
    minus * plus * regularScalarDriver D first second
  rw [Derivation.leibniz, minusLaw, plusLaw]
  unfold regularScalarDriver
  ring

private theorem gaussian_sheet_derivative (D : LatticeData) (first second : Charge D) :
    PowerSeries.derivative ℂ (sheetSubstitution (chargedEnergyGaussian D first second)) =
      sheetSubstitution (chargedEnergyGaussian D first second) *
        regularScalarDriver D first second := by
  have original : PowerSeries.derivative ℂ (chargedEnergyGaussian D first second) =
      chargedEnergyGaussian D first second *
        PowerSeries.derivative ℂ (chargedEnergyLog D first second) := by
    rw [chargedEnergyGaussian, PowerSeries.derivative_subst
      (charged_log_substitution_supplier D first second), PowerSeries.derivative_exp]
  have driver := original_log_two_sheet_derivative D first second
  rw [sheet_apply, PowerSeries.derivative_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant), ← sheet_apply] at driver
  rw [sheet_apply, PowerSeries.derivative_subst
    (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant), ← sheet_apply,
    original, map_mul, mul_assoc, driver, sheet_apply]

private theorem gaussian_sheet_initial (D : LatticeData) (first second : Charge D) :
    PowerSeries.coeff 0 (sheetSubstitution (chargedEnergyGaussian D first second)) = 1 := by
  rw [sheet_apply, PowerSeries.coeff_subst'
    (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant), finsum_eq_single _ 0]
  · simpa using charged_gaussian_initial_supplier D first second
  · intro degree nonzero
    rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, sheet_constant]
    simp [nonzero]

theorem actual_charged_scalar_two_sheet (D : LatticeData) (first second : Charge D) :
    sheetSubstitution (chargedEnergyGaussian D first second) =
      regularScalarOnSheet D first second := by
  apply scalar_ode_uniqueness_supplier _ _ (regularScalarDriver D first second)
    (gaussian_sheet_derivative D first second) (regular_scalar_derivative D first second)
  rw [gaussian_sheet_initial]
  have initial (exponent : ℤ) :
      PowerSeries.constantCoeff
        (PowerSeries.rescale (-1 : ℂ)
          (PowerSeries.binomialSeries (R := ℤ) ℂ exponent)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
    simp only [pow_zero, one_mul, PowerSeries.binomialSeries_coeff,
      Ring.choose_zero_right, one_smul]
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, regularScalarOnSheet, map_mul,
    initial, PowerSeries.binomialSeries_constantCoeff, one_mul]

private def plusBinomial (exponent : ℤ) : PowerSeries ℂ :=
  PowerSeries.binomialSeries (R := ℤ) ℂ exponent

private def minusBinomial (exponent : ℤ) : PowerSeries ℂ :=
  PowerSeries.rescale (-1 : ℂ) (plusBinomial exponent)

private theorem plus_add (first second : ℤ) :
    plusBinomial (first + second) = plusBinomial first * plusBinomial second :=
  PowerSeries.binomialSeries_add first second

private theorem minus_add (first second : ℤ) :
    minusBinomial (first + second) = minusBinomial first * minusBinomial second := by
  rw [minusBinomial, plus_add, map_mul]
  rfl

private theorem plus_negative_power (degree : ℕ) :
    plusBinomial (-(degree : ℤ)) = plusBinomial (-1) ^ degree := by
  induction degree with
  | zero => simp [plusBinomial]
  | succ degree previous =>
    rw [Nat.cast_add, Nat.cast_one, neg_add, plus_add, previous, pow_succ]

private theorem minus_negative_power (degree : ℕ) :
    minusBinomial (-(degree : ℤ)) = minusBinomial (-1) ^ degree := by
  rw [minusBinomial, plus_negative_power, map_pow]
  rfl

private theorem minus_inverse : minusBinomial (-1) =
    (1 - PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one minus_constant).2
  have one : minusBinomial 1 = (1 - PowerSeries.X : PowerSeries ℂ) := by
    unfold minusBinomial plusBinomial
    rw [show (1 : ℤ) = (1 : ℕ) by norm_num, PowerSeries.binomialSeries_nat]
    simp [sub_eq_add_neg]
  rw [← one, ← minus_add]
  simp [minusBinomial, plusBinomial]

private theorem plus_inverse : plusBinomial (-1) =
    (1 + PowerSeries.X : PowerSeries ℂ)⁻¹ := by
  apply (PowerSeries.eq_inv_iff_mul_eq_one plus_constant).2
  have one : plusBinomial 1 = (1 + PowerSeries.X : PowerSeries ℂ) := by
    simpa [plusBinomial] using PowerSeries.binomialSeries_nat (A := ℂ) (R := ℤ) 1
  rw [← one, ← plus_add]
  simp [plusBinomial]

private theorem branch_counts (gram : ℤ) :
    ((gram.natAbs : ℤ) + gram).toNat = 2 * gram.toNat ∧
      2 * gram.toNat + 2 * (-gram).toNat = 2 * gram.natAbs ∧
        (((gram.natAbs : ℤ) + gram).toNat : ℤ) = (gram.natAbs : ℤ) + gram := by
  by_cases positive : 0 ≤ gram
  · have absolute : (gram.natAbs : ℤ) = gram := by
      rw [Int.natCast_natAbs, abs_of_nonneg positive]
    omega
  · have absolute : (gram.natAbs : ℤ) = -gram := by
      rw [Int.natCast_natAbs, abs_of_neg (by omega)]
    omega

private theorem cleared_scalar_sheet (gram : ℤ) :
    (LatticeHalfFockBranchClearing.clearedPolynomial gram).eval₂
        (PowerSeries.C : ℂ →+* PowerSeries ℂ) (sheetSubstitution halfRoot) =
      2 ^ (2 * gram.natAbs) * PowerSeries.X ^ ((gram.natAbs : ℤ) + gram).toNat *
        plusBinomial (-(2 * gram.natAbs : ℤ)) := by
  have plus := PowerSeries.mul_inv_cancel (1 + PowerSeries.X : PowerSeries ℂ) plus_constant
  have first : 1 - sheetSubstitution halfRoot =
      2 * PowerSeries.X * plusBinomial (-1) := by
    rw [original_half_root_two_sheet, plus_inverse]
    linear_combination -plus
  have second : 1 + sheetSubstitution halfRoot = 2 * plusBinomial (-1) := by
    rw [original_half_root_two_sheet, plus_inverse]
    linear_combination -plus
  simp only [LatticeHalfFockBranchClearing.clearedPolynomial, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub, Polynomial.eval₂_add,
    Polynomial.eval₂_one, Polynomial.eval₂_X]
  rw [first, second, (branch_counts gram).1]
  have sum := (branch_counts gram).2.1
  calc
    (2 * PowerSeries.X * plusBinomial (-1)) ^ (2 * gram.toNat) *
        (2 * plusBinomial (-1)) ^ (2 * (-gram).toNat) =
      2 ^ (2 * gram.toNat + 2 * (-gram).toNat) *
        PowerSeries.X ^ (2 * gram.toNat) *
          plusBinomial (-1) ^ (2 * gram.toNat + 2 * (-gram).toNat) := by
      simp only [mul_pow, pow_add]
      ring
    _ = _ := by
      rw [sum, ← plus_negative_power]
      congr 1

private theorem scalar_normal_sheet (D : LatticeData) (first second : Charge D) :
    twoSheetSeries ^ ((bilinear D first second).natAbs + bilinear D first second : ℤ).toNat *
        regularScalarOnSheet D first second *
          twoSheetLabel (chargeNorm D first - 2 * (bilinear D first second).natAbs) =
      4 ^ ((bilinear D first second).natAbs + bilinear D first second : ℤ).toNat *
        PowerSeries.X ^ ((bilinear D first second).natAbs + bilinear D first second : ℤ).toNat *
          plusBinomial (-(2 * (bilinear D first second).natAbs : ℤ)) := by
  let gram := bilinear D first second
  let start := ((gram.natAbs : ℤ) + gram).toNat
  let norm := chargeNorm D first
  have parameter : twoSheetSeries = 4 * PowerSeries.X * minusBinomial (-2) := by
    rw [twoSheetSeries, ← minus_inverse, ← minus_negative_power 2]
    norm_num
  have exponent : -2 * (start : ℤ) + (norm + 2 * gram) +
      (-(norm - 2 * gram.natAbs)) = 0 := by
    have count := (branch_counts gram).2.2
    change (start : ℤ) = (gram.natAbs : ℤ) + gram at count
    omega
  have scaled_power : minusBinomial (-2) ^ start = minusBinomial (-2 * (start : ℤ)) := by
    rw [show (-2 : ℤ) = -(2 : ℕ) by norm_num, minus_negative_power, ← pow_mul,
      ← minus_negative_power]
    congr 1
  change twoSheetSeries ^ start * (minusBinomial (norm + 2 * gram) * plusBinomial (-norm)) *
    (plusBinomial (norm - 2 * gram.natAbs) * minusBinomial (-(norm - 2 * gram.natAbs))) = _
  rw [parameter, mul_pow, mul_pow, scaled_power]
  calc
    _ = 4 ^ start * PowerSeries.X ^ start *
        (minusBinomial (-2 * (start : ℤ)) * minusBinomial (norm + 2 * gram) *
          minusBinomial (-(norm - 2 * gram.natAbs))) *
        (plusBinomial (-norm) * plusBinomial (norm - 2 * gram.natAbs)) := by ring
    _ = _ := by
      rw [← minus_add, ← minus_add, exponent, ← plus_add]
      simp only [minusBinomial, plusBinomial, PowerSeries.binomialSeries_zero,
        map_one, mul_one]
      congr 1
      congr 1
      ring

private theorem sheet_injective : Function.Injective sheetSubstitution := by
  have linear : PowerSeries.coeff 1 twoSheetSeries = 4 := by
    have representation : twoSheetSeries =
        (4 * ((1 - PowerSeries.X : PowerSeries ℂ)⁻¹) ^ 2) * PowerSeries.X := by
      unfold twoSheetSeries
      ring
    rw [representation, PowerSeries.coeff_succ_mul_X 0,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    norm_num [map_ofNat]
  have linearUnit : IsUnit (PowerSeries.coeff 1 twoSheetSeries) := by
    rw [linear]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  let inverse := twoSheetSeries.substInvOfIsUnit linearUnit
  have recover (series : PowerSeries ℂ) :
      (sheetSubstitution series).subst inverse = series := by
    rw [sheet_apply, PowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.of_constantCoeff_zero sheet_constant)
      (PowerSeries.HasSubst.substInvOfIsUnit twoSheetSeries linearUnit),
      PowerSeries.subst_substInvOfIsUnit_right twoSheetSeries sheet_constant linearUnit,
      PowerSeries.X_subst]
  intro first second equal
  simpa only [recover] using congrArg (fun series : PowerSeries ℂ => series.subst inverse) equal

private theorem original_norm_add (D : LatticeData) (left right : Charge D) :
    chargeNorm D (left + right) =
      chargeNorm D left + chargeNorm D right + 2 * bilinear D left right := by
  have first : bilinear D (left + right) left = bilinear D left left + bilinear D right left := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  have second : bilinear D (left + right) right =
      bilinear D left right + bilinear D right right := by
    simp [bilinear, add_mul, Finset.sum_add_distrib]
  unfold chargeNorm
  rw [LatticeActualGeneratorLocality.bilinear_add_right, first, second,
    LatticeFiniteNegativeGeneration.bilinear_symmetric D right left]
  ring

private theorem original_ground_normalization (D : LatticeData) (left right : Charge D) :
    chargeScalar D left * chargeScalar D right *
        (2 : ℂ) ^ (2 * (bilinear D left right).natAbs) =
      chargeScalar D (left + right) *
        (4 : ℂ) ^ (((bilinear D left right).natAbs : ℤ) + bilinear D left right).toNat := by
  let gram := bilinear D left right
  let start := ((gram.natAbs : ℤ) + gram).toNat
  have separate : chargeScalar D left * chargeScalar D right =
      chargeScalar D (left + right) * (2 : ℂ) ^ (2 * gram) := by
    unfold chargeScalar
    rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), original_norm_add]
    congr 1
    dsimp [gram]
    ring
  have counts : 2 * gram + ((2 * gram.natAbs : ℕ) : ℤ) = ((2 * start : ℕ) : ℤ) := by
    have count := (branch_counts gram).2.2
    change (start : ℤ) = (gram.natAbs : ℤ) + gram at count
    simp only [Nat.cast_mul, Nat.cast_ofNat, count]
    ring
  have powers : (2 : ℂ) ^ (2 * gram) * 2 ^ (2 * gram.natAbs) = 4 ^ start := by
    rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0), counts, zpow_natCast,
      pow_mul]
    norm_num
  rw [separate, mul_assoc, powers]

theorem actual_regular_charged_scalar_ratio (D : LatticeData) (left right : Charge D) :
    PowerSeries.C (chargeScalar D left * chargeScalar D right * epsilon D left right) *
        (LatticeHalfFockBranchClearing.clearedPolynomial (bilinear D left right)).eval₂
          (PowerSeries.C : ℂ →+* PowerSeries ℂ) halfRoot =
      PowerSeries.C (chargeScalar D (left + right) * epsilon D left right) *
        PowerSeries.X ^ (((bilinear D left right).natAbs : ℤ) + bilinear D left right).toNat *
          chargedEnergyGaussian D left right *
            halfLabel (chargeNorm D left - 2 * (bilinear D left right).natAbs) := by
  apply sheet_injective
  have transport : sheetSubstitution
      ((LatticeHalfFockBranchClearing.clearedPolynomial (bilinear D left right)).eval₂
        (PowerSeries.C : ℂ →+* PowerSeries ℂ) halfRoot) =
      (LatticeHalfFockBranchClearing.clearedPolynomial (bilinear D left right)).eval₂
        (PowerSeries.C : ℂ →+* PowerSeries ℂ) (sheetSubstitution halfRoot) := by
    simp only [LatticeHalfFockBranchClearing.clearedPolynomial, Polynomial.eval₂_mul,
      Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_sub,
      Polynomial.eval₂_one, Polynomial.eval₂_X, map_mul, map_pow, map_sub, map_add, map_one]
  simp only [map_mul, map_pow, sheet_C, sheet_X]
  rw [transport, cleared_scalar_sheet, actual_charged_scalar_two_sheet,
    original_half_integer_all_label_two_sheet]
  have normalization := congrArg (PowerSeries.C : ℂ →+* PowerSeries ℂ)
    (original_ground_normalization D left right)
  simp only [map_mul, map_pow, map_ofNat] at normalization
  calc
    _ = (PowerSeries.C (chargeScalar D left) * PowerSeries.C (chargeScalar D right) *
          2 ^ (2 * (bilinear D left right).natAbs)) * PowerSeries.C (epsilon D left right) *
        (PowerSeries.X ^ (((bilinear D left right).natAbs : ℤ) + bilinear D left right).toNat *
          plusBinomial (-(2 * (bilinear D left right).natAbs : ℤ))) := by
      ring
    _ = (PowerSeries.C (chargeScalar D (left + right)) *
          4 ^ (((bilinear D left right).natAbs : ℤ) + bilinear D left right).toNat) *
        PowerSeries.C (epsilon D left right) *
        (PowerSeries.X ^ (((bilinear D left right).natAbs : ℤ) + bilinear D left right).toNat *
          plusBinomial (-(2 * (bilinear D left right).natAbs : ℤ))) := by rw [normalization]
    _ = PowerSeries.C (chargeScalar D (left + right) * epsilon D left right) *
        (twoSheetSeries ^ (((bilinear D left right).natAbs : ℤ) + bilinear D left right).toNat *
          regularScalarOnSheet D left right *
            twoSheetLabel (chargeNorm D left - 2 * (bilinear D left right).natAbs)) := by
      rw [scalar_normal_sheet]
      simp only [map_mul]
      ring
    _ = _ := by
      simp only [map_mul]
      ring

#print axioms original_log_two_sheet_derivative
#print axioms actual_charged_scalar_two_sheet
#print axioms cleared_scalar_sheet
#print axioms scalar_normal_sheet
#print axioms actual_regular_charged_scalar_ratio

#print axioms original_logarithmic_driver

end

end D5.S3.VertexAlgebra.LatticeHalfFockRegularChargedScalar
