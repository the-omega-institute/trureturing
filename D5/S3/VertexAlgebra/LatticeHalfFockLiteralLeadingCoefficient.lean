/- GID: D5/S3/VertexAlgebra/LatticeHalfFockLiteralLeadingCoefficient
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockLiteralLeadingCoefficient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: First nonzero coefficient of the literal half-integer charged chart. -/

import D5.S3.VertexAlgebra.LatticeHalfFockOriginalTwoSheetChartRecurrence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockLiteralLeadingCoefficient

open LatticeHalfFockBranchClearing LatticeHalfFockOriginalTwoSheetChartRecurrence
open scoped BigOperators

noncomputable section

theorem literal_clearing_leading_coefficient (gram shift : ℤ) :
    (∑ degree ∈ Finset.range (2 * gram.natAbs + 1),
      (clearedPolynomial gram).coeff degree *
        halfIntegerBinomial (shift - degree) (2 * gram.toNat)) =
      (2 : ℂ) ^ (-2 * gram) := by
  classical
  let root := PowerSeries.binomialSeries ℂ (-1 / 2 : ℂ)
  let base := PowerSeries.binomialSeries ℂ ((shift : ℂ) / 2)
  have multiple (scalar : ℂ) (degree : ℕ) :
      PowerSeries.binomialSeries ℂ ((degree : ℂ) * scalar) =
        (PowerSeries.binomialSeries ℂ scalar) ^ degree := by
    induction degree with
    | zero => simp
    | succ degree previous =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        PowerSeries.binomialSeries_add, previous, pow_succ]
  have binomial (degree : ℕ) :
      PowerSeries.binomialSeries ℂ (((shift - degree : ℤ) : ℂ) / 2) =
        base * root ^ degree := by
    have exponent : (((shift - degree : ℤ) : ℂ) / 2) =
        (shift : ℂ) / 2 + (degree : ℂ) * (-1 / 2) := by
      push_cast
      ring
    rw [exponent, PowerSeries.binomialSeries_add, multiple]
  have evaluation :
      (clearedPolynomial gram).eval₂ (PowerSeries.C : ℂ →+* PowerSeries ℂ) root =
        (1 - root) ^ (2 * gram.toNat) * (1 + root) ^ (2 * (-gram).toNat) := by
    simp [clearedPolynomial, Polynomial.eval₂_pow, Polynomial.eval₂_sub,
      Polynomial.eval₂_add, Polynomial.eval₂_one, Polynomial.eval₂_X]
  have evaluationSum := Polynomial.eval₂_eq_sum_range'
    (PowerSeries.C : ℂ →+* PowerSeries ℂ)
    (Nat.lt_succ_of_le (cleared_polynomial_degree gram)) root
  have coefficient :
      (∑ degree ∈ Finset.range (2 * gram.natAbs + 1),
        (clearedPolynomial gram).coeff degree *
          halfIntegerBinomial (shift - degree) (2 * gram.toNat)) =
        PowerSeries.coeff (2 * gram.toNat) (base *
          ((clearedPolynomial gram).eval₂ (PowerSeries.C : ℂ →+* PowerSeries ℂ) root)) := by
    rw [evaluationSum, Finset.mul_sum, map_sum]
    apply Finset.sum_congr rfl
    intro degree member
    rw [mul_left_comm base, PowerSeries.coeff_C_mul, ← binomial]
    simp [halfIntegerBinomial]
  rw [coefficient, evaluation]
  let tail := PowerSeries.mk (fun degree => PowerSeries.coeff (degree + 1) (1 - root))
  have factor : 1 - root = PowerSeries.X * tail := by
    have split := PowerSeries.eq_X_mul_shift_add_const (1 - root)
    simpa [tail, root] using split
  have firstCoefficient : PowerSeries.coeff 0 tail = (1 / 2 : ℂ) := by
    simp [tail, root, Ring.choose_one_right]
    ring
  rw [factor, mul_pow]
  rw [show base * (PowerSeries.X ^ (2 * gram.toNat) * tail ^ (2 * gram.toNat) *
      (1 + root) ^ (2 * (-gram).toNat)) = PowerSeries.X ^ (2 * gram.toNat) *
        (base * tail ^ (2 * gram.toNat) * (1 + root) ^ (2 * (-gram).toNat)) by ring]
  have coefficientShift := PowerSeries.coeff_X_pow_mul
    (base * tail ^ (2 * gram.toNat) * (1 + root) ^ (2 * (-gram).toNat))
    (2 * gram.toNat) 0
  simp only [zero_add] at coefficientShift
  rw [coefficientShift]
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul, map_pow,
    base, PowerSeries.binomialSeries_constantCoeff, one_mul, map_add, map_one, root]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, firstCoefficient]
  norm_num only
  simp only [one_div, inv_pow]
  have inversePower : ((2 : ℂ) ^ (2 * gram.toNat))⁻¹ =
      (2 : ℂ) ^ (-((2 * gram.toNat : ℕ) : ℤ)) := by
    simp only [zpow_neg, zpow_natCast]
  have positivePower : (2 : ℂ) ^ (2 * (-gram).toNat) =
      (2 : ℂ) ^ ((2 * (-gram).toNat : ℕ) : ℤ) := by
    simp only [zpow_natCast]
  rw [inversePower, positivePower]
  rw [← zpow_add₀ (by norm_num : (2 : ℂ) ≠ 0)]
  congr 1
  omega

end
end D5.S3.VertexAlgebra.LatticeHalfFockLiteralLeadingCoefficient
