/- GID: D5/S3/VertexAlgebra/LatticeHalfFockBranchClearing
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeHalfFockBranchClearing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Both native contraction branches are cleared by their exact binomial factors. -/

import D5.S3.VertexAlgebra.LatticeHalfFockChargedCoefficients
import Mathlib.Algebra.Polynomial.Reverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

namespace D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing

open LatticeGeneratingFieldLocality LatticeHalfFockChargedCoefficients
open scoped BigOperators

noncomputable section

private theorem binomial_shift (amount : ℕ) (exponent : ℤ) :
    (1 + PowerSeries.X : PowerSeries ℂ) ^ amount *
      PowerSeries.binomialSeries ℂ exponent =
        PowerSeries.binomialSeries ℂ ((amount : ℤ) + exponent) := by
  rw [← PowerSeries.binomialSeries_nat (R := ℤ), PowerSeries.binomialSeries_add]

private theorem rescale_positive (amount : ℕ) :
    PowerSeries.rescale (-1 : ℂ) ((1 + PowerSeries.X : PowerSeries ℂ) ^ amount) =
      (1 - PowerSeries.X : PowerSeries ℂ) ^ amount := by
  simp only [map_pow, map_add, map_one, PowerSeries.rescale_neg_one_X, sub_eq_add_neg]

theorem half_contraction_two_branch_clearing (D : LatticeData) (left right : Charge D) :
    (1 - PowerSeries.X : PowerSeries ℂ) ^ (-bilinear D left right).toNat *
      (1 + PowerSeries.X : PowerSeries ℂ) ^ (bilinear D left right).toNat *
        halfContraction D left right =
      (1 - PowerSeries.X : PowerSeries ℂ) ^ (bilinear D left right).toNat *
        (1 + PowerSeries.X : PowerSeries ℂ) ^ (-bilinear D left right).toNat := by
  let gram := bilinear D left right
  let negative := (-gram).toNat
  let positive := gram.toNat
  have positiveShift : (negative : ℤ) + gram = positive := by
    dsimp [negative, positive]
    omega
  have negativeShift : (positive : ℤ) + -gram = negative := by
    dsimp [negative, positive]
    omega
  have first : (1 - PowerSeries.X : PowerSeries ℂ) ^ negative *
      PowerSeries.rescale (-1 : ℂ) (PowerSeries.binomialSeries ℂ gram) =
        (1 - PowerSeries.X : PowerSeries ℂ) ^ positive := by
    calc
      _ = PowerSeries.rescale (-1 : ℂ)
          ((1 + PowerSeries.X : PowerSeries ℂ) ^ negative *
            PowerSeries.binomialSeries ℂ gram) := by
        rw [map_mul, rescale_positive]
      _ = PowerSeries.rescale (-1 : ℂ)
          (PowerSeries.binomialSeries ℂ (positive : ℤ)) := by
        rw [binomial_shift, positiveShift]
      _ = _ := by rw [PowerSeries.binomialSeries_nat, rescale_positive]
  have second : (1 + PowerSeries.X : PowerSeries ℂ) ^ positive *
      PowerSeries.binomialSeries ℂ (-gram) =
        (1 + PowerSeries.X : PowerSeries ℂ) ^ negative := by
    rw [binomial_shift, negativeShift, PowerSeries.binomialSeries_nat]
  change (1 - PowerSeries.X : PowerSeries ℂ) ^ negative *
      (1 + PowerSeries.X : PowerSeries ℂ) ^ positive *
      (PowerSeries.rescale (-1 : ℂ) (PowerSeries.binomialSeries ℂ gram) *
        PowerSeries.binomialSeries ℂ (-gram)) = _
  calc
    _ = ((1 - PowerSeries.X : PowerSeries ℂ) ^ negative *
        PowerSeries.rescale (-1 : ℂ) (PowerSeries.binomialSeries ℂ gram)) *
        ((1 + PowerSeries.X : PowerSeries ℂ) ^ positive *
          PowerSeries.binomialSeries ℂ (-gram)) := by ring
    _ = _ := by rw [first, second]

def clearedPolynomial (gram : ℤ) : Polynomial ℂ :=
  (1 - Polynomial.X) ^ (2 * gram.toNat) *
    (1 + Polynomial.X) ^ (2 * (-gram).toNat)

private theorem physical_factorization (gram : ℤ) :
    (1 - PowerSeries.X ^ 2 : PowerSeries ℂ) ^ gram.natAbs =
      ((1 - PowerSeries.X : PowerSeries ℂ) ^ gram.toNat *
        (1 + PowerSeries.X : PowerSeries ℂ) ^ (-gram).toNat) *
      ((1 - PowerSeries.X : PowerSeries ℂ) ^ (-gram).toNat *
        (1 + PowerSeries.X : PowerSeries ℂ) ^ gram.toNat) := by
  have size : gram.natAbs = (-gram).toNat + gram.toNat := by
    rw [Nat.add_comm, Int.toNat_add_toNat_neg_eq_natAbs]
  have factor : (1 - PowerSeries.X ^ 2 : PowerSeries ℂ) =
      (1 - PowerSeries.X) * (1 + PowerSeries.X) := by ring
  have regroup : (1 - PowerSeries.X : PowerSeries ℂ) ^ ((-gram).toNat + gram.toNat) *
      (1 + PowerSeries.X : PowerSeries ℂ) ^ ((-gram).toNat + gram.toNat) =
      ((1 - PowerSeries.X : PowerSeries ℂ) ^ gram.toNat *
        (1 + PowerSeries.X : PowerSeries ℂ) ^ (-gram).toNat) *
      ((1 - PowerSeries.X : PowerSeries ℂ) ^ (-gram).toNat *
        (1 + PowerSeries.X : PowerSeries ℂ) ^ gram.toNat) := by
    rw [pow_add, pow_add]
    ring
  rw [size, factor, mul_pow, regroup]

private theorem cleared_square (gram : ℤ) :
    ((1 - PowerSeries.X : PowerSeries ℂ) ^ gram.toNat *
      (1 + PowerSeries.X : PowerSeries ℂ) ^ (-gram).toNat) *
      ((1 - PowerSeries.X : PowerSeries ℂ) ^ gram.toNat *
        (1 + PowerSeries.X : PowerSeries ℂ) ^ (-gram).toNat) =
      (clearedPolynomial gram).toPowerSeries := by
  simp only [clearedPolynomial, Polynomial.coe_mul, Polynomial.coe_pow,
    Polynomial.coe_sub, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X]
  simp only [two_mul, pow_add]
  ring

theorem half_contraction_physical_clearing (D : LatticeData) (left right : Charge D) :
    (1 - PowerSeries.X ^ 2 : PowerSeries ℂ) ^ (bilinear D left right).natAbs *
      halfContraction D left right =
        (clearedPolynomial (bilinear D left right)).toPowerSeries := by
  rw [physical_factorization, mul_assoc, half_contraction_two_branch_clearing,
    cleared_square]

private theorem linear_power_degree (polynomial : Polynomial ℂ)
    (bound : polynomial.natDegree ≤ 1) (degree : ℕ) :
    (polynomial ^ degree).natDegree ≤ degree := by
  simpa using Polynomial.natDegree_pow_le_of_le degree bound

private theorem reflect_linear_power (polynomial : Polynomial ℂ)
    (bound : polynomial.natDegree ≤ 1) (degree : ℕ) :
    (polynomial ^ degree).reflect degree = (polynomial.reflect 1) ^ degree := by
  induction degree with
  | zero => simp [Polynomial.reflect_one]
  | succ degree inductionProof =>
    rw [pow_succ, Polynomial.reflect_mul _ _ (linear_power_degree polynomial bound degree) bound,
      inductionProof, pow_succ]

private theorem negative_linear_degree : (1 - Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
  simpa using Polynomial.natDegree_sub_le (1 : Polynomial ℂ) Polynomial.X

private theorem positive_linear_degree : (1 + Polynomial.X : Polynomial ℂ).natDegree ≤ 1 := by
  simpa using Polynomial.natDegree_add_le (1 : Polynomial ℂ) Polynomial.X

theorem cleared_polynomial_degree (gram : ℤ) :
    (clearedPolynomial gram).natDegree ≤ 2 * gram.natAbs := by
  have bound := Polynomial.natDegree_mul_le_of_le
    (linear_power_degree (1 - Polynomial.X) negative_linear_degree (2 * gram.toNat))
    (linear_power_degree (1 + Polynomial.X) positive_linear_degree (2 * (-gram).toNat))
  unfold clearedPolynomial
  convert bound using 1
  rw [← Nat.mul_add, Int.toNat_add_toNat_neg_eq_natAbs]

theorem cleared_polynomial_reciprocity (gram : ℤ) :
    (clearedPolynomial gram).reflect (2 * gram.natAbs) = clearedPolynomial gram := by
  have size : 2 * gram.natAbs = 2 * gram.toNat + 2 * (-gram).toNat := by
    rw [← Nat.mul_add, Int.toNat_add_toNat_neg_eq_natAbs]
  have negativeReflection : (1 - Polynomial.X : Polynomial ℂ).reflect 1 =
      -(1 - Polynomial.X) := by
    rw [Polynomial.reflect_sub, Polynomial.reflect_one, Polynomial.reflect_one_X]
    simp
  have positiveReflection : (1 + Polynomial.X : Polynomial ℂ).reflect 1 =
      1 + Polynomial.X := by
    rw [Polynomial.reflect_add, Polynomial.reflect_one, Polynomial.reflect_one_X]
    simp [add_comm]
  rw [clearedPolynomial, size,
    Polynomial.reflect_mul _ _
      (linear_power_degree (1 - Polynomial.X) negative_linear_degree (2 * gram.toNat))
      (linear_power_degree (1 + Polynomial.X) positive_linear_degree (2 * (-gram).toNat)),
    reflect_linear_power _ negative_linear_degree,
    reflect_linear_power _ positive_linear_degree, negativeReflection, positiveReflection,
    (even_two_mul gram.toNat).neg_pow]

theorem cleared_polynomial_coefficient_reciprocity (gram : ℤ) (degree : ℕ)
    (bound : degree ≤ 2 * gram.natAbs) :
    (clearedPolynomial gram).coeff (2 * gram.natAbs - degree) =
      (clearedPolynomial gram).coeff degree := by
  have equality := congrArg (fun polynomial : Polynomial ℂ => polynomial.coeff degree)
    (cleared_polynomial_reciprocity gram)
  rw [Polynomial.coeff_reflect, Polynomial.revAt_le bound] at equality
  exact equality

theorem physical_clearing_sign (gram : ℤ) : (-1 : ℂ) ^ gram.natAbs = paritySign gram := by
  simp only [neg_one_pow_eq_ite, Int.natAbs_even, paritySign]

end
end D5.S3.VertexAlgebra.LatticeHalfFockBranchClearing
