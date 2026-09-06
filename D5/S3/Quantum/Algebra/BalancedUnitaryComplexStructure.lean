/- GID: D5/S3/Quantum/Algebra/BalancedUnitaryComplexStructure
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/BalancedUnitaryComplexStructure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Two-sided half-unitary summands with cancelling cross terms produce a unitary skew-adjoint relative product whose square is minus identity. -/

import D5.S3.Quantum.Algebra.BalancedUnitarySum

open scoped Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.BalancedUnitaryComplexStructure

open Matrix
open D5.S3.Quantum.Algebra.BalancedUnitarySum

/-- Twice the relative mixed product of two balanced summands. -/
def relativeComplexStructure
    {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ) • (A * Bᴴ)

/-- Cross cancellation makes the relative product skew-adjoint. -/
theorem relativeComplexStructure_is_skewAdjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hCross : A * Bᴴ + B * Aᴴ = 0) :
    (relativeComplexStructure A B)ᴴ =
      -(relativeComplexStructure A B) := by
  unfold relativeComplexStructure
  rw [Matrix.conjTranspose_smul]
  simp only [map_ofNat]
  rw [crossProduct_is_skewAdjoint A B hCross]
  simp

/-- Right unitarity of the relative product follows from right normalization of
`A` and left normalization of `B`. -/
theorem relativeComplexStructure_mul_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hA : A * Aᴴ = halfIdentity)
    (hB : Bᴴ * B = halfIdentity) :
    relativeComplexStructure A B *
        (relativeComplexStructure A B)ᴴ =
      (1 : Matrix n n ℂ) := by
  simp [relativeComplexStructure, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, hA, hB, halfIdentity]

/-- Left unitarity follows from left normalization of `A` and right
normalization of `B`. -/
theorem relativeComplexStructure_conjTranspose_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hA : Aᴴ * A = halfIdentity)
    (hB : B * Bᴴ = halfIdentity) :
    (relativeComplexStructure A B)ᴴ *
        relativeComplexStructure A B =
      (1 : Matrix n n ℂ) := by
  simp [relativeComplexStructure, Matrix.conjTranspose_mul,
    Matrix.mul_assoc, hA, hB, halfIdentity]

/-- A unitary skew-adjoint matrix squares to minus identity. -/
theorem square_eq_neg_one_of_skewAdjoint_unitary
    {n : Type*} [Fintype n] [DecidableEq n]
    (R : Matrix n n ℂ)
    (hSkew : Rᴴ = -R)
    (hUnitary : R * Rᴴ = (1 : Matrix n n ℂ)) :
    R * R = -(1 : Matrix n n ℂ) := by
  have hneg : -(R * R) = (1 : Matrix n n ℂ) := by
    calc
      -(R * R) = R * (-R) := by simp
      _ = R * Rᴴ := by rw [hSkew]
      _ = 1 := hUnitary
  have h := congrArg Neg.neg hneg
  simpa using h

/-- The balanced relative product is a genuine complex structure. -/
theorem relativeComplexStructure_square
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hCross : A * Bᴴ + B * Aᴴ = 0)
    (hA : A * Aᴴ = halfIdentity)
    (hB : Bᴴ * B = halfIdentity) :
    relativeComplexStructure A B * relativeComplexStructure A B =
      -(1 : Matrix n n ℂ) := by
  exact square_eq_neg_one_of_skewAdjoint_unitary
    (relativeComplexStructure A B)
    (relativeComplexStructure_is_skewAdjoint A B hCross)
    (relativeComplexStructure_mul_conjTranspose A B hA hB)

/-- Multiplication by `i` turns a skew-adjoint complex structure into a
Hermitian involution. -/
def relativeInvolution
    {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  Complex.I • relativeComplexStructure A B

/-- The induced involution is Hermitian. -/
theorem relativeInvolution_isHermitian
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hCross : A * Bᴴ + B * Aᴴ = 0) :
    (relativeInvolution A B)ᴴ = relativeInvolution A B := by
  unfold relativeInvolution
  rw [Matrix.conjTranspose_smul]
  rw [relativeComplexStructure_is_skewAdjoint A B hCross]
  simp [Complex.star_def]

/-- The induced Hermitian matrix squares to identity. -/
theorem relativeInvolution_square
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hCross : A * Bᴴ + B * Aᴴ = 0)
    (hA : A * Aᴴ = halfIdentity)
    (hB : Bᴴ * B = halfIdentity) :
    relativeInvolution A B * relativeInvolution A B =
      (1 : Matrix n n ℂ) := by
  simp [relativeInvolution, Matrix.mul_smul, Matrix.smul_mul,
    relativeComplexStructure_square A B hCross hA hB]

#print axioms relativeComplexStructure_is_skewAdjoint
#print axioms relativeComplexStructure_mul_conjTranspose
#print axioms relativeComplexStructure_conjTranspose_mul
#print axioms square_eq_neg_one_of_skewAdjoint_unitary
#print axioms relativeComplexStructure_square
#print axioms relativeInvolution_isHermitian
#print axioms relativeInvolution_square

end D5.S3.Quantum.Algebra.BalancedUnitaryComplexStructure
