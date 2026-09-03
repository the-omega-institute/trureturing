/- GID: D5/S3/Quantum/Algebra/BalancedUnitarySum
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/BalancedUnitarySum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: If a unitary matrix is the sum of two half-unitary summands, their cross terms cancel and the relative product is skew-adjoint. -/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

open scoped Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.BalancedUnitarySum

open Matrix

/-- The squared normalization carried by each summand in a balanced unitary
sum. -/
def halfIdentity {n : Type*} [DecidableEq n] : Matrix n n ℂ :=
  (1 / 2 : ℂ) • (1 : Matrix n n ℂ)

/-- If `S = A + B` is unitary and both summands have right Gram matrix
`I / 2`, the mixed Gram terms cancel exactly. -/
theorem crossTerms_eq_zero
    {n : Type*} [Fintype n] [DecidableEq n]
    (S A B : Matrix n n ℂ)
    (hS : S = A + B)
    (hUnitary : S * Sᴴ = (1 : Matrix n n ℂ))
    (hA : A * Aᴴ = halfIdentity)
    (hB : B * Bᴴ = halfIdentity) :
    A * Bᴴ + B * Aᴴ = 0 := by
  subst S
  rw [Matrix.conjTranspose_add] at hUnitary
  calc
    A * Bᴴ + B * Aᴴ =
        (A + B) * (Aᴴ + Bᴴ) - A * Aᴴ - B * Bᴴ := by
          noncomm_ring
    _ = (1 : Matrix n n ℂ) - halfIdentity - halfIdentity := by
      rw [hUnitary, hA, hB]
    _ = 0 := by
      ext i j
      simp [halfIdentity, Matrix.one_apply]

/-- Cross cancellation says that one mixed product is the negative adjoint of
the other. -/
theorem secondCross_eq_neg_first
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hCross : A * Bᴴ + B * Aᴴ = 0) :
    B * Aᴴ = -(A * Bᴴ) := by
  exact eq_neg_of_add_eq_zero_left hCross

/-- The relative cross product of a balanced unitary sum is skew-adjoint. -/
theorem crossProduct_is_skewAdjoint
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ)
    (hCross : A * Bᴴ + B * Aᴴ = 0) :
    (A * Bᴴ)ᴴ = -(A * Bᴴ) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  exact secondCross_eq_neg_first A B hCross

/-- Direct consumer theorem combining balanced normalization with the
skew-adjoint conclusion. -/
theorem crossProduct_is_skewAdjoint_of_balanced_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (S A B : Matrix n n ℂ)
    (hS : S = A + B)
    (hUnitary : S * Sᴴ = (1 : Matrix n n ℂ))
    (hA : A * Aᴴ = halfIdentity)
    (hB : B * Bᴴ = halfIdentity) :
    (A * Bᴴ)ᴴ = -(A * Bᴴ) := by
  exact crossProduct_is_skewAdjoint A B
    (crossTerms_eq_zero S A B hS hUnitary hA hB)

#print axioms crossTerms_eq_zero
#print axioms secondCross_eq_neg_first
#print axioms crossProduct_is_skewAdjoint
#print axioms crossProduct_is_skewAdjoint_of_balanced_sum

end D5.S3.Quantum.Algebra.BalancedUnitarySum
