/- GID: D5/S3/Zeros/SelfWeightedHankelPositivity
   generality: G
   mirror-B: D5/B/S3/Zeros/SelfWeightedHankelPositivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite self-weighted Hankel forms are exact sums of weighted polynomial norm squares. -/

import Mathlib.Analysis.Matrix.PosDef

/- Library-search audit trail (2026-09-02):
   * Six-route searches covered Hankel and Hamburger moment matrices, self-weighted
     nodes, polynomial norm-square energies, digestion receipts, theorem-body
     generalizations, and every in-flight lane. Existing D5 Hankel results concern
     determinant ratios or realization rank; Toeplitz moment criteria and generic
     Gramian energies do not identify the self-weighted Hankel matrix below.
   * Pinned Mathlib supplies `Matrix.posSemidef_vecMulVec_self_star`,
     `Matrix.posSemidef_sum`, and positivity-preserving real scalar multiplication.
     No packaged theorem gives the displayed self-weighted moment identity.
   * The source's RH equivalence requires an unformalized Hamburger representation
     theorem plus analytic continuation. This module records the exact finite
     algebraic implication, with node nonnegativity and strictness made explicit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Zeros.SelfWeightedHankelPositivity

open scoped ComplexConjugate ComplexOrder

/-- The vector of monomials of degree at most `N` at a real node. -/
def monomialVector (N : Nat) (x : Real) : Fin (N + 1) -> ℂ :=
  fun k => (x : ℂ) ^ k.1

/-- Evaluation of the coefficient vector as a polynomial at a real node. -/
def polynomialValue {N : Nat} (c : Fin (N + 1) -> ℂ) (x : Real) : ℂ :=
  ∑ k, c k * monomialVector N x k

/-- The finite self-weighted Hankel matrix. Its node `v r` has weight
`multiplicity r * v r`, as in the centered inverse-zero moment construction. -/
noncomputable def selfWeightedHankel {R : Type*} [Fintype R] [DecidableEq R]
    (N : Nat) (multiplicity node : R -> Real) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  ∑ r, (multiplicity r * node r) •
    Matrix.vecMulVec (monomialVector N (node r))
      (star (monomialVector N (node r)))

/-- The matrix entry is the expected shifted moment
`sum_r multiplicity_r * node_r^(i+j+1)`. -/
theorem selfWeightedHankel_apply {R : Type*} [Fintype R] [DecidableEq R]
    (N : Nat) (multiplicity node : R -> Real) (i j : Fin (N + 1)) :
    selfWeightedHankel N multiplicity node i j =
      ∑ r, ((multiplicity r * node r ^ (i.1 + j.1 + 1) : Real) : ℂ) := by
  classical
  simp only [selfWeightedHankel, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro r _
  simp [monomialVector, Matrix.vecMulVec, pow_add]
  ring

private theorem rankOne_quadraticForm (N : Nat) (x : Real)
    (c : Fin (N + 1) -> ℂ) :
    dotProduct (star c)
        (Matrix.mulVec
          (Matrix.vecMulVec (monomialVector N x) (star (monomialVector N x))) c) =
      Complex.normSq (polynomialValue c x) := by
  have hEval : star (monomialVector N x) ⬝ᵥ c = polynomialValue c x := by
    simp [dotProduct, polynomialValue, monomialVector, Pi.star_apply, mul_comm]
  rw [Matrix.vecMulVec_mulVec]
  simp only [op_smul_eq_smul, dotProduct_smul, smul_eq_mul]
  rw [Matrix.star_dotProduct c (monomialVector N x), hEval]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [starRingEnd_apply]
  ring

/-- The self-weighted Hankel quadratic form is exactly a sum of weighted
polynomial norm squares. -/
theorem selfWeightedHankel_quadraticForm {R : Type*} [Fintype R] [DecidableEq R]
    (N : Nat) (multiplicity node : R -> Real)
    (c : Fin (N + 1) -> ℂ) :
    dotProduct (star c) (Matrix.mulVec (selfWeightedHankel N multiplicity node) c) =
      ∑ r, ((multiplicity r * node r : Real) : ℂ) *
        Complex.normSq (polynomialValue c (node r)) := by
  classical
  unfold selfWeightedHankel
  rw [Matrix.sum_mulVec, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Matrix.smul_mulVec, dotProduct_smul, rankOne_quadraticForm]
  rfl

/-- Nonnegative multiplicities and nodes make every finite self-weighted Hankel
matrix positive semidefinite. -/
theorem selfWeightedHankel_posSemidef {R : Type*} [Fintype R] [DecidableEq R]
    (N : Nat) (multiplicity node : R -> Real)
    (hmultiplicity : forall r, 0 <= multiplicity r)
    (hnode : forall r, 0 <= node r) :
    (selfWeightedHankel N multiplicity node).PosSemidef := by
  unfold selfWeightedHankel
  apply Matrix.posSemidef_sum
  intro r _
  exact (Matrix.posSemidef_vecMulVec_self_star (monomialVector N (node r))).smul
    (mul_nonneg (hmultiplicity r) (hnode r))

/-- Strict positivity for a particular nonzero coefficient vector follows from
one positive-weight node where the associated polynomial does not vanish. -/
theorem selfWeightedHankel_quadraticForm_pos {R : Type*} [Fintype R] [DecidableEq R]
    (N : Nat) (multiplicity node : R -> Real)
    (hmultiplicity : forall r, 0 <= multiplicity r)
    (hnode : forall r, 0 <= node r)
    (c : Fin (N + 1) -> ℂ)
    (r0 : R) (hweight : 0 < multiplicity r0 * node r0)
    (hnonzero : polynomialValue c (node r0) ≠ 0) :
    0 < Complex.re
      (dotProduct (star c) (Matrix.mulVec (selfWeightedHankel N multiplicity node) c)) := by
  rw [selfWeightedHankel_quadraticForm]
  rw [Complex.re_sum]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  apply Finset.sum_pos'
  · intro r _
    exact mul_nonneg (mul_nonneg (hmultiplicity r) (hnode r))
      (Complex.normSq_nonneg _)
  · refine ⟨r0, Finset.mem_univ r0, ?_⟩
    exact mul_pos hweight (Complex.normSq_pos.mpr hnonzero)

#print axioms selfWeightedHankel_quadraticForm
#print axioms selfWeightedHankel_posSemidef
#print axioms selfWeightedHankel_quadraticForm_pos

end D5.S3.Zeros.SelfWeightedHankelPositivity
