/- GID: D5/S3/Weil/FiniteSpectralCayleyIdentity
   generality: G
   mirror-B: D5/B/S3/Weil/FiniteSpectralCayleyIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite real spectra obey the Li-Cayley norm and diagonal determinant identities. -/

import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/- Library-search audit trail (2026-09-02):
   * Six-route searches covered automorphic Li coefficients, Cayley nodes, Hilbert-
     Schmidt defects, diagonal spectral determinants, digestion receipts, theorem-
     body generalizations, and every in-flight lane. Existing D5 Cayley results
     characterize critical-line unitarity or phase limits; Li-Caratheodory modules
     and positive Fredholm products do not contain the finite identities below.
   * Pinned Mathlib supplies `Complex.normSq_sub`, `Real.sq_sqrt`, `map_pow`,
     `Matrix.det_diagonal`, and the diagonal add/smul laws. They are used directly.
   * General automorphic GRH, infinite Hilbert-Schmidt operators, and Fredholm
     determinants are not formalized here. The source claim is corrected to a finite
     real spectral family, where every denominator and square root is justified. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.FiniteSpectralCayleyIdentity

/-- The folded spectral coordinate attached to a real ordinate. -/
noncomputable def spectralWeight (gamma : Real) : Real :=
  1 / (4 * gamma ^ 2 + 1)

/-- The finite-spectrum Cayley node associated with a real ordinate. -/
noncomputable def cayleyNode (gamma : Real) : Complex :=
  let x := spectralWeight gamma
  (1 - 2 * x : Real) + (2 * Real.sqrt (x * (1 - x))) * Complex.I

theorem spectralWeight_pos (gamma : Real) : 0 < spectralWeight gamma := by
  unfold spectralWeight
  positivity

theorem spectralWeight_le_one (gamma : Real) : spectralWeight gamma <= 1 := by
  unfold spectralWeight
  apply (div_le_iff₀ (by positivity : 0 < 4 * gamma ^ 2 + 1)).2
  nlinarith [sq_nonneg gamma]

private theorem spectralRadicand_nonneg (gamma : Real) :
    0 <= spectralWeight gamma * (1 - spectralWeight gamma) :=
  mul_nonneg (spectralWeight_pos gamma).le
    (sub_nonneg.mpr (spectralWeight_le_one gamma))

/-- Every real spectral ordinate produces a unit-circle Cayley node. -/
theorem cayleyNode_normSq (gamma : Real) :
    Complex.normSq (cayleyNode gamma) = 1 := by
  let x := spectralWeight gamma
  have hx : 0 <= x * (1 - x) := spectralRadicand_nonneg gamma
  rw [Complex.normSq_apply]
  simp [cayleyNode]
  nlinarith [Real.sq_sqrt hx]

/-- At the first Li index, the squared defect is four times the folded weight. -/
theorem cayleyNode_one_sub_normSq (gamma : Real) :
    Complex.normSq (1 - cayleyNode gamma) = 4 * spectralWeight gamma := by
  let x := spectralWeight gamma
  have hx : 0 <= x * (1 - x) := spectralRadicand_nonneg gamma
  rw [Complex.normSq_apply]
  simp [cayleyNode]
  nlinarith [Real.sq_sqrt hx]

/-- The finite Li expression written through real parts of powers. -/
noncomputable def finiteLiCoefficient {J : Type*} [Fintype J]
    (gamma : J -> Real) (n : Nat) : Real :=
  ∑ j, 2 * (1 - (cayleyNode (gamma j) ^ n).re)

/-- The Hilbert-Schmidt squared norm of the diagonal Cayley defect. -/
noncomputable def diagonalHilbertSchmidtDefect {J : Type*} [Fintype J]
    (gamma : J -> Real) (n : Nat) : Real :=
  ∑ j, Complex.normSq (1 - cayleyNode (gamma j) ^ n)

/-- For every power, the finite Li coefficient is exactly the diagonal
Hilbert-Schmidt defect squared. -/
theorem finiteLiCoefficient_eq_diagonalHilbertSchmidtDefect
    {J : Type*} [Fintype J] (gamma : J -> Real) (n : Nat) :
    finiteLiCoefficient gamma n = diagonalHilbertSchmidtDefect gamma n := by
  classical
  unfold finiteLiCoefficient diagonalHilbertSchmidtDefect
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.normSq_sub]
  have hpower : Complex.normSq (cayleyNode (gamma j) ^ n) = 1 := by
    rw [map_pow, cayleyNode_normSq, one_pow]
  have hconj :
      ((starRingEnd Complex) (cayleyNode (gamma j) ^ n)).re =
        (cayleyNode (gamma j) ^ n).re := by
    rw [starRingEnd_apply, Complex.star_def, Complex.conj_re]
  rw [hpower]
  simp only [map_one, one_mul]
  rw [hconj]
  ring

/-- The first diagonal Hilbert-Schmidt defect is four times the total folded
spectral weight. -/
theorem diagonalHilbertSchmidtDefect_one {J : Type*} [Fintype J]
    (gamma : J -> Real) :
    diagonalHilbertSchmidtDefect gamma 1 = 4 * ∑ j, spectralWeight (gamma j) := by
  classical
  simp [diagonalHilbertSchmidtDefect, cayleyNode_one_sub_normSq,
    Finset.mul_sum]

/-- The finite diagonal determinant is the product of its scalar spectral
factors. This is the finite-dimensional form of the source Fredholm formula. -/
theorem finiteSpectralDeterminant {J : Type*} [Fintype J] [DecidableEq J]
    (gamma : J -> Real) (z : Complex) :
    Matrix.det
        (1 + (4 * z / (1 - z) ^ 2) •
          Matrix.diagonal (fun j => (spectralWeight (gamma j) : Complex))) =
      ∏ j, (1 + (4 * z / (1 - z) ^ 2) * spectralWeight (gamma j)) := by
  rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, Matrix.diagonal_add,
    Matrix.det_diagonal]
  rfl

#print axioms cayleyNode_normSq
#print axioms cayleyNode_one_sub_normSq
#print axioms finiteLiCoefficient_eq_diagonalHilbertSchmidtDefect
#print axioms finiteSpectralDeterminant

end D5.S3.Weil.FiniteSpectralCayleyIdentity
