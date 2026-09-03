/- GID: D5/S3/Quantum/Algebra/FlatPhaseConjugation
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/FlatPhaseConjugation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Conjugating a zero-sum diagonal phase profile through an entrywise-unit matrix gives a matrix with zero diagonal after normalized flat averaging. -/

import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Algebra.FlatPhaseConjugation

/-- The normalized kernel of `diag(c) H diag(star d) Hᴴ`, written entrywise so
that the flat-diagonal cancellation can be consumed without a separate diagonal
matrix API. -/
def flatPhaseConjugation
    {ι κ : Type*} [Fintype κ]
    (H : Matrix ι κ ℂ) (c : ι → ℂ) (d : κ → ℂ) : Matrix ι ι ℂ :=
  fun i l ↦
    (Fintype.card κ : ℂ)⁻¹ * c i *
      ∑ j, H i j * star (d j) * star (H l j)

private theorem mul_star_self_of_normSq_one
    {z : ℂ} (hz : Complex.normSq z = 1) :
    z * star z = 1 := by
  have h : star z * z = 1 := by
    simpa [Complex.star_def, Complex.normSq_eq_conj_mul_self] using
      congrArg (fun a : ℝ ↦ (a : ℂ)) hz
  simpa [mul_comm] using h

/-- Entrywise unit modulus removes the Hadamard row from a diagonal entry. -/
theorem flatPhaseConjugation_diagonal
    {ι κ : Type*} [Fintype κ]
    (H : Matrix ι κ ℂ) (c : ι → ℂ) (d : κ → ℂ)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (i : ι) :
    flatPhaseConjugation H c d i i =
      (Fintype.card κ : ℂ)⁻¹ * c i * ∑ j, star (d j) := by
  unfold flatPhaseConjugation
  congr 2
  apply Finset.sum_congr rfl
  intro j hj
  calc
    H i j * star (d j) * star (H i j) =
        star (d j) * (H i j * star (H i j)) := by ring
    _ = star (d j) := by
      rw [mul_star_self_of_normSq_one (hH i j)]
      simp

/-- A zero-sum phase profile has zero diagonal after flat conjugation. -/
theorem flatPhaseConjugation_diagonal_zero
    {ι κ : Type*} [Fintype κ]
    (H : Matrix ι κ ℂ) (c : ι → ℂ) (d : κ → ℂ)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (hd : ∑ j, d j = 0)
    (i : ι) :
    flatPhaseConjugation H c d i i = 0 := by
  rw [flatPhaseConjugation_diagonal H c d hH i]
  have hstar : ∑ j, star (d j) = 0 := by
    simpa using congrArg star hd
  rw [hstar]
  simp

/-- The entire diagonal vanishes pointwise. -/
theorem flatPhaseConjugation_zero_diagonal
    {ι κ : Type*} [Fintype κ]
    (H : Matrix ι κ ℂ) (c : ι → ℂ) (d : κ → ℂ)
    (hH : ∀ i j, Complex.normSq (H i j) = 1)
    (hd : ∑ j, d j = 0) :
    ∀ i, flatPhaseConjugation H c d i i = 0 := by
  intro i
  exact flatPhaseConjugation_diagonal_zero H c d hH hd i

#print axioms flatPhaseConjugation_diagonal
#print axioms flatPhaseConjugation_diagonal_zero
#print axioms flatPhaseConjugation_zero_diagonal

end D5.S3.Quantum.Algebra.FlatPhaseConjugation
