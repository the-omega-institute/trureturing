/- GID: D5/S3/Quantum/Tomography/MUBCompletionRelativeGramEquivalence
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionRelativeGramEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-edge mutually unbiased double completion is exactly equivalent to one flat relative Gram whose two rationally recovered factors are complex Hadamards. -/

import D5.S3.Quantum.Tomography.MUBCompletionSingleRelativeGram

/- Library-search audit trail (2026-09-03):
   * Reuses the unique relative-Gram recovery theorem from
     `MUBCompletionGluing` and the two-sided Hadamard laws from
     `ComplexHadamardTwoSided`.
   * Reuses `factorizedCube_crossGram_apply`; the cube cross-Gram expansion is
     not repeated.
   * The only new content is the converse gluing direction and the resulting
     exact feasibility equivalence.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCubeCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionGluing
open D5.S3.Quantum.Tomography.ComplexHadamardTwoSided

/-- Entrywise conjugation, kept as a transparent abbreviation instead of a
second matrix operation. -/
abbrev entrywiseConj {m n : Type*} (P : Matrix m n ℂ) : Matrix m n ℂ :=
  fun i j ↦ star (P i j)

/-- Rational recovery of the first factor from a relative Gram. -/
abbrev recoverFirst
    {n : Type*} [Fintype n]
    (X P : ComplexSquare n) : ComplexSquare n :=
  ((Fintype.card n : ℂ)⁻¹) • (X * P)

/-- Rational recovery of the conjugate-coupled second factor. -/
abbrev recoverSecond
    {n : Type*} [Fintype n]
    (Y P : ComplexSquare n) : ComplexSquare n :=
  ((Fintype.card n : ℂ)⁻¹) • (Y * entrywiseConj P)

private theorem mul_star_eq_card_of_normSq
    {z : ℂ} {d : ℕ}
    (hz : Complex.normSq z = (d : ℝ)) :
    z * star z = (d : ℂ) := by
  have h := congrArg (fun a : ℝ ↦ (a : ℂ)) hz
  simpa [Complex.star_def, Complex.normSq_eq_conj_mul_self, mul_comm] using h

/-- A flat relative Gram whose two rationally recovered factors are complex
Hadamards reconstructs a mutually unbiased double completion over the fixed
factorized face. -/
theorem oneRelativeGram_reconstructs_doubleCompletion
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H X Y P : ComplexSquare n)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y)
    (hPflat : ∀ i j,
      Complex.normSq (P i j) = (Fintype.card n : ℝ))
    (hRecoverX : IsComplexHadamard (recoverFirst X P))
    (hRecoverY : IsComplexHadamard (recoverSecond Y P)) :
    IsComplexHadamard (recoverFirst X P) ∧
    IsComplexHadamard (recoverSecond Y P) ∧
    HadamardUnbiased X (recoverFirst X P) ∧
    (factorizedCubeMatrix H X Y)ᴴ *
        factorizedCubeMatrix H (recoverFirst X P) (recoverSecond Y P) =
      fun _ _ ↦ (Fintype.card n : ℂ) := by
  have hGramX : Xᴴ * recoverFirst X P = P :=
    relativeGram_of_recovered_factor X P hX
  have hGramY : Yᴴ * recoverSecond Y P = entrywiseConj P :=
    relativeGram_of_recovered_factor Y (entrywiseConj P) hY
  refine ⟨hRecoverX, hRecoverY, ?_, ?_⟩
  · intro i j
    rw [hGramX]
    exact hPflat i j
  · ext k l
    rw [factorizedCube_crossGram_apply H X (recoverFirst X P)
      Y (recoverSecond Y P) hH k l]
    rw [hGramX, hGramY]
    exact mul_star_eq_card_of_normSq (hPflat k l)

/-- Exact fixed-edge reduction. Existence of two Hadamard completion factors
whose cube slices are mutually unbiased is equivalent to existence of one
entrywise-flat relative Gram `P` for which the two rational recovery formulas
again produce complex Hadamards.

This theorem removes an entire matrix pair from the feasibility problem. -/
theorem doubleCompletion_iff_oneRelativeGram
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H X Y : ComplexSquare n)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y) :
    (∃ X' Y' : ComplexSquare n,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' =
        fun _ _ ↦ (Fintype.card n : ℂ)) ↔
    ∃ P : ComplexSquare n,
      (∀ i j,
        Complex.normSq (P i j) = (Fintype.card n : ℝ)) ∧
      IsComplexHadamard (recoverFirst X P) ∧
      IsComplexHadamard (recoverSecond Y P) := by
  constructor
  · rintro ⟨X', Y', hX', hY', hXX', hCross⟩
    let P : ComplexSquare n := Xᴴ * X'
    have hDetermined :=
      second_completion_determined_by_one_relativeGram
        H X X' Y Y' hH hX hY hXX' hCross
    refine ⟨P, ?_, ?_, ?_⟩
    · exact hXX'
    · simpa [P, recoverFirst] using hDetermined.2.1 ▸ hX'
    · simpa [P, recoverSecond, entrywiseConj] using hDetermined.2.2 ▸ hY'
  · rintro ⟨P, hPflat, hRecoverX, hRecoverY⟩
    have hReconstruct :=
      oneRelativeGram_reconstructs_doubleCompletion
        H X Y P hH hX hY hPflat hRecoverX hRecoverY
    exact ⟨recoverFirst X P, recoverSecond Y P,
      hReconstruct.1, hReconstruct.2.1,
      hReconstruct.2.2.1, hReconstruct.2.2.2⟩

/-- Dimension-six specialization of the exact one-relative-Gram reduction. -/
theorem doubleCompletion_iff_oneRelativeGram_six
    (H X Y : Mat6)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y) :
    (∃ X' Y' : Mat6,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' = fun _ _ ↦ (6 : ℂ)) ↔
    ∃ P : Mat6,
      (∀ i j, Complex.normSq (P i j) = 6) ∧
      IsComplexHadamard (recoverFirst X P) ∧
      IsComplexHadamard (recoverSecond Y P) := by
  simpa using doubleCompletion_iff_oneRelativeGram H X Y hH hX hY

#print axioms oneRelativeGram_reconstructs_doubleCompletion
#print axioms doubleCompletion_iff_oneRelativeGram
#print axioms doubleCompletion_iff_oneRelativeGram_six

end D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence
