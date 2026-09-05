/- GID: D5/S3/Quantum/Tomography/MUBCompletionRecoveredRowGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionRecoveredRowGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A scaled-Hadamard relative Gram automatically supplies the row-Gram equations of both rationally recovered completion factors. -/

import D5.S3.Quantum.Tomography.MUBCompletionScalarDefect

/- Library-search audit trail (2026-09-03):
   * Reuses the existing Hadamard row Gram, `entrywiseConj`, and rational
     recovery definitions.
   * Matrix associativity, conjugate transpose, scalar multiplication, and the
     finite-cardinality nonzero fact are reused from Mathlib.
   * No second unitarity or scaled-Hadamard structure is introduced.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionRecoveredRowGram

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence
open D5.S3.Quantum.Tomography.MUBCompletionScalarDefect
open D5.S3.Quantum.Tomography.ComplexHadamardEntrywiseDefect
open D5.S3.Quantum.Tomography.ComplexHadamardTwoSided

private theorem card_cast_ne_zero
    {n : Type*} [Fintype n] [Nonempty n] :
    (Fintype.card n : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (Fintype.card_pos : 0 < Fintype.card n))

/-- The entrywise conjugate of a matrix with scalar row Gram has the same row
Gram when the scalar is the real finite-cardinality square. -/
theorem entrywiseConj_preserves_cardSq_rowGram
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : ComplexSquare n)
    (hP : P * Pᴴ =
      ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n)) :
    entrywiseConj P * (entrywiseConj P)ᴴ =
      ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n) := by
  ext i j
  have hEntry := congrFun (congrFun hP j) i
  simpa [entrywiseConj, Matrix.mul_apply,
    Matrix.conjTranspose_apply, mul_comm, eq_comm] using hEntry

/-- If `X` has row Gram `d I` and `P` has row Gram `d^2 I`, then the rational
recovery `d⁻¹ X P` again has row Gram `d I`. -/
theorem recoverFirst_rowGram
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (X P : ComplexSquare n)
    (hX : IsComplexHadamard X)
    (hP : P * Pᴴ =
      ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n)) :
    recoverFirst X P * (recoverFirst X P)ᴴ =
      (Fintype.card n : ℂ) • (1 : ComplexSquare n) := by
  let d : ℂ := Fintype.card n
  have hd : d ≠ 0 := card_cast_ne_zero
  simp [recoverFirst, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_mul, Matrix.mul_assoc,
    hP, hX.2, smul_smul, d, hd]

/-- The conjugate-coupled rational recovery has the same automatic row Gram. -/
theorem recoverSecond_rowGram
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (Y P : ComplexSquare n)
    (hY : IsComplexHadamard Y)
    (hP : P * Pᴴ =
      ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n)) :
    recoverSecond Y P * (recoverSecond Y P)ᴴ =
      (Fintype.card n : ℂ) • (1 : ComplexSquare n) := by
  have hConj := entrywiseConj_preserves_cardSq_rowGram P hP
  simpa [recoverSecond, recoverFirst] using
    recoverFirst_rowGram Y (entrywiseConj P) hY hConj

/-- Final exact polynomial form of fixed-edge double completion.

Only one matrix `P` remains. Its entries have squared modulus `d`, its row Gram
is `d^2 I`, and two scalar sums of squares enforce entrywise flatness of the
recovered factors. Their row-Gram equations follow automatically from the
first two conditions. -/
theorem doubleCompletion_iff_scaledRelativeGram_and_twoDefects
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H X Y : ComplexSquare n)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y) :
    (∃ X' Y' : ComplexSquare n,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (D5.S3.Quantum.Tomography.MUBCubeCompatibility.factorizedCubeMatrix
          H X Y)ᴴ *
          D5.S3.Quantum.Tomography.MUBCubeCompatibility.factorizedCubeMatrix
            H X' Y' =
        fun _ _ ↦ (Fintype.card n : ℂ)) ↔
    ∃ P : ComplexSquare n,
      (∀ i j,
        Complex.normSq (P i j) = (Fintype.card n : ℝ)) ∧
      P * Pᴴ =
        ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
          (1 : ComplexSquare n) ∧
      (∑ i, ∑ j,
        (Complex.normSq ((recoverFirst X P) i j) - 1) ^ 2 = 0) ∧
      (∑ i, ∑ j,
        (Complex.normSq ((recoverSecond Y P) i j) - 1) ^ 2 = 0) := by
  rw [D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence.doubleCompletion_iff_oneRelativeGram
    H X Y hH hX hY]
  constructor
  · rintro ⟨P, hPflat, hRecoverX, hRecoverY⟩
    have hPGram :=
      relativeGram_mul_conjTranspose_eq_card_sq_smul
        X (recoverFirst X P) hX hRecoverX
    have hRelative : Xᴴ * recoverFirst X P = P :=
      relativeGram_of_recovered_factor X P hX
    rw [hRelative] at hPGram
    exact ⟨P, hPflat, hPGram,
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverFirst X P)).mp hRecoverX.1,
      (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
        (recoverSecond Y P)).mp hRecoverY.1⟩
  · rintro ⟨P, hPflat, hPGram, hXDefect, hYDefect⟩
    refine ⟨P, hPflat, ?_, ?_⟩
    · exact ⟨
        (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
          (recoverFirst X P)).mpr hXDefect,
        recoverFirst_rowGram X P hX hPGram⟩
    · exact ⟨
        (entrywiseUnit_iff_sum_normSq_sub_one_sq_eq_zero
          (recoverSecond Y P)).mpr hYDefect,
        recoverSecond_rowGram Y P hY hPGram⟩

/-- Dimension-six final polynomial specialization. -/
theorem doubleCompletion_iff_scaledRelativeGram_and_twoDefects_six
    (H X Y : Mat6)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y) :
    (∃ X' Y' : Mat6,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (D5.S3.Quantum.Tomography.MUBCubeCompatibility.factorizedCubeMatrix
          H X Y)ᴴ *
          D5.S3.Quantum.Tomography.MUBCubeCompatibility.factorizedCubeMatrix
            H X' Y' = fun _ _ ↦ (6 : ℂ)) ↔
    ∃ P : Mat6,
      (∀ i j, Complex.normSq (P i j) = 6) ∧
      P * Pᴴ = (36 : ℂ) • (1 : Mat6) ∧
      (∑ i, ∑ j,
        (Complex.normSq ((recoverFirst X P) i j) - 1) ^ 2 = 0) ∧
      (∑ i, ∑ j,
        (Complex.normSq ((recoverSecond Y P) i j) - 1) ^ 2 = 0) := by
  simpa using
    doubleCompletion_iff_scaledRelativeGram_and_twoDefects
      H X Y hH hX hY

#print axioms entrywiseConj_preserves_cardSq_rowGram
#print axioms recoverFirst_rowGram
#print axioms recoverSecond_rowGram
#print axioms doubleCompletion_iff_scaledRelativeGram_and_twoDefects
#print axioms doubleCompletion_iff_scaledRelativeGram_and_twoDefects_six

end D5.S3.Quantum.Tomography.MUBCompletionRecoveredRowGram
