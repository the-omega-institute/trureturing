/- GID: D5/S3/Quantum/Tomography/MUBCompletionScalarDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionScalarDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Fixed-edge double completion is equivalent to one flat relative Gram, two row-Gram equations, and two scalar entrywise defects. -/

import D5.S3.Quantum.Tomography.ComplexHadamardEntrywiseDefect

/- Library-search audit trail (2026-09-03):
   * This is a corollary layer over the exact relative-Gram equivalence and the
     generic scalar-defect theorem.
   * No new feasibility predicate or objective function is introduced; the
     certificate equations remain visible in the theorem statement.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionScalarDefect

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCubeCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence
open D5.S3.Quantum.Tomography.ComplexHadamardEntrywiseDefect

/-- Exact scalar-defect form of fixed-edge double-completion feasibility.

The many entrywise equations for the two recovered factors are compressed to
two nonnegative scalar sums. Their row-Gram equations remain explicit and can
later be discharged from the scaled-Hadamard law of the relative Gram. -/
theorem doubleCompletion_iff_oneRelativeGram_twoScalarDefects
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
      (∑ i, ∑ j,
        (Complex.normSq ((recoverFirst X P) i j) - 1) ^ 2 = 0) ∧
      recoverFirst X P * (recoverFirst X P)ᴴ =
        (Fintype.card n : ℂ) • (1 : ComplexSquare n) ∧
      (∑ i, ∑ j,
        (Complex.normSq ((recoverSecond Y P) i j) - 1) ^ 2 = 0) ∧
      recoverSecond Y P * (recoverSecond Y P)ᴴ =
        (Fintype.card n : ℂ) • (1 : ComplexSquare n) := by
  rw [doubleCompletion_iff_oneRelativeGram H X Y hH hX hY]
  constructor
  · rintro ⟨P, hP, hRecoverX, hRecoverY⟩
    have hXScalar :=
      (isComplexHadamard_iff_scalarDefect_and_rowGram
        (recoverFirst X P)).mp hRecoverX
    have hYScalar :=
      (isComplexHadamard_iff_scalarDefect_and_rowGram
        (recoverSecond Y P)).mp hRecoverY
    exact ⟨P, hP, hXScalar.1, hXScalar.2,
      hYScalar.1, hYScalar.2⟩
  · rintro ⟨P, hP, hXDefect, hXGram, hYDefect, hYGram⟩
    refine ⟨P, hP, ?_, ?_⟩
    · exact
        (isComplexHadamard_iff_scalarDefect_and_rowGram
          (recoverFirst X P)).mpr ⟨hXDefect, hXGram⟩
    · exact
        (isComplexHadamard_iff_scalarDefect_and_rowGram
          (recoverSecond Y P)).mpr ⟨hYDefect, hYGram⟩

/-- Dimension-six scalar-defect specialization. -/
theorem doubleCompletion_iff_oneRelativeGram_twoScalarDefects_six
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
      (∑ i, ∑ j,
        (Complex.normSq ((recoverFirst X P) i j) - 1) ^ 2 = 0) ∧
      recoverFirst X P * (recoverFirst X P)ᴴ =
        (6 : ℂ) • (1 : Mat6) ∧
      (∑ i, ∑ j,
        (Complex.normSq ((recoverSecond Y P) i j) - 1) ^ 2 = 0) ∧
      recoverSecond Y P * (recoverSecond Y P)ᴴ =
        (6 : ℂ) • (1 : Mat6) := by
  simpa using
    doubleCompletion_iff_oneRelativeGram_twoScalarDefects
      H X Y hH hX hY

#print axioms doubleCompletion_iff_oneRelativeGram_twoScalarDefects
#print axioms doubleCompletion_iff_oneRelativeGram_twoScalarDefects_six

end D5.S3.Quantum.Tomography.MUBCompletionScalarDefect
