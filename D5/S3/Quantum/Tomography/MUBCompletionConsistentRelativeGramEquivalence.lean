/- GID: D5/S3/Quantum/Tomography/MUBCompletionConsistentRelativeGramEquivalence
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionConsistentRelativeGramEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The one-relative-Gram equivalence remains exact after adding the multiplicative transition-consistency equation of a Hadamard-cube completion. -/

import D5.S3.Quantum.Tomography.MUBCompletionConsistencyTransport

/- Library-search audit trail (2026-09-03):
   * This theorem only combines `doubleCompletion_iff_oneRelativeGram` with
     `recovery_preserves_transition_consistency`.
   * No stronger cube predicate is invented. The precise multiplicative
     consistency equation remains explicit in the statement.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionConsistentRelativeGramEquivalence

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCubeCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence
open D5.S3.Quantum.Tomography.MUBCompletionConsistencyTransport

/-- Exact relative-Gram reduction with the transition-composition equation
included. The second consistency equation is automatic under rational recovery,
so it introduces no new feasibility variable or constraint on `P`. -/
theorem consistentDoubleCompletion_iff_oneRelativeGram
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H X Y : ComplexSquare n)
    (s : ℂ)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y)
    (hConsistency : H * X = s • entrywiseConj Y) :
    (∃ X' Y' : ComplexSquare n,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' =
        fun _ _ ↦ (Fintype.card n : ℂ) ∧
      H * X' = s • entrywiseConj Y') ↔
    ∃ P : ComplexSquare n,
      (∀ i j,
        Complex.normSq (P i j) = (Fintype.card n : ℝ)) ∧
      IsComplexHadamard (recoverFirst X P) ∧
      IsComplexHadamard (recoverSecond Y P) := by
  constructor
  · rintro ⟨X', Y', hX', hY', hXX', hCross, hConsistency'⟩
    exact
      (doubleCompletion_iff_oneRelativeGram H X Y hH hX hY).mp
        ⟨X', Y', hX', hY', hXX', hCross⟩
  · rintro ⟨P, hPflat, hRecoverX, hRecoverY⟩
    have hReconstruct :=
      oneRelativeGram_reconstructs_doubleCompletion
        H X Y P hH hX hY hPflat hRecoverX hRecoverY
    refine ⟨recoverFirst X P, recoverSecond Y P,
      hReconstruct.1, hReconstruct.2.1,
      hReconstruct.2.2.1, hReconstruct.2.2.2, ?_⟩
    exact recovery_preserves_transition_consistency
      H X Y P s hConsistency

/-- Dimension-six specialization with transition consistency retained. -/
theorem consistentDoubleCompletion_iff_oneRelativeGram_six
    (H X Y : Mat6)
    (s : ℂ)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hY : IsComplexHadamard Y)
    (hConsistency : H * X = s • entrywiseConj Y) :
    (∃ X' Y' : Mat6,
      IsComplexHadamard X' ∧
      IsComplexHadamard Y' ∧
      HadamardUnbiased X X' ∧
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' = fun _ _ ↦ (6 : ℂ) ∧
      H * X' = s • entrywiseConj Y') ↔
    ∃ P : Mat6,
      (∀ i j, Complex.normSq (P i j) = 6) ∧
      IsComplexHadamard (recoverFirst X P) ∧
      IsComplexHadamard (recoverSecond Y P) := by
  simpa using consistentDoubleCompletion_iff_oneRelativeGram
    H X Y s hH hX hY hConsistency

#print axioms consistentDoubleCompletion_iff_oneRelativeGram
#print axioms consistentDoubleCompletion_iff_oneRelativeGram_six

end D5.S3.Quantum.Tomography.MUBCompletionConsistentRelativeGramEquivalence
