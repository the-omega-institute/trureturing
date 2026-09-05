/- GID: D5/S3/Quantum/Tomography/MUBCompletionSingleRelativeGram
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionSingleRelativeGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every fixed-edge mutually unbiased double completion yields one scaled-Hadamard relative Gram that recovers both second factors. -/

import D5.S3.Quantum.Tomography.ComplexHadamardTwoSided

/- Library-search audit trail (2026-09-03):
   * This module is only an aggregation layer over
     `MUBCubeCompatibility`, `MUBCompletionGluing`, and
     `ComplexHadamardTwoSided`.
   * It introduces no new matrix carrier, no new Hadamard predicate, and no
     duplicate cube multiplication proof.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionSingleRelativeGram

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCubeCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionGluing
open D5.S3.Quantum.Tomography.ComplexHadamardTwoSided

/-- Necessary one-matrix system for a fixed-edge mutually unbiased double
completion.

Set `P = Xᴴ X'`. Then `P` is entrywise of squared modulus `d`, has row Gram
`d^2 I`, and determines both second-completion factors through

`X P = d X'` and `Y (entrywiseConj P) = d Y'`.

The theorem keeps the unnormalized convention, so every coefficient is
rational in the finite cardinality and no square root occurs. -/
theorem doubleCompletion_yields_singleRelativeGramSystem
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H X X' Y Y' : ComplexSquare n)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hX' : IsComplexHadamard X')
    (hY : IsComplexHadamard Y)
    (hXX' : HadamardUnbiased X X')
    (hCubeCross :
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' =
        fun _ _ ↦ (Fintype.card n : ℂ)) :
    let P := Xᴴ * X'
    (∀ i j, Complex.normSq (P i j) = (Fintype.card n : ℝ)) ∧
    P * Pᴴ =
      ((Fintype.card n : ℂ) * (Fintype.card n : ℂ)) •
        (1 : ComplexSquare n) ∧
    X * P = (Fintype.card n : ℂ) • X' ∧
    Y * (fun i j ↦ star (P i j)) =
      (Fintype.card n : ℂ) • Y' := by
  dsimp
  have hScaled := relativeGram_scaledHadamard X X' hX hX' hXX'
  have hDetermined :=
    second_completion_determined_by_one_relativeGram
      H X X' Y Y' hH hX hY hXX' hCubeCross
  refine ⟨hScaled.1, hScaled.2,
    left_mul_relativeGram_eq_card_smul X X' hX.2, ?_⟩
  have hYRecovery := left_mul_relativeGram_eq_card_smul Y Y' hY.2
  rwa [hDetermined.1] at hYRecovery

/-- Dimension-six specialization of the necessary relative-Gram equations. -/
theorem doubleCompletion_yields_singleRelativeGramSystem_six
    (H X X' Y Y' : Mat6)
    (hH : EntrywiseUnit H)
    (hX : IsComplexHadamard X)
    (hX' : IsComplexHadamard X')
    (hY : IsComplexHadamard Y)
    (hXX' : HadamardUnbiased X X')
    (hCubeCross :
      (factorizedCubeMatrix H X Y)ᴴ *
          factorizedCubeMatrix H X' Y' =
        fun _ _ ↦ (6 : ℂ)) :
    let P := Xᴴ * X'
    (∀ i j, Complex.normSq (P i j) = 6) ∧
    P * Pᴴ = (36 : ℂ) • (1 : Mat6) ∧
    X * P = (6 : ℂ) • X' ∧
    Y * (fun i j ↦ star (P i j)) = (6 : ℂ) • Y' := by
  simpa using
    (doubleCompletion_yields_singleRelativeGramSystem
      H X X' Y Y' hH hX hX' hY hXX' hCubeCross)

#print axioms doubleCompletion_yields_singleRelativeGramSystem
#print axioms doubleCompletion_yields_singleRelativeGramSystem_six

end D5.S3.Quantum.Tomography.MUBCompletionSingleRelativeGram
