/- GID: D5/S3/Quantum/Tomography/MUBCompletionConsistencyTransport
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/MUBCompletionConsistencyTransport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Rational relative-Gram recovery preserves the multiplicative transition consistency of a factorized MUB completion. -/

import D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence

/- Library-search audit trail (2026-09-03):
   * Reuses `entrywiseConj`, `recoverFirst`, and `recoverSecond` from the exact
     relative-Gram reduction.
   * Reuses Matrix multiplication and finite sums. Only the missing transport
     law for the existing recovery formulas is added.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.MUBCompletionConsistencyTransport

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.MUBCompletionRelativeGramEquivalence

/-- Entrywise complex conjugation preserves matrix multiplication. -/
theorem entrywiseConj_mul
    {m n p : Type*} [Fintype n]
    (A : Matrix m n ℂ) (B : Matrix n p ℂ) :
    entrywiseConj (A * B) = entrywiseConj A * entrywiseConj B := by
  ext i j
  simp [entrywiseConj, Matrix.mul_apply, map_sum, map_mul]

/-- Entrywise complex conjugation is involutive. -/
theorem entrywiseConj_entrywiseConj
    {m n : Type*} (A : Matrix m n ℂ) :
    entrywiseConj (entrywiseConj A) = A := by
  ext i j
  simp [entrywiseConj]

/-- The inverse finite-cardinality scalar is fixed by complex conjugation. -/
theorem entrywiseConj_invCard_smul
    {m n κ : Type*} [Fintype κ]
    (A : Matrix m n ℂ) :
    entrywiseConj (((Fintype.card κ : ℂ)⁻¹) • A) =
      ((Fintype.card κ : ℂ)⁻¹) • entrywiseConj A := by
  ext i j
  simp [entrywiseConj]

/-- Relative-Gram recovery preserves the transition-composition equation.

The standard factorized MUB convention has an equation of the form
`H X = s • entrywiseConj Y`, with `s = sqrt d` after choosing normalized or
unnormalized transition matrices. If `X` is transported by `P`, the conjugate
coupling in `recoverSecond` transports `Y` so that the same equation remains
true. -/
theorem recovery_preserves_transition_consistency
    {n : Type*} [Fintype n]
    (H X Y P : ComplexSquare n)
    (s : ℂ)
    (hConsistency : H * X = s • entrywiseConj Y) :
    H * recoverFirst X P =
      s • entrywiseConj (recoverSecond Y P) := by
  let dInv : ℂ := (Fintype.card n : ℂ)⁻¹
  calc
    H * recoverFirst X P =
        dInv • (H * (X * P)) := by
      simp [recoverFirst, dInv]
    _ = dInv • ((H * X) * P) := by
      rw [Matrix.mul_assoc]
    _ = dInv • ((s • entrywiseConj Y) * P) := by
      rw [hConsistency]
    _ = s • (dInv • (entrywiseConj Y * P)) := by
      simp [smul_smul, mul_comm, mul_left_comm]
    _ = s • entrywiseConj
        (dInv • (Y * entrywiseConj P)) := by
      rw [entrywiseConj_invCard_smul]
      rw [entrywiseConj_mul]
      rw [entrywiseConj_entrywiseConj]
    _ = s • entrywiseConj (recoverSecond Y P) := by
      rfl

#print axioms entrywiseConj_mul
#print axioms entrywiseConj_entrywiseConj
#print axioms entrywiseConj_invCard_smul
#print axioms recovery_preserves_transition_consistency

end D5.S3.Quantum.Tomography.MUBCompletionConsistencyTransport
