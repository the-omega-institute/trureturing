/- GID: D5/S3/Quantum/Decoherence/EnvironmentMarginalChannel
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/EnvironmentMarginalChannel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite environment marginal is the entrywise channel of its record Gram matrix. -/

import D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality

/- Library-search audit trail (2026-08-27):
   * `SingletonRecordClassicality.recordGram` is the canonical general finite
     record-overlap primitive and is reused directly.
   * `EnvironmentRecords` and the private bridge in `MeasurementMarginal` cover
     only the fixed two-point carrier; `RecordingIsometry` and
     `NonselectiveMarginalization` cover orthogonal projective recordings.
   * Pinned Mathlib supplies matrix multiplication, conjugate transpose,
     Hadamard product, and finite-sum rules, but no packaged theorem equating
     this arbitrary finite environment marginal with its Gram channel. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Decoherence.EnvironmentMarginalChannel

open D5.S3.Quantum.FixedAlgebra.SingletonRecordClassicality

/-- Tracing the finite environment out of the controlled recording of an
arbitrary system matrix gives both the canonical record channel and the
Hadamard product with the record Gram matrix, entry by entry. -/
theorem environment_marginal_channel {d e : Nat}
    (record : Fin d -> Fin e -> ℂ)
    (rho : Matrix (Fin d) (Fin d) ℂ) :
    let recording : Matrix (Fin d × Fin e) (Fin d) ℂ :=
      fun indexed j => if j = indexed.1 then record indexed.1 indexed.2 else 0
    let partialTrace :
        Matrix (Fin d × Fin e) (Fin d × Fin e) ℂ ->
          Matrix (Fin d) (Fin d) ℂ :=
      fun joint i j => ∑ a, joint (i, a) (j, a)
    partialTrace (recording * rho * Matrix.conjTranspose recording) =
        recordChannel record rho ∧
      partialTrace (recording * rho * Matrix.conjTranspose recording) =
        Matrix.hadamard (fun i j => recordGram record i j) rho ∧
      ∀ i j,
        partialTrace (recording * rho * Matrix.conjTranspose recording) i j =
          recordGram record i j * rho i j := by
  dsimp only
  let recording : Matrix (Fin d × Fin e) (Fin d) ℂ :=
    fun indexed j => if j = indexed.1 then record indexed.1 indexed.2 else 0
  have hEntry (i j : Fin d) :
      (∑ a, (recording * rho * Matrix.conjTranspose recording) (i, a) (j, a)) =
        recordGram record i j * rho i j := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp [recording, recordGram, apply_ite, Finset.sum_mul, mul_assoc]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simpa [recording, recordChannel] using hEntry i j
  · ext i j
    change
      (∑ a, (recording * rho * Matrix.conjTranspose recording) (i, a) (j, a)) =
        recordGram record i j * rho i j
    exact hEntry i j
  · intro i j
    simpa [recording] using hEntry i j

#print axioms environment_marginal_channel

end D5.S3.Quantum.Decoherence.EnvironmentMarginalChannel
