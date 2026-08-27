/- GID: D5/S3/Quantum/Decoherence/NonselectiveMarginalization
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/NonselectiveMarginalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Ignoring a finite recording register yields the sum of the diagonal measurement blocks. -/

import D5.S3.Quantum.Decoherence.RecordingIsometry

/- Library-search audit trail (2026-08-27):
   * The frozen `recording_isometry_and_state_blocks` theorem is the exact
     canonical recording-map/block identity and is applied directly.
   * Existing `Quantum.EnvironmentRecords.traceEnvironment` has the same
     partial-trace body but only on the fixed two-by-two carrier, so it cannot
     express this arbitrary finite outcome statement; the generic map remains
     a public `let` rather than a second named definition.
   * Pinned Mathlib supplies `Matrix.sum_apply` and finite-sum congruence; no
     theorem already packages the non-selective marginal identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Decoherence.NonselectiveMarginalization

open D5.S3.Quantum.Decoherence.RecordingIsometry

/-- The partial trace over the recording register of the canonical recording
map is the non-selective sum of the diagonal projective blocks. -/
theorem nonselective_recording_marginal
    {System Outcome : Type*}
    [Fintype System] [DecidableEq System]
    [Fintype Outcome] [DecidableEq Outcome]
    (projector : Outcome -> Matrix System System ℂ)
    (projectorSelfAdjoint : forall a,
      Matrix.conjTranspose (projector a) = projector a)
    (projectorOrthogonal : forall a b,
      projector a * projector b = if a = b then projector a else 0)
    (projectorComplete : ∑ a, projector a = 1)
    (rho : Matrix System System ℂ) :
    let recording : Matrix (System × Outcome) System ℂ :=
      fun indexed j => projector indexed.2 indexed.1 j
    let partialTrace :
        Matrix (System × Outcome) (System × Outcome) ℂ -> Matrix System System ℂ :=
      fun joint i j => ∑ a, joint (i, a) (j, a)
    partialTrace (recording * rho * Matrix.conjTranspose recording) =
      ∑ a, projector a * rho * projector a := by
  dsimp only
  have hblocks :=
    (recording_isometry_and_state_blocks projector projectorSelfAdjoint
      projectorOrthogonal projectorComplete).2 rho
  ext i j
  simp only [Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a ha
  exact hblocks a a i j

#print axioms nonselective_recording_marginal

end D5.S3.Quantum.Decoherence.NonselectiveMarginalization
