/- GID: D5/S3/Quantum/Decoherence/RecordingIsometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Decoherence/RecordingIsometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The canonical recording matrix is isometric and has the expected state blocks. -/

import Mathlib

/- Library-search audit trail (2026-08-27):
   * Repository searches found finite environment-record calculations in
     `Quantum.EnvironmentRecords` but no theorem exposing the canonical recording map, its
     isometry, and its arbitrary-state block expansion together.
   * Body-shape searches for a matrix with entries `P a i j` on the product output basis found no
     existing D5 definition, so the canonical map is displayed as a `let` in the public theorem.
   * Pinned Mathlib supplies `Matrix.conjTranspose_apply`, `Matrix.mul_apply`, and
     `Fintype.sum_prod_type`; each is used directly in the proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators ComplexConjugate

namespace D5.S3.Quantum.Decoherence.RecordingIsometry

/-- Orthogonal self-adjoint projectors summing to the identity define the canonical product-basis
recording isometry. Conjugating an arbitrary state by that same map has `(a,b)` block
`P_a rho P_b`. -/
theorem recording_isometry_and_state_blocks
    {System Outcome : Type*}
    [Fintype System] [DecidableEq System]
    [Fintype Outcome] [DecidableEq Outcome]
    (projector : Outcome -> Matrix System System ℂ)
    (projectorSelfAdjoint : forall a,
      Matrix.conjTranspose (projector a) = projector a)
    (projectorOrthogonal : forall a b,
      projector a * projector b = if a = b then projector a else 0)
    (projectorComplete : ∑ a, projector a = 1) :
    let recording : Matrix (System × Outcome) System ℂ :=
      fun indexed j => projector indexed.2 indexed.1 j
    Matrix.conjTranspose recording * recording = 1 /\
      forall (rho : Matrix System System ℂ) (a b : Outcome) (i j : System),
        (recording * rho * Matrix.conjTranspose recording) (i, a) (j, b) =
          (projector a * rho * projector b) i j := by
  dsimp only
  have projectorConjugate (a : Outcome) (i j : System) :
      star (projector a j i) = projector a i j := by
    have entry := congrFun (congrFun (projectorSelfAdjoint a) i) j
    simpa only [Matrix.conjTranspose_apply] using entry
  constructor
  · ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    calc
      (∑ x : System × Outcome,
          star (projector x.2 x.1 i) * projector x.2 x.1 j) =
          ∑ a : Outcome, ∑ k : System,
            star (projector a k i) * projector a k j := by
              rw [Fintype.sum_prod_type, Finset.sum_comm]
      _ = ∑ a : Outcome,
          (Matrix.conjTranspose (projector a) * projector a) i j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [Matrix.mul_apply]
            rfl
      _ = ∑ a : Outcome, (projector a * projector a) i j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [projectorSelfAdjoint]
      _ = ∑ a : Outcome, projector a i j := by
            apply Finset.sum_congr rfl
            intro a _
            rw [projectorOrthogonal a a, if_pos rfl]
      _ = (∑ a : Outcome, projector a) i j := by
            simp only [Matrix.sum_apply]
      _ = (1 : Matrix System System ℂ) i j := by
            rw [projectorComplete]
  · intro rho a b i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    simp_rw [projectorConjugate]

#print axioms recording_isometry_and_state_blocks

end D5.S3.Quantum.Decoherence.RecordingIsometry
