/- GID: D5/S3/Observer/BlockStructure/ProjectionCommutatorCrossBlockCriterion
   generality: G
   mirror-B: D5/B/S3/Observer/BlockStructure/ProjectionCommutatorCrossBlockCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An orthogonal projection commutator is the difference of its directed cross blocks and vanishes exactly when both cross blocks vanish. -/

import D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/- Library-search audit trail (2026-08-27):
   * Repository searches for projection commutators, star projections, and cross-block
     vanishing found no single theorem with both public clauses on the Hilbert carrier.
   * The frozen `commutator_eq_cross_blocks` is the exact identity clause and is applied
     directly; its adjacent iff theorem is restricted to finite complex matrices.
   * Pinned Mathlib supplies `Submodule.isIdempotentElem_starProjection` together with
     `IsIdempotentElem.mul_one_sub_self` and `one_sub_mul_self`, but no packaged theorem
     combining the identity and both cross-block implications.
 -/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.BlockStructure.ProjectionCommutatorCrossBlockCriterion

open D5.S3.Observer.HiddenFlow.ProjectionCommutatorIdentity

/-- For the canonical orthogonal projection onto `V`, the commutator is the difference
of the two directed cross blocks, and it vanishes exactly when both blocks vanish. -/
theorem projection_commutator_cross_blocks
    {K H : Type*} [RCLike K] [NormedAddCommGroup H]
    [InnerProductSpace K H]
    (V : Submodule K H) [V.HasOrthogonalProjection]
    (T : H →L[K] H) :
    let P := V.starProjection
    let Q := 1 - P
    (commutator P T = P * T * Q - Q * T * P) ∧
      (commutator P T = 0 ↔ P * T * Q = 0 ∧ Q * T * P = 0) := by
  dsimp only
  let P := V.starProjection
  let Q := 1 - P
  have hP : IsIdempotentElem P := V.isIdempotentElem_starProjection
  have hPP : P * P = P := hP
  have hPQ : P * Q = 0 := by
    simpa only [Q] using hP.mul_one_sub_self
  have hQP : Q * P = 0 := by
    simpa only [Q] using hP.one_sub_mul_self
  have hQQ : Q * Q = Q := by
    dsimp only [Q]
    calc
      (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
      _ = 1 - P := by rw [hPP]; abel
  have hIdentity : commutator P T = P * T * Q - Q * T * P :=
    commutator_eq_cross_blocks P Q T rfl
  refine ⟨hIdentity, ?_⟩
  constructor
  · intro hComm
    have hCross : P * T * Q - Q * T * P = 0 := by
      rw [← hIdentity]
      exact hComm
    constructor
    · have hLeft : P * (P * T * Q - Q * T * P) * Q = P * T * Q := by
        calc
          P * (P * T * Q - Q * T * P) * Q =
              (P * P) * T * (Q * Q) - (P * Q) * T * (P * Q) := by
            noncomm_ring
          _ = P * T * Q := by rw [hPP, hQQ, hPQ]; simp
      have hIsolated := congrArg (fun A => P * A * Q) hCross
      rw [hLeft] at hIsolated
      simpa using hIsolated
    · have hNeg : -(Q * T * P) = 0 := by
        have hRight : Q * (P * T * Q - Q * T * P) * P = -(Q * T * P) := by
          calc
            Q * (P * T * Q - Q * T * P) * P =
                (Q * P) * T * (Q * P) - (Q * Q) * T * (P * P) := by
              noncomm_ring
            _ = -(Q * T * P) := by rw [hQP, hQQ, hPP]; simp
        have hIsolated := congrArg (fun A => Q * A * P) hCross
        rw [hRight] at hIsolated
        simpa using hIsolated
      exact neg_eq_zero.mp hNeg
  · rintro ⟨hVisible, hResidual⟩
    rw [hIdentity, hVisible, hResidual, sub_zero]

example :
    let V : Submodule ℝ ℝ := ⊥
    let T : ℝ →L[ℝ] ℝ := 0
    let P := V.starProjection
    let Q := 1 - P
    (commutator P T = P * T * Q - Q * T * P) ∧
      (commutator P T = 0 ↔ P * T * Q = 0 ∧ Q * T * P = 0) := by
  exact projection_commutator_cross_blocks (⊥ : Submodule ℝ ℝ) 0

#print axioms projection_commutator_cross_blocks

end D5.S3.Observer.BlockStructure.ProjectionCommutatorCrossBlockCriterion
