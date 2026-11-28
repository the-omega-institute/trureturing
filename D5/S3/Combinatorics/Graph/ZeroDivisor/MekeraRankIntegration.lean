/- GID: D5/S3/Combinatorics/Graph/ZeroDivisor/MekeraRankIntegration
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/ZeroDivisor/MekeraRankIntegration
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Block ranks characterize ordered arcs in full matrix rings over fields. -/

import D5.S3.LinearAlgebra.Matrix.AnnihilatorRank
import D5.S0.Certificates.Algebra.MekeraNilpotentAdjacencyRefutation

/-! Ranks characterize ordered arcs in the annihilator digraph of a full matrix ring. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration

open OmegaMath.MatrixAnnihilatorRank
open D5.S0.Certificates.Algebra.MekeraNilpotentAdjacencyRefutation (vertex arc)

private theorem vertex_iff_nonzero_det_eq_zero {F ι : Type*}
    [Field F] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F) :
    vertex A ↔ A ≠ 0 ∧ A.det = 0 :=
  nonzero_annihilator_iff_det_eq_zero A

/-- The two block-rank tests for the ordered arc from a nonzero singular matrix
to a distinct nonzero singular matrix. -/
theorem arc_iff_rank {F : Type*} [Field F] (n : ℕ) (_hn : 2 ≤ n)
    (A B : Matrix (Fin n) (Fin n) F)
    (hne : A ≠ B) (hA : A ≠ 0 ∧ A.det = 0) (hB : B ≠ 0 ∧ B.det = 0) :
    arc A B ↔
      ((A * B).rank < A.rank ∧ (A * B).rank < (Matrix.fromCols (A * B) B).rank) ∨
      ((A * B).rank < B.rank ∧ (A * B).rank < (Matrix.fromRows (A * B) A).rank) := by
  unfold arc
  rw [vertex_iff_nonzero_det_eq_zero, vertex_iff_nonzero_det_eq_zero]
  have hRank := or_congr (leftWitness_iff_rank A B) (rightWitness_iff_rank A B)
  exact ⟨fun h => hRank.mp h.2.2.2, fun h => ⟨hA, hB, hne, hRank.mpr h⟩⟩

end D5.S3.Combinatorics.Graph.ZeroDivisor.MekeraRankIntegration
