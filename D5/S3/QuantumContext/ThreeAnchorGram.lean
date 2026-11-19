/- GID: D5/S3/QuantumContext/ThreeAnchorGram
   generality: G
   mirror-B: D5/B/S3/QuantumContext/ThreeAnchorGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-vector Gram determinant and positivity detect independent anchors. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! Three-anchor Gram determinants and their independence criterion. -/

open scoped InnerProductSpace

namespace D5.S3.QuantumContext.ThreeAnchorGram

/-- The Gram matrix of three vectors, displayed in the order used by the
three-anchor constraint model. -/
def threeAnchorGram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v w : E) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.gram ℝ ![u, v, w]

/-- The three-anchor Gram determinant is the squared volume expression. -/
theorem three_anchor_gram_det_formula {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v w : E) :
    (threeAnchorGram u v w).det =
      ‖u‖ ^ 2 * ‖v‖ ^ 2 * ‖w‖ ^ 2
        + 2 * ⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ * ⟪v, w⟫_ℝ
        - ‖u‖ ^ 2 * ⟪v, w⟫_ℝ ^ 2
        - ‖v‖ ^ 2 * ⟪u, w⟫_ℝ ^ 2
        - ‖w‖ ^ 2 * ⟪u, v⟫_ℝ ^ 2 := by
  simp [threeAnchorGram, Matrix.gram, Matrix.det_fin_three, real_inner_comm]
  ring

/-- A three-vector Gram determinant is positive exactly when the three vectors
are linearly independent over the reals. -/
theorem three_anchor_gram_det_pos_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v w : E) :
    0 < (threeAnchorGram u v w).det ↔ LinearIndependent ℝ ![u, v, w] := by
  constructor
  · intro h
    apply (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).mp
    simpa [threeAnchorGram] using (ne_of_gt h)
  · intro h
    have hpos : Matrix.PosDef (Matrix.gram ℝ ![u, v, w]) :=
      Matrix.posDef_gram_of_linearIndependent h
    simpa [threeAnchorGram] using hpos.det_pos

end D5.S3.QuantumContext.ThreeAnchorGram
