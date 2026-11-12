/- GID: D5/S3/QuantumContext/TwoAnchorGram
   generality: G
   mirror-B: D5/B/S3/QuantumContext/TwoAnchorGram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The two-vector Gram determinant is explicit and is positive exactly on independent anchors. -/

import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped InnerProductSpace

namespace D5.S3.QuantumContext.TwoAnchorGram

/-- The Gram matrix of two vectors, displayed in the order used by the book's
two-anchor corridor model. -/
def twoAnchorGram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v : E) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.gram ℝ ![u, v]

/-- The two-anchor Gram determinant is the squared area expression. -/
theorem two_anchor_gram_det_formula {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    (twoAnchorGram u v).det = ‖u‖ ^ 2 * ‖v‖ ^ 2 - (⟪u, v⟫_ℝ) ^ 2 := by
  simp [twoAnchorGram, Matrix.gram, Matrix.det_fin_two, real_inner_comm]
  ring

/-- A two-vector Gram determinant is positive exactly when the two anchors are
linearly independent. -/
theorem two_anchor_gram_det_pos_iff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (u v : E) :
    0 < (twoAnchorGram u v).det ↔ LinearIndependent ℝ ![u, v] := by
  constructor
  · intro h
    apply (Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)).mp
    simpa [twoAnchorGram] using (ne_of_gt h)
  · intro h
    have hpos : Matrix.PosDef (Matrix.gram ℝ ![u, v]) :=
      Matrix.posDef_gram_of_linearIndependent h
    simpa [twoAnchorGram] using hpos.det_pos

end D5.S3.QuantumContext.TwoAnchorGram
