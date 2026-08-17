/- GID: D5/S3/Factorization/Squarefree/SquarefreeSquareDecompositionExistence
   generality: G
   mirror-B: D5/B/S3/Factorization/Squarefree/SquarefreeSquareDecompositionExistence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive naturals have a unique square-times-squarefree decomposition. -/

import D5.S3.Factorization.SquarefreeSquareDecomposition

namespace D5.S3.Factorization.Squarefree.SquarefreeSquareDecompositionExistence

/-- Every positive natural number has a unique representation as a positive square multiplied by
a squarefree natural number. -/
theorem bcs_square_squarefree_exists_unique (n : ℕ) (hn : 0 < n) :
    ∃! parts : ℕ × ℕ,
      0 < parts.1 ∧ Squarefree parts.2 ∧ parts.1 ^ 2 * parts.2 = n := by
  obtain ⟨a, b, ha, hb, hba, hsf⟩ := Nat.sq_mul_squarefree_of_pos hn
  refine ⟨(b, a), ⟨hb, hsf, hba⟩, ?_⟩
  rintro ⟨b₂, a₂⟩ ⟨hb₂, hsf₂, hba₂⟩
  have hu :=
    D5.S3.Factorization.SquarefreeSquareDecomposition.bcs_square_squarefree_unique
      (Nat.ne_of_gt hb) hsf hsf₂ (hba.trans hba₂.symm)
  exact Prod.ext hu.2.symm hu.1.symm

end D5.S3.Factorization.Squarefree.SquarefreeSquareDecompositionExistence
