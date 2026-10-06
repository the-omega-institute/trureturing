/- GID: D5/S3/Combinatorics/Graph/PrefixReversalStarCardinality
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/PrefixReversalStarCardinality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Combinatorics/Graph/PrefixReversalZeroStarComplement]
   utility: none
   digest: The residual zero-star has exactly m((m+1)2) vertices by the explicit group-action coordinates. -/

import D5.S3.Combinatorics.Graph.PrefixReversalZeroStarComplement

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.PrefixReversalStarCardinality

open PrefixReversalZeroStarComplement

universe u

/- The coordinate bijection turns the abstract deletion star into the exact
   finite product used by the native Hamilton layer.  This exposes the vertex
   count as a theorem rather than leaving it implicit in the later walk. -/
theorem star_cardinality {m : ℕ} (hm : 3 ≤ m) (z : Configuration m) :
    @Fintype.card
      {v : Configuration m //
        Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v}
      (Fintype.ofEquiv (Fin m × Fin (m + 1) × Bool) (coordinateEquiv hm z)) =
      m * ((m + 1) * 2) := by
  let e := coordinateEquiv hm z
  let targetFintype : Fintype {v : Configuration m //
      Star (z (Fin.last m)) (residualList z : Cycle (Fin (m + 1))) v} :=
    Fintype.ofEquiv (Fin m × Fin (m + 1) × Bool) e
  change @Fintype.card _ targetFintype = _
  have h := @Fintype.card_congr (Fin m × Fin (m + 1) × Bool)
    {v : Configuration m // Star (z (Fin.last m))
      (residualList z : Cycle (Fin (m + 1))) v} _ targetFintype e
  rw [← h]
  simp

end D5.S3.Combinatorics.Graph.PrefixReversalStarCardinality
