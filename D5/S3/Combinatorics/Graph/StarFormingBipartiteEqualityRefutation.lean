/- GID: D5/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarFormingBipartiteEqualityRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: The bipartite two-star counterexample refutes bipartite equality for all positive k. -/

import D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace D5.S3.Combinatorics.Graph.StarFormingBipartiteEqualityRefutation

open StarFormingDissociationRefutation

/-- Conjecture 4.1, with finite vertex types represented by Fin n. -/
def claim : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (k : ℕ), 1 ≤ k → G.Colorable 2 → beta G k = SF G k

/-- The all-positive-k bipartite equality implies the false bipartite equality at two. -/
theorem result : ¬ claim := by
  intro h
  apply StarFormingDissociationRefutation.result
  intro n G _ hc
  exact h n G 2 (Nat.le_succ 1) hc

end D5.S3.Combinatorics.Graph.StarFormingBipartiteEqualityRefutation
