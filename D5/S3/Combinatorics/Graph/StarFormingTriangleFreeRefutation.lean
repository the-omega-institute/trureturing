/- GID: D5/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarFormingTriangleFreeRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: none
   digest: The bipartite two-star counterexample refutes triangle-free equality at k = 2. -/

import D5.S3.Combinatorics.Graph.StarFormingDissociationRefutation

namespace D5.S3.Combinatorics.Graph.StarFormingTriangleFreeRefutation

open StarFormingDissociationRefutation

/-- Conjecture 7.2, with finite vertex types represented by Fin n. -/
def claim : Prop := ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
  G.CliqueFree 3 → beta G 2 = SF G 2

/-- The triangle-free equality implies the false bipartite equality at two. -/
theorem result : ¬ claim := by
  intro h
  apply StarFormingDissociationRefutation.result
  intro n G _ hc
  exact h n G (hc.cliqueFree (Nat.lt_succ_self 2))

end D5.S3.Combinatorics.Graph.StarFormingTriangleFreeRefutation
