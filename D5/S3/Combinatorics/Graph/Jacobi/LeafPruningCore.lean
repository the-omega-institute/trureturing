/- GID: D5/S3/Combinatorics/Graph/Jacobi/LeafPruningCore
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/Jacobi/LeafPruningCore
   mirror-E: none(waiver:actual-protected-pruning-core-maximality)
   anchors: []
   utility: none
   digest: Every internally stable vertex set survives actual protected leaf pruning. -/

import D5.S3.Combinatorics.Graph.Jacobi.FlagPruning

/-! Maximality and chronology independence of the actual retained core. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Graph.Jacobi.FlagGraph.LeafPruning

/-- The terminal vertices contain every vertex set whose nonanchor vertices
have at least two actual flags with mates in the set. Thus the retained core
is the greatest such set and is independent of the deletion chronology.
Loops contribute both flags, and no connectedness or stability is assumed. -/
theorem terminal_core_greatest {F : Type} [Finite F] {G : FlagGraph F}
    (P : G.LeafPruning) (S : Set G.VertexOrbit)
    (hS : ∀ v ∈ S, ¬G.HasAnchor v →
      2 ≤ Nat.card {f : F // G.vertexOf f = v ∧ G.vertexOf (G.edge f) ∈ S}) :
    S ⊆ {v | P.rank v = P.steps} := by
  classical
  have no_delete : ∀ i : ℕ, ∀ v ∈ S, P.rank v = i → P.rank v < P.steps → False := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro v hv hvi hdel
      have hna : ¬G.HasAnchor v := by
        intro ha
        have := P.protect_anchor v ha
        omega
      let A := {f : F // G.vertexOf f = v ∧ G.vertexOf (G.edge f) ∈ S}
      let B := {f : F // G.vertexOf f = v ∧
        P.rank v ≤ P.rank (G.vertexOf (G.edge f))}
      let embed : A → B := fun f => ⟨f.val, f.property.1, by
        by_contra hnot
        have hm : P.rank (G.vertexOf (G.edge f.val)) < i := by omega
        exact ih _ hm _ f.property.2 rfl (by omega)⟩
      have hinj : Function.Injective embed := by
        intro f g he
        apply Subtype.ext
        exact congrArg (fun z : B => z.val) he
      have hcard := Nat.card_le_card_of_injective embed hinj
      have hlow := hS v hv hna
      have hhigh := P.deletion_degree v hdel
      change Nat.card A ≤ Nat.card B at hcard
      change 2 ≤ Nat.card A at hlow
      change Nat.card B ≤ 1 at hhigh
      omega
  intro v hv
  by_contra hne
  change P.rank v ≠ P.steps at hne
  exact no_delete (P.rank v) v hv rfl (by have := P.rank_le v; omega)

end D5.S3.Combinatorics.Graph.Jacobi.FlagGraph.LeafPruning
