/- GID: D5/S3/Combinatorics/Graph/StarForming/PortClauseOwnership
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/PortClauseOwnership
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.PrivateClauses

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/PortClauseOwnership.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.PortClauseOwnership

open D5.S3.Combinatorics.Graph.StarForming.PrivateClauses

def BasedAt {Vertex : Type} (internal : Vertex → Prop) (port : Vertex) : Clause Vertex → Prop
  | .closed center => center = port
  | .oriented center neighbor =>
      (center = port ∧ internal neighbor) ∨ (neighbor = port ∧ internal center)

theorem external_neighbor_in_support {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (internal : Vertex → Prop)
    (port vertex : Vertex) (clause : Clause Vertex)
    (hbased : BasedAt internal port clause) (hexternal : ¬ internal vertex)
    (hedge : adjacency port vertex) : Support adjacency clause vertex := by
  cases clause with
  | closed center =>
    change center = port at hbased
    subst center
    exact Or.inr hedge
  | oriented center neighbor =>
    change (center = port ∧ internal neighbor) ∨
      (neighbor = port ∧ internal center) at hbased
    rcases hbased with ⟨rfl, hneighbor⟩ | ⟨rfl, hcenter⟩
    · exact Or.inr (Or.inl ⟨hedge,
        fun hequal => hexternal (hequal.symm ▸ hneighbor)⟩)
    · exact Or.inr (Or.inr ⟨hedge,
        fun hequal => hexternal (hequal.symm ▸ hcenter)⟩)

theorem outside_neighbors_unique {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (internal selection : Vertex → Prop)
    (port owner : Vertex) (clause : Clause Vertex)
    (hbased : BasedAt internal port clause)
    (hprivate : Private adjacency selection clause owner) :
    ∀ vertex, ¬ internal vertex → selection vertex → adjacency port vertex → vertex = owner := by
  intro vertex hexternal hselected hedge
  exact hprivate.2.2 vertex hselected
    (external_neighbor_in_support adjacency internal port vertex clause hbased hexternal hedge)

end D5.S3.Combinatorics.Graph.StarForming.PortClauseOwnership
