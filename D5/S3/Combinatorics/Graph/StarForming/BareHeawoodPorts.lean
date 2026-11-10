/- GID: D5/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/BareHeawoodPorts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularBound

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/BareHeawoodPorts.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.BarePorts

open D5.S3.Combinatorics.Graph.StarForming.Regular

theorem only_failure_forces_bare_boundary {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (deleted port support : Vertex)
    (hminimal : Minimal adjacency selection) (hdeleted : selection deleted)
    (hnew : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted)
    (hother : ∀ outside, ¬ selection outside → outside ≠ port →
      TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside)
    (hsupport : selection support) (hkeep : support ≠ deleted)
    (hedge : adjacency port support) (hnotdeleted : ¬ adjacency port deleted) :
    ¬ selection port ∧
      ∀ neighbor, adjacency port neighbor → selection neighbor → neighbor = support := by
  classical
  obtain ⟨outside, houtside, hfailure⟩ :=
    covered_deletion_has_failure adjacency selection hminimal deleted hdeleted hnew
  have hequal : outside = port := by
    apply Classical.byContradiction
    intro hdifferent
    exact hfailure (hother outside houtside hdifferent)
  subst outside
  refine ⟨houtside, ?_⟩
  intro neighbor hadjacent hselected
  apply Classical.byContradiction
  intro hdifferent
  have hneighbor : neighbor ≠ deleted := by
    intro hequal
    exact hnotdeleted (hequal ▸ hadjacent)
  apply hfailure
  exact Or.inl ⟨neighbor, support, ⟨hselected, hneighbor⟩,
    ⟨hsupport, hkeep⟩, hdifferent, hadjacent, hedge⟩

theorem internal_neighbors_omitted {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection internal : Vertex → Prop)
    (port support : Vertex)
    (hboundary : ¬ selection port ∧
      ∀ neighbor, adjacency port neighbor → selection neighbor → neighbor = support)
    (hexternal : ¬ internal support) :
    ¬ selection port ∧
      ∀ neighbor, internal neighbor → adjacency port neighbor → ¬ selection neighbor := by
  refine ⟨hboundary.1, ?_⟩
  intro neighbor hinternal hadjacent hselected
  have hequal := hboundary.2 neighbor hadjacent hselected
  exact hexternal (hequal ▸ hinternal)

end D5.S3.Combinatorics.Graph.StarForming.BarePorts
