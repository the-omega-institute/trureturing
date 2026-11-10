/- GID: D5/S3/Combinatorics/Graph/StarForming/CubicPathAccounting
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CubicPathAccounting
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.CubicStability
import D5.S3.Combinatorics.Graph.StarForming.DissociationCover

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/CubicPathAccounting.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.CubicPathAccounting

open D5.S3.Combinatorics.Graph.StarForming.Regular D5.S3.Combinatorics.Graph.StarForming.CubicStability
open D5.S3.Combinatorics.Graph.StarForming.DissociationCover

theorem augment_isolated_pairs {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection added : Vertex → Prop)
    (partner : Vertex → Vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hdissociates : Dissociates adjacency selection)
    (hisolated : ∀ vertex, added vertex → ∀ neighbor,
      selection neighbor → ¬ adjacency (partner vertex) neighbor)
    (hneighbor : ∀ vertex, added vertex → ∀ neighbor,
      selection neighbor → adjacency vertex neighbor → neighbor = partner vertex)
    (hindependent : ∀ first second, added first → added second → ¬ adjacency first second)
    (hinjective : ∀ first second, added first → added second →
      partner first = partner second → first = second) :
    Dissociates adjacency (fun vertex => selection vertex ∨ added vertex) := by
  intro center first second hcenter hfirst hsecond hfirstEdge hsecondEdge
  rcases hcenter with hcenter | hcenter
  · rcases hfirst with hfirst | hfirst
    · rcases hsecond with hsecond | hsecond
      · exact hdissociates center first second hcenter hfirst hsecond hfirstEdge hsecondEdge
      · have hequal := hneighbor second hsecond center hcenter (hsymmetric _ _ hsecondEdge)
        exact False.elim (hisolated second hsecond first hfirst (hequal ▸ hfirstEdge))
    · rcases hsecond with hsecond | hsecond
      · have hequal := hneighbor first hfirst center hcenter (hsymmetric _ _ hfirstEdge)
        exact False.elim (hisolated first hfirst second hsecond (hequal ▸ hsecondEdge))
      · apply hinjective first second hfirst hsecond
        exact (hneighbor first hfirst center hcenter (hsymmetric _ _ hfirstEdge)).symm.trans
          (hneighbor second hsecond center hcenter (hsymmetric _ _ hsecondEdge))
  · rcases hfirst with hfirst | hfirst
    · rcases hsecond with hsecond | hsecond
      · exact (hneighbor center hcenter first hfirst hfirstEdge).trans
          (hneighbor center hcenter second hsecond hsecondEdge).symm
      · exact False.elim (hindependent center second hcenter hsecond hsecondEdge)
    · exact False.elim (hindependent center first hcenter hfirst hfirstEdge)

theorem extra_leaf_failure_is_unused {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (htrianglefree : ∀ outside first second, adjacency outside first →
      adjacency outside second → adjacency first second → False)
    (witness reserved : Vertex → Vertex)
    (hfailure : ∀ owner, High adjacency selection owner →
      Failure adjacency selection owner (witness owner))
    (hreserved : ∀ owner, High adjacency selection owner →
      ¬ adjacency (witness owner) owner →
      ∀ neighbor, selection neighbor → adjacency (witness owner) neighbor →
        neighbor = reserved owner)
    (leaf support outside : Vertex) (hleaf : selection leaf) (hsupport : selection support)
    (hleafedge : adjacency leaf support) (houtsideedge : adjacency outside leaf)
    (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support)
    (hextra : leaf ≠ reserved support) :
    ∀ owner, High adjacency selection owner → outside ≠ witness owner := by
  intro owner hhigh hequal
  have hshared := shared_leaf_high_witness_has_good_support_owner adjacency selection
    htrianglefree leaf support owner outside hleaf hsupport hleafedge houtsideedge
    hunique hhigh (hequal.symm ▸ hfailure owner hhigh)
  have hnonadjacent : ¬ adjacency (witness owner) owner := hequal ▸ hshared.2
  have hsame := hreserved owner hhigh hnonadjacent leaf hleaf (hequal ▸ houtsideedge)
  exact hextra (hshared.1 ▸ hsame)

end D5.S3.Combinatorics.Graph.StarForming.CubicPathAccounting
