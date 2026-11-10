/- GID: D5/S3/Combinatorics/Graph/StarForming/CubicStability
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CubicStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularBound

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/CubicStability.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.CubicStability

open D5.S3.Combinatorics.Graph.StarForming.Regular

theorem leaf_has_adjacent_failure {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hminimal : Minimal adjacency selection)
    (leaf support : Vertex) (hleaf : selection leaf)
    (hhigh : High adjacency selection support) (hsupport : adjacency leaf support)
    (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support) :
    ∃ outside, Failure adjacency selection leaf outside ∧ adjacency outside leaf := by
  classical
  have hdifferent : support ≠ leaf := by
    intro hequal
    exact hirreflexive leaf (hequal ▸ hsupport)
  have hnew := adjacent_high_survives adjacency selection support leaf leaf
    hhigh hdifferent hsupport
  obtain ⟨outside, hfailure⟩ :=
    covered_deletion_has_failure adjacency selection hminimal leaf hleaf hnew
  refine ⟨outside, hfailure, ?_⟩
  apply Classical.byContradiction
  intro hnonadjacent
  apply hfailure.2
  rcases hminimal.1 outside hfailure.1 with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, endpoint, hc, he, ha, hb⟩
  · have hfirst : first ≠ leaf := fun heq => hnonadjacent (heq ▸ ha)
    have hsecond : second ≠ leaf := fun heq => hnonadjacent (heq ▸ hb)
    exact Or.inl ⟨first, second, ⟨hf, hfirst⟩, ⟨hs, hsecond⟩, hne, ha, hb⟩
  · have hcenter : center ≠ leaf := fun heq => hnonadjacent (heq ▸ ha)
    by_cases hendpoint : endpoint = leaf
    · have hequal : center = support :=
        hunique center hc (hsymmetric _ _ (hendpoint ▸ hb))
      exact adjacent_high_survives adjacency selection support leaf outside
        hhigh hdifferent (hequal ▸ ha)
    · exact Or.inr ⟨center, endpoint, ⟨hc, hcenter⟩, ⟨he, hendpoint⟩, ha, hb⟩

theorem leaf_failure_other_neighbor_is_isolated {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (leaf support outside other : Vertex)
    (hhigh : High adjacency selection support)
    (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support)
    (hfailure : Failure adjacency selection leaf outside)
    (hother : selection other) (hdifferent : other ≠ leaf)
    (hedge : adjacency outside other) :
    ∀ endpoint, selection endpoint → ¬ adjacency other endpoint := by
  intro endpoint hselected hadjacent
  apply hfailure.2
  by_cases hequal : endpoint = leaf
  · have hsupport : other = support :=
      hunique other hother (hsymmetric _ _ (hequal ▸ hadjacent))
    exact adjacent_high_survives adjacency selection support leaf outside
      hhigh (hsupport ▸ hdifferent) (hsupport ▸ hedge)
  · exact Or.inr ⟨other, endpoint, ⟨hother, hdifferent⟩, ⟨hselected, hequal⟩,
      hedge, hadjacent⟩

theorem high_adjacent_failure_other_neighbor_is_isolated {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (htrianglefree : ∀ outside first second, adjacency outside first →
      adjacency outside second → adjacency first second → False)
    (deleted outside other : Vertex)
    (hfailure : Failure adjacency selection deleted outside)
    (hdeletededge : adjacency outside deleted)
    (hotheredge : adjacency outside other)
    (hother : selection other) (hdifferent : other ≠ deleted) :
    ∀ endpoint, selection endpoint → ¬ adjacency other endpoint := by
  intro endpoint hselected hadjacent
  by_cases hequal : endpoint = deleted
  · exact htrianglefree outside deleted other hdeletededge hotheredge
      (hsymmetric _ _ (hequal ▸ hadjacent))
  · exact hfailure.2 (Or.inr ⟨other, endpoint, ⟨hother, hdifferent⟩,
      ⟨hselected, hequal⟩, hotheredge, hadjacent⟩)

theorem shared_leaf_high_witness_has_good_support_owner {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (htrianglefree : ∀ outside first second, adjacency outside first →
      adjacency outside second → adjacency first second → False)
    (leaf support deleted outside : Vertex)
    (hleaf : selection leaf) (hsupport : selection support)
    (hleafedge : adjacency leaf support) (houtsideedge : adjacency outside leaf)
    (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support)
    (hhigh : High adjacency selection deleted)
    (hfailure : Failure adjacency selection deleted outside) :
    deleted = support ∧ ¬ adjacency outside deleted := by
  classical
  have hnotleaf : deleted ≠ leaf := by
    intro hequal
    subst deleted
    obtain ⟨first, second, hf, hs, hne, ha, hb⟩ := hhigh.2
    exact hne ((hunique first hf ha).trans (hunique second hs hb).symm)
  have howner : deleted = support := by
    apply Classical.byContradiction
    intro hdifferent
    exact hfailure.2 (Or.inr ⟨leaf, support,
      ⟨hleaf, fun hequal => hnotleaf hequal.symm⟩,
      ⟨hsupport, fun hequal => hdifferent hequal.symm⟩, houtsideedge, hleafedge⟩)
  refine ⟨howner, ?_⟩
  intro hedge
  exact htrianglefree outside leaf support houtsideedge (howner ▸ hedge) hleafedge

end D5.S3.Combinatorics.Graph.StarForming.CubicStability
