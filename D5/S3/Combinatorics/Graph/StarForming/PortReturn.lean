/- GID: D5/S3/Combinatorics/Graph/StarForming/PortReturn
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/PortReturn
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularBound

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/PortReturn.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.PortReturn

open D5.S3.Combinatorics.Graph.StarForming.Regular

def OnlyNeighbor {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (vertex neighbor : Vertex) : Prop :=
  adjacency vertex neighbor ∧ selection neighbor ∧
    ∀ other, selection other → adjacency vertex other → other = neighbor

def FailureShape {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (deleted outside : Vertex) : Prop :=
  OnlyNeighbor adjacency selection outside deleted ∨
  (adjacency outside deleted ∧ ∃ other, selection other ∧ other ≠ deleted ∧
    adjacency outside other ∧
    (∀ neighbor, selection neighbor → adjacency outside neighbor →
      neighbor = deleted ∨ neighbor = other) ∧
    (∀ leaf, selection leaf → adjacency other leaf → leaf = deleted)) ∨
  (¬ adjacency outside deleted ∧ ∃ support,
    OnlyNeighbor adjacency selection outside support ∧
    OnlyNeighbor adjacency selection support deleted)

theorem failure_iff_shapes {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hforms : Forms adjacency selection) (deleted outside : Vertex)
    (hselected : selection deleted) (houtside : ¬ selection outside) :
    Failure adjacency selection deleted outside ↔
      FailureShape adjacency selection deleted outside := by
  classical
  constructor
  · intro hfailure
    by_cases hedge : adjacency outside deleted
    · by_cases hother : ∃ other, selection other ∧ adjacency outside other ∧ other ≠ deleted
      · obtain ⟨other, hotherSelected, hotherEdge, hotherDifferent⟩ := hother
        refine Or.inr (Or.inl ⟨hedge, other, hotherSelected, hotherDifferent, hotherEdge, ?_, ?_⟩)
        · intro neighbor hneighbor hneighborEdge
          by_cases hequal : neighbor = deleted
          · exact Or.inl hequal
          · apply Or.inr
            apply Classical.byContradiction
            intro hdifferent
            exact hfailure.2 (Or.inl ⟨neighbor, other, ⟨hneighbor, hequal⟩,
              ⟨hotherSelected, hotherDifferent⟩, hdifferent, hneighborEdge, hotherEdge⟩)
        · intro leaf hleaf hleafEdge
          apply Classical.byContradiction
          intro hdifferent
          exact hfailure.2 (Or.inr ⟨other, leaf, ⟨hotherSelected, hotherDifferent⟩,
            ⟨hleaf, hdifferent⟩, hotherEdge, hleafEdge⟩)
      · refine Or.inl ⟨hedge, hselected, ?_⟩
        intro neighbor hneighbor hneighborEdge
        apply Classical.byContradiction
        intro hdifferent
        exact hother ⟨neighbor, hneighbor, hneighborEdge, hdifferent⟩
    · apply Or.inr ∘ Or.inr
      refine ⟨hedge, ?_⟩
      rcases hforms outside houtside with ⟨first, second, hf, hs, hne, ha, hb⟩ |
        ⟨support, leaf, hs, hl, ha, hb⟩
      · have hfirst : first ≠ deleted := fun hequal => hedge (hequal ▸ ha)
        have hsecond : second ≠ deleted := fun hequal => hedge (hequal ▸ hb)
        exact False.elim (hfailure.2 (Or.inl ⟨first, second, ⟨hf, hfirst⟩,
          ⟨hs, hsecond⟩, hne, ha, hb⟩))
      · have hsupport : support ≠ deleted := fun hequal => hedge (hequal ▸ ha)
        have hleaf : leaf = deleted := by
          apply Classical.byContradiction
          intro hdifferent
          exact hfailure.2 (Or.inr ⟨support, leaf, ⟨hs, hsupport⟩,
            ⟨hl, hdifferent⟩, ha, hb⟩)
        refine ⟨support, ⟨ha, hs, ?_⟩, ⟨hleaf ▸ hb, hselected, ?_⟩⟩
        · intro neighbor hneighbor hneighborEdge
          exact nonadjacent_witness_unique_neighbor adjacency selection deleted outside
            neighbor support hfailure hedge hneighbor hs hneighborEdge ha
        · intro neighbor hneighbor hneighborEdge
          apply Classical.byContradiction
          intro hdifferent
          exact hfailure.2 (Or.inr ⟨support, neighbor, ⟨hs, hsupport⟩,
            ⟨hneighbor, hdifferent⟩, ha, hneighborEdge⟩)
  · intro hshape
    refine ⟨houtside, ?_⟩
    intro hcovered
    rcases hshape with honly | ⟨_, other, hother, hotherDifferent, _, hneighbors, hleaves⟩ |
      ⟨_, support, houtsideOnly, hsupportOnly⟩
    · rcases hcovered with ⟨first, _, hf, _, _, ha, _⟩ |
        ⟨center, _, hc, _, ha, _⟩
      · exact hf.2 (honly.2.2 first hf.1 ha)
      · exact hc.2 (honly.2.2 center hc.1 ha)
    · rcases hcovered with ⟨first, second, hf, hs, hne, ha, hb⟩ |
        ⟨center, leaf, hc, hl, ha, hb⟩
      · have hfirst : first = other := (hneighbors first hf.1 ha).resolve_left hf.2
        have hsecond : second = other := (hneighbors second hs.1 hb).resolve_left hs.2
        exact hne (hfirst.trans hsecond.symm)
      · have hcenter : center = other := (hneighbors center hc.1 ha).resolve_left hc.2
        exact hl.2 (hleaves leaf hl.1 (hcenter ▸ hb))
    · rcases hcovered with ⟨first, second, hf, hs, hne, ha, hb⟩ |
        ⟨center, leaf, hc, hl, ha, hb⟩
      · have hfirst := houtsideOnly.2.2 first hf.1 ha
        have hsecond := houtsideOnly.2.2 second hs.1 hb
        exact hne (hfirst.trans hsecond.symm)
      · have hcenter := houtsideOnly.2.2 center hc.1 ha
        exact hl.2 (hsupportOnly.2.2 leaf hl.1 (hcenter ▸ hb))

theorem protected_port_returns {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection block core : Vertex → Prop)
    (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hminimal : Minimal adjacency selection) (port exit : Vertex)
    (hhigh : High adjacency selection port) (hexit : core exit)
    (hboundary : ∀ neighbor, adjacency port neighbor → ¬ block neighbor → neighbor = exit)
    (hprotectedOmitted : ∀ outside, block outside → ¬ selection outside →
      adjacency outside port →
      TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ port) outside)
    (hprotectedSelected : ∀ neighbor, block neighbor → selection neighbor →
      adjacency port neighbor → ∃ replacement, selection replacement ∧
        replacement ≠ port ∧ adjacency neighbor replacement)
    (hexitNeighbors : ∀ vertex, adjacency exit vertex → vertex ≠ port → core vertex) :
    ∃ outside, core outside ∧ Failure adjacency selection port outside ∧
      (outside = exit ∨ (¬ adjacency outside port ∧
        OnlyNeighbor adjacency selection outside exit ∧
        OnlyNeighbor adjacency selection exit port)) := by
  classical
  obtain ⟨outside, hfailure⟩ := high_has_failure adjacency selection
    hirreflexive hminimal port hhigh
  by_cases hedge : adjacency outside port
  · have hexternal : ¬ block outside := by
      intro hinternal
      exact hfailure.2 (hprotectedOmitted outside hinternal hfailure.1 hedge)
    have hequal := hboundary outside (hsymmetric _ _ hedge) hexternal
    exact ⟨outside, hequal ▸ hexit, hfailure, Or.inl hequal⟩
  · have hshape := (failure_iff_shapes adjacency selection hminimal.1 port outside
      hhigh.1 hfailure.1).mp hfailure
    rcases hshape with honly | ⟨hadjacent, _⟩ | ⟨_, support, houtsideOnly, hsupportOnly⟩
    · exact False.elim (hedge honly.1)
    · exact False.elim (hedge hadjacent)
    · have hexternal : ¬ block support := by
        intro hinternal
        obtain ⟨replacement, hr, hne, ha⟩ := hprotectedSelected support hinternal
          houtsideOnly.2.1 (hsymmetric _ _ hsupportOnly.1)
        exact hne (hsupportOnly.2.2 replacement hr ha)
      have hequal := hboundary support (hsymmetric _ _ hsupportOnly.1) hexternal
      subst support
      have hdifferent : outside ≠ port := fun hequal => hfailure.1 (hequal ▸ hhigh.1)
      have hcore := hexitNeighbors outside (hsymmetric _ _ houtsideOnly.1) hdifferent
      exact ⟨outside, hcore, hfailure, Or.inr ⟨hedge, houtsideOnly, hsupportOnly⟩⟩

theorem return_witness_unique {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hforms : Forms adjacency selection) (first second outside : Vertex)
    (hfirst : High adjacency selection first) (hsecond : High adjacency selection second)
    (hfailureFirst : Failure adjacency selection first outside)
    (hfailureSecond : Failure adjacency selection second outside) : first = second := by
  exact failure_witnesses_disjoint adjacency selection hforms first second outside
    hfirst hsecond hfailureFirst hfailureSecond

theorem other_high_cannot_touch_return {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (port other outside : Vertex) (hdifferent : other ≠ port)
    (hhigh : High adjacency selection other)
    (hfailure : Failure adjacency selection port outside) :
    ¬ adjacency outside other := by
  intro hedge
  exact hfailure.2 (adjacent_high_survives adjacency selection other port outside
    hhigh hdifferent hedge)

end D5.S3.Combinatorics.Graph.StarForming.PortReturn
