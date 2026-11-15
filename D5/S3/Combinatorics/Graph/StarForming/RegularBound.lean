/- GID: D5/S3/Combinatorics/Graph/StarForming/RegularBound
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/RegularBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import Std

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/RegularBound.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.Regular

def TwoAt {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (outside : Vertex) : Prop :=
  (∃ first second, selection first ∧ selection second ∧ first ≠ second ∧
    adjacency outside first ∧ adjacency outside second) ∨
  (∃ center leaf, selection center ∧ selection leaf ∧
    adjacency outside center ∧ adjacency center leaf)

def Forms {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) : Prop :=
  ∀ outside, ¬ selection outside → TwoAt adjacency selection outside

def Minimal {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) : Prop :=
  Forms adjacency selection ∧ ∀ smaller : Vertex → Prop,
    (∀ vertex, smaller vertex → selection vertex) →
    (∃ vertex, selection vertex ∧ ¬ smaller vertex) → ¬ Forms adjacency smaller

def High {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (vertex : Vertex) : Prop :=
  selection vertex ∧ ∃ first second, selection first ∧ selection second ∧
    first ≠ second ∧ adjacency vertex first ∧ adjacency vertex second

def Failure {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (deleted outside : Vertex) : Prop :=
  ¬ selection outside ∧
    ¬ TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside

theorem covered_deletion_has_failure {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hminimal : Minimal adjacency selection) (deleted : Vertex)
    (hselected : selection deleted)
    (hnew : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) :
    ∃ outside, Failure adjacency selection deleted outside := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hforms : Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) := by
    intro outside houtside
    by_cases hequal : outside = deleted
    · exact hequal ▸ hnew
    · have hold : ¬ selection outside := fun hs => houtside ⟨hs, hequal⟩
      apply Classical.byContradiction
      intro hfailure
      exact hnone ⟨outside, hold, hfailure⟩
  exact hminimal.2 _ (fun _ hvertex => hvertex.1)
    ⟨deleted, hselected, fun hvertex => hvertex.2 rfl⟩ hforms

theorem high_has_failure {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex)
    (hminimal : Minimal adjacency selection) (deleted : Vertex)
    (hhigh : High adjacency selection deleted) :
    ∃ outside, Failure adjacency selection deleted outside := by
  classical
  apply Classical.byContradiction
  intro hnone
  have hforms : Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) := by
    intro outside houtside
    by_cases hequal : outside = deleted
    · subst outside
      obtain ⟨first, second, hf, hs, hne, ha, hb⟩ := hhigh.2
      have hfirst : first ≠ deleted := by
        intro hsame
        subst first
        exact hirreflexive deleted ha
      have hsecond : second ≠ deleted := by
        intro hsame
        subst second
        exact hirreflexive deleted hb
      exact Or.inl ⟨first, second, ⟨hf, hfirst⟩, ⟨hs, hsecond⟩, hne, ha, hb⟩
    · have hold : ¬ selection outside := fun hs => houtside ⟨hs, hequal⟩
      apply Classical.byContradiction
      intro hfailure
      exact hnone ⟨outside, hold, hfailure⟩
  exact hminimal.2 _ (fun _ hvertex => hvertex.1)
    ⟨deleted, hhigh.1, fun hvertex => hvertex.2 rfl⟩ hforms

theorem adjacent_high_survives {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (center deleted outside : Vertex) (hhigh : High adjacency selection center)
    (hdifferent : center ≠ deleted) (hedge : adjacency outside center) :
    TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside := by
  classical
  obtain ⟨first, second, hf, hs, hne, ha, hb⟩ := hhigh.2
  by_cases hfirst : first = deleted
  · have hsecond : second ≠ deleted := fun heq => hne (hfirst.trans heq.symm)
    exact Or.inr ⟨center, second, ⟨hhigh.1, hdifferent⟩, ⟨hs, hsecond⟩, hedge, hb⟩
  · exact Or.inr ⟨center, first, ⟨hhigh.1, hdifferent⟩, ⟨hf, hfirst⟩, hedge, ha⟩

theorem selected_leaf_has_private_witness {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hminimal : Minimal adjacency selection)
    (hnoisolates : ∀ vertex, selection vertex → ∃ neighbor, selection neighbor ∧ adjacency vertex neighbor)
    (leaf support : Vertex) (hleaf : selection leaf)
    (hhigh : High adjacency selection support) (hsupport : adjacency leaf support)
    (hunique : ∀ neighbor, selection neighbor → adjacency leaf neighbor → neighbor = support) :
    ∃ outside, Failure adjacency selection leaf outside ∧ adjacency outside leaf ∧
      ∀ neighbor, selection neighbor → adjacency outside neighbor → neighbor = leaf := by
  classical
  have hdifferent : support ≠ leaf := by
    intro hequal
    exact hirreflexive leaf (hequal ▸ hsupport)
  have hnew := adjacent_high_survives adjacency selection support leaf leaf
    hhigh hdifferent hsupport
  obtain ⟨outside, hfailure⟩ :=
    covered_deletion_has_failure adjacency selection hminimal leaf hleaf hnew
  have hadjacent : adjacency outside leaf := by
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
  refine ⟨outside, hfailure, hadjacent, ?_⟩
  intro neighbor hneighbor hedge
  apply Classical.byContradiction
  intro hne
  apply hfailure.2
  obtain ⟨endpoint, he, ha⟩ := hnoisolates neighbor hneighbor
  by_cases hendpoint : endpoint = leaf
  · have hequal : neighbor = support :=
      hunique neighbor hneighbor (hsymmetric _ _ (hendpoint ▸ ha))
    exact adjacent_high_survives adjacency selection support leaf outside
      hhigh hdifferent (hequal ▸ hedge)
  · exact Or.inr ⟨neighbor, endpoint, ⟨hneighbor, hne⟩, ⟨he, hendpoint⟩, hedge, ha⟩

theorem failure_witnesses_disjoint {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (hforms : Forms adjacency selection) (first second outside : Vertex)
    (hfirst : High adjacency selection first) (hsecond : High adjacency selection second)
    (hfailureFirst : Failure adjacency selection first outside)
    (hfailureSecond : Failure adjacency selection second outside) : first = second := by
  classical
  apply Classical.byContradiction
  intro hdifferent
  have hnotFirst : ¬ adjacency outside first := by
    intro hedge
    exact hfailureSecond.2
      (adjacent_high_survives adjacency selection first second outside hfirst hdifferent hedge)
  have hnotSecond : ¬ adjacency outside second := by
    intro hedge
    exact hfailureFirst.2
      (adjacent_high_survives adjacency selection second first outside hsecond
        (fun heq => hdifferent heq.symm) hedge)
  rcases hforms outside hfailureFirst.1 with ⟨left, right, hl, hr, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · have hleft : left ≠ first := fun heq => hnotFirst (heq ▸ ha)
    have hright : right ≠ first := fun heq => hnotFirst (heq ▸ hb)
    exact hfailureFirst.2 (Or.inl ⟨left, right, ⟨hl, hleft⟩, ⟨hr, hright⟩, hne, ha, hb⟩)
  · have hcenter : center ≠ first := fun heq => hnotFirst (heq ▸ ha)
    by_cases hleaf : leaf = first
    · have hcenterSecond : center ≠ second := fun heq => hnotSecond (heq ▸ ha)
      have hleafSecond : leaf ≠ second := fun heq => hdifferent (hleaf.symm.trans heq)
      exact hfailureSecond.2
        (Or.inr ⟨center, leaf, ⟨hc, hcenterSecond⟩, ⟨hl, hleafSecond⟩, ha, hb⟩)
    · exact hfailureFirst.2 (Or.inr ⟨center, leaf, ⟨hc, hcenter⟩, ⟨hl, hleaf⟩, ha, hb⟩)

theorem witness_has_no_three_neighbors {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (deleted outside first second third : Vertex)
    (hfailure : Failure adjacency selection deleted outside)
    (hf : selection first) (hs : selection second) (ht : selection third)
    (hfs : first ≠ second) (hft : first ≠ third) (hst : second ≠ third)
    (ha : adjacency outside first) (hb : adjacency outside second)
    (hc : adjacency outside third) : False := by
  classical
  apply hfailure.2
  by_cases hfirst : first = deleted
  · have hsecond : second ≠ deleted := fun heq => hfs (hfirst.trans heq.symm)
    have hthird : third ≠ deleted := fun heq => hft (hfirst.trans heq.symm)
    exact Or.inl ⟨second, third, ⟨hs, hsecond⟩, ⟨ht, hthird⟩, hst, hb, hc⟩
  · by_cases hsecond : second = deleted
    · have hthird : third ≠ deleted := fun heq => hst (hsecond.trans heq.symm)
      exact Or.inl ⟨first, third, ⟨hf, hfirst⟩, ⟨ht, hthird⟩, hft, ha, hc⟩
    · exact Or.inl ⟨first, second, ⟨hf, hfirst⟩, ⟨hs, hsecond⟩, hfs, ha, hb⟩

theorem nonadjacent_witness_unique_neighbor {Vertex : Type}
    (adjacency : Vertex → Vertex → Prop) (selection : Vertex → Prop)
    (deleted outside first second : Vertex)
    (hfailure : Failure adjacency selection deleted outside)
    (hnonadjacent : ¬ adjacency outside deleted)
    (hf : selection first) (hs : selection second)
    (ha : adjacency outside first) (hb : adjacency outside second) : first = second := by
  apply Classical.byContradiction
  intro hne
  have hfirst : first ≠ deleted := fun heq => hnonadjacent (heq ▸ ha)
  have hsecond : second ≠ deleted := fun heq => hnonadjacent (heq ▸ hb)
  exact hfailure.2 (Or.inl ⟨first, second, ⟨hf, hfirst⟩, ⟨hs, hsecond⟩, hne, ha, hb⟩)

theorem witness_capacity (maximum selectedDegree outsideDegree : Nat) (adjacent : Prop)
    (hselected : selectedDegree ≤ maximum)
    (houtside : outsideDegree ≤ 2)
    (hadjacent : adjacent → selectedDegree + 1 ≤ maximum)
    (hnonadjacent : ¬ adjacent → outsideDegree ≤ 1) :
    selectedDegree + outsideDegree ≤ maximum + 1 := by
  classical
  by_cases hedge : adjacent
  · have hbound := hadjacent hedge
    omega
  · have hbound := hnonadjacent hedge
    omega

end D5.S3.Combinatorics.Graph.StarForming.Regular
