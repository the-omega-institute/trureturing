/- GID: D5/S3/Combinatorics/Graph/StarForming/CoverStability
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CoverStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.CoverPullback

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/CoverStability.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.CoverPullback

open D5.S3.Combinatorics.Graph.StarForming.Regular

def Crossed {Vertex : Type} (selection : Vertex → Prop) (deleted first second : Vertex) : Prop :=
  (first = deleted ∧ ¬ selection second) ∨ (second = deleted ∧ ¬ selection first)

def CanonicalAdj {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (deleted : Vertex) (first second : Vertex × Bool) : Prop :=
  adjacency first.1 second.1 ∧
    ((Crossed selection deleted first.1 second.1 ∧ first.2 ≠ second.2) ∨
      (¬ Crossed selection deleted first.1 second.1 ∧ first.2 = second.2))

theorem canonical_symmetric {Vertex : Type} {adjacency : Vertex → Vertex → Prop}
    {selection : Vertex → Prop} (deleted : Vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first) :
    ∀ first second, CanonicalAdj adjacency selection deleted first second →
      CanonicalAdj adjacency selection deleted second first := by
  intro first second hedge
  refine ⟨hsymmetric _ _ hedge.1, ?_⟩
  rcases hedge.2 with ⟨hcrossed, hne⟩ | ⟨huncrossed, hequal⟩
  · exact Or.inl ⟨Or.symm hcrossed, Ne.symm hne⟩
  · exact Or.inr ⟨fun hs => huncrossed (Or.symm hs), hequal.symm⟩

theorem canonical_cover {Vertex : Type} {adjacency : Vertex → Vertex → Prop}
    {selection : Vertex → Prop} (deleted : Vertex) :
    NeighborhoodCover adjacency (CanonicalAdj adjacency selection deleted) Prod.fst := by
  classical
  refine ⟨fun _ _ hedge => hedge.1, ?_, ?_⟩
  · intro vertex neighbor hedge
    by_cases hcrossed : Crossed selection deleted vertex.1 neighbor
    · refine ⟨(neighbor, !vertex.2), ⟨hedge, Or.inl ⟨hcrossed, ?_⟩⟩, rfl⟩
      cases vertex.2 <;> simp
    · exact ⟨(neighbor, vertex.2), ⟨hedge, Or.inr ⟨hcrossed, rfl⟩⟩, rfl⟩
  · intro vertex first second hfirst hsecond himage
    rcases vertex with ⟨base, sheet⟩
    rcases first with ⟨firstBase, firstSheet⟩
    rcases second with ⟨secondBase, secondSheet⟩
    change firstBase = secondBase at himage
    subst secondBase
    by_cases hcrossed : Crossed selection deleted base firstBase
    all_goals cases sheet <;> cases firstSheet <;> cases secondSheet <;>
      simp_all [CanonicalAdj]

theorem canonical_selected_edge {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (deleted first second : Vertex) (sheet : Bool)
    (hfirst : selection first) (hsecond : selection second) (hedge : adjacency first second) :
    CanonicalAdj adjacency selection deleted (first, sheet) (second, sheet) := by
  refine ⟨hedge, Or.inr ⟨?_, rfl⟩⟩
  rintro (⟨_, hnot⟩ | ⟨_, hnot⟩)
  · exact hnot hsecond
  · exact hnot hfirst

theorem canonical_retained_edge {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (deleted outside selected : Vertex) (sheet : Bool)
    (hselected : selection selected) (hdifferent : selected ≠ deleted)
    (hedge : adjacency outside selected) :
    CanonicalAdj adjacency selection deleted (outside, sheet) (selected, sheet) := by
  refine ⟨hedge, Or.inr ⟨?_, rfl⟩⟩
  rintro (⟨_, hnot⟩ | ⟨hequal, _⟩)
  · exact hnot hselected
  · exact hdifferent hequal

theorem twoAt_canonical_after_deletion {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (deleted outside : Vertex) (sheet : Bool)
    (hstar : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) outside) :
    TwoAt (CanonicalAdj adjacency selection deleted)
      (fun vertex => selection vertex.1 ∧ vertex ≠ (deleted, false)) (outside, sheet) := by
  have retained : ∀ vertex, selection vertex ∧ vertex ≠ deleted →
      selection (vertex, sheet).1 ∧ (vertex, sheet) ≠ (deleted, false) := by
    intro vertex hselected
    exact ⟨hselected.1, fun hequal => hselected.2 (congrArg Prod.fst hequal)⟩
  rcases hstar with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · exact Or.inl ⟨(first, sheet), (second, sheet), retained first hf, retained second hs,
      (fun hequal => hne (congrArg Prod.fst hequal)),
      canonical_retained_edge deleted outside first sheet hf.1 hf.2 ha,
      canonical_retained_edge deleted outside second sheet hs.1 hs.2 hb⟩
  · exact Or.inr ⟨(center, sheet), (leaf, sheet), retained center hc, retained leaf hl,
      canonical_retained_edge deleted outside center sheet hc.1 hc.2 ha,
      canonical_retained_edge deleted center leaf sheet hl.1 hl.2 hb⟩

theorem canonical_deletion_forms_of_missing_certificate {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (deleted : Vertex) (hselected : selection deleted)
    (hmissing : ¬ ((¬ TwoAt adjacency
        (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) ∨
      ∃ outside, SafeFailure adjacency selection deleted outside)) :
    Forms (CanonicalAdj adjacency selection deleted)
      (fun vertex => selection vertex.1 ∧ vertex ≠ (deleted, false)) := by
  classical
  have hself : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted := by
    apply Classical.byContradiction
    intro hnot
    exact hmissing (Or.inl hnot)
  intro outside houtside
  rcases outside with ⟨base, sheet⟩
  by_cases hbaseSelected : selection base
  · have hequal : (base, sheet) = (deleted, false) := by
      apply Classical.byContradiction
      intro hne
      exact houtside ⟨hbaseSelected, hne⟩
    exact hequal.symm ▸ twoAt_canonical_after_deletion deleted deleted false hself
  · by_cases hstar : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) base
    · exact twoAt_canonical_after_deletion deleted base sheet hstar
    · have hunsafe : ¬ (adjacency base deleted → ∀ center, selection center →
          adjacency base center → ¬ adjacency center deleted) := by
        intro hsafe
        exact hmissing (Or.inr ⟨base, ⟨⟨hbaseSelected, hstar⟩, hsafe⟩⟩)
      have hadjacent : adjacency base deleted := by
        apply Classical.byContradiction
        intro hnonadjacent
        exact hunsafe (fun hedge => False.elim (hnonadjacent hedge))
      have htriangle : ∃ center, selection center ∧ adjacency base center ∧ adjacency center deleted := by
        apply Classical.byContradiction
        intro hnone
        apply hunsafe
        intro _ center hc hedge hsupport
        exact hnone ⟨center, hc, hedge, hsupport⟩
      obtain ⟨center, hc, hbaseCenter, hcenterDeleted⟩ := htriangle
      have hdifferent : center ≠ deleted := by
        intro hequal
        exact hirreflexive deleted (hequal ▸ hcenterDeleted)
      have hcenterSelected : selection (center, true).1 ∧ (center, true) ≠ (deleted, false) :=
        ⟨hc, by simp⟩
      have hdeletedSelected : selection (deleted, true).1 ∧ (deleted, true) ≠ (deleted, false) :=
        ⟨hselected, by simp⟩
      cases sheet
      · exact Or.inr ⟨(deleted, true), (center, true), hdeletedSelected, hcenterSelected,
          ⟨hadjacent, Or.inl ⟨Or.inr ⟨rfl, hbaseSelected⟩, by simp⟩⟩,
          canonical_selected_edge deleted deleted center true hselected hc
            (hsymmetric _ _ hcenterDeleted)⟩
      · exact Or.inr ⟨(center, true), (deleted, true), hcenterSelected, hdeletedSelected,
          canonical_retained_edge deleted base center true hc hdifferent hbaseCenter,
          canonical_selected_edge deleted center deleted true hc hselected hcenterDeleted⟩

theorem canonical_nonminimal_of_missing_certificate {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (deleted : Vertex) (hselected : selection deleted)
    (hmissing : ¬ ((¬ TwoAt adjacency
        (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) ∨
      ∃ outside, SafeFailure adjacency selection deleted outside)) :
    ¬ Minimal (CanonicalAdj adjacency selection deleted) (fun vertex => selection vertex.1) := by
  intro hminimal
  apply hminimal.2 (fun vertex => selection vertex.1 ∧ vertex ≠ (deleted, false))
    (fun _ hs => hs.1) ⟨(deleted, false), hselected, fun hs => hs.2 rfl⟩
  exact canonical_deletion_forms_of_missing_certificate hirreflexive hsymmetric
    deleted hselected hmissing

theorem safe_certificates_iff_canonical_minimal {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hminimal : Minimal adjacency selection) :
    HasSafeCertificates adjacency selection ↔
      ∀ deleted, selection deleted → Minimal (CanonicalAdj adjacency selection deleted)
        (fun vertex => selection vertex.1) := by
  classical
  constructor
  · intro hcertificates deleted _
    exact minimal_pullback_of_safe_certificates (canonical_cover deleted) hirreflexive
      hsymmetric (canonical_symmetric deleted hsymmetric) hminimal.1 hcertificates
  · intro hcanonical deleted hselected
    apply Classical.byContradiction
    intro hmissing
    exact canonical_nonminimal_of_missing_certificate hirreflexive hsymmetric deleted
      hselected hmissing (hcanonical deleted hselected)

theorem safe_certificates_iff_all_covers {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (hirreflexive : ∀ vertex, ¬ adjacency vertex vertex)
    (hsymmetric : ∀ first second, adjacency first second → adjacency second first)
    (hminimal : Minimal adjacency selection) :
    HasSafeCertificates adjacency selection ↔
      ∀ (Lift : Type) (liftAdjacency : Lift → Lift → Prop) (projection : Lift → Vertex),
        NeighborhoodCover adjacency liftAdjacency projection →
        (∀ first second, liftAdjacency first second → liftAdjacency second first) →
        Minimal liftAdjacency (fun vertex => selection (projection vertex)) := by
  constructor
  · intro hcertificates Lift liftAdjacency projection cover hliftSymmetric
    exact minimal_pullback_of_safe_certificates cover hirreflexive hsymmetric
      hliftSymmetric hminimal.1 hcertificates
  · intro hstable
    apply (safe_certificates_iff_canonical_minimal hirreflexive hsymmetric hminimal).2
    intro deleted _
    exact hstable (Vertex × Bool) (CanonicalAdj adjacency selection deleted) Prod.fst
      (canonical_cover deleted) (canonical_symmetric deleted hsymmetric)

end D5.S3.Combinatorics.Graph.StarForming.CoverPullback
