/- GID: D5/S3/Combinatorics/Graph/StarForming/CoverPullback
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CoverPullback
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularBound

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/CoverPullback.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.CoverPullback

open D5.S3.Combinatorics.Graph.StarForming.Regular

def TriangleFree {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Prop :=
  ∀ first second third, adjacency first second → adjacency second third →
    adjacency third first → False

def SafeFailure {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (deleted outside : Vertex) : Prop :=
  Failure adjacency selection deleted outside ∧
    (adjacency outside deleted → ∀ center, selection center →
      adjacency outside center → ¬ adjacency center deleted)

def HasSafeCertificates {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) : Prop :=
  ∀ deleted, selection deleted →
    (¬ TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted) ∨
    ∃ outside, SafeFailure adjacency selection deleted outside

def BoundaryTriangleFree {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) : Prop :=
  ∀ outside first second, ¬ selection outside → selection first → selection second →
    adjacency outside first → adjacency outside second → ¬ adjacency first second

structure NeighborhoodCover {Base Lift : Type}
    (baseAdjacency : Base → Base → Prop) (liftAdjacency : Lift → Lift → Prop)
    (projection : Lift → Base) : Prop where
  map_edge : ∀ first second, liftAdjacency first second →
    baseAdjacency (projection first) (projection second)
  neighbor_surjective : ∀ vertex neighbor, baseAdjacency (projection vertex) neighbor →
    ∃ lifted, liftAdjacency vertex lifted ∧ projection lifted = neighbor
  neighbor_injective : ∀ vertex first second,
    liftAdjacency vertex first → liftAdjacency vertex second →
    projection first = projection second → first = second

theorem twoAt_mono {Vertex : Type} {adjacency : Vertex → Vertex → Prop}
    {smaller larger : Vertex → Prop} {outside : Vertex}
    (hinclusion : ∀ vertex, smaller vertex → larger vertex)
    (hstar : TwoAt adjacency smaller outside) : TwoAt adjacency larger outside := by
  rcases hstar with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · exact Or.inl ⟨first, second, hinclusion _ hf, hinclusion _ hs, hne, ha, hb⟩
  · exact Or.inr ⟨center, leaf, hinclusion _ hc, hinclusion _ hl, ha, hb⟩

theorem forms_mono {Vertex : Type} {adjacency : Vertex → Vertex → Prop}
    {smaller larger : Vertex → Prop}
    (hinclusion : ∀ vertex, smaller vertex → larger vertex)
    (hforms : Forms adjacency smaller) : Forms adjacency larger := by
  intro outside houtside
  exact twoAt_mono hinclusion (hforms outside (fun hs => houtside (hinclusion _ hs)))

theorem minimal_of_single_deletions {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (hforms : Forms adjacency selection)
    (hdeletions : ∀ deleted, selection deleted →
      ¬ Forms adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted)) :
    Minimal adjacency selection := by
  refine ⟨hforms, ?_⟩
  intro smaller hinclusion hproper hsmaller
  obtain ⟨deleted, hselected, hmissing⟩ := hproper
  apply hdeletions deleted hselected
  apply forms_mono (larger := fun vertex => selection vertex ∧ vertex ≠ deleted) ?_ hsmaller
  intro vertex hvertex
  refine ⟨hinclusion _ hvertex, ?_⟩
  intro hequal
  exact hmissing (hequal ▸ hvertex)

theorem twoAt_pullback {Base Lift : Type}
    {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop}
    {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection)
    {selection : Base → Prop} (outside : Lift)
    (hstar : TwoAt baseAdjacency selection (projection outside)) :
    TwoAt liftAdjacency (fun vertex => selection (projection vertex)) outside := by
  rcases hstar with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · obtain ⟨firstLift, hfirst, hfirstImage⟩ := cover.neighbor_surjective outside first ha
    obtain ⟨secondLift, hsecond, hsecondImage⟩ := cover.neighbor_surjective outside second hb
    refine Or.inl ⟨firstLift, secondLift,
      (show selection (projection firstLift) from hfirstImage.symm ▸ hf),
      (show selection (projection secondLift) from hsecondImage.symm ▸ hs),
      ?_, hfirst, hsecond⟩
    intro hequal
    exact hne (hfirstImage.symm.trans ((congrArg projection hequal).trans hsecondImage))
  · obtain ⟨centerLift, hcenter, hcenterImage⟩ := cover.neighbor_surjective outside center ha
    obtain ⟨leafLift, hleaf, hleafImage⟩ :=
      cover.neighbor_surjective centerLift leaf (hcenterImage.symm ▸ hb)
    exact Or.inr ⟨centerLift, leafLift,
      (show selection (projection centerLift) from hcenterImage.symm ▸ hc),
      (show selection (projection leafLift) from hleafImage.symm ▸ hl), hcenter, hleaf⟩

theorem forms_pullback {Base Lift : Type}
    {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop}
    {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection)
    {selection : Base → Prop} (hforms : Forms baseAdjacency selection) :
    Forms liftAdjacency (fun vertex => selection (projection vertex)) := by
  intro outside houtside
  exact twoAt_pullback cover outside (hforms _ houtside)

theorem self_deletion_projects {Base Lift : Type}
    {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop}
    {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection)
    (hirreflexive : ∀ vertex, ¬ baseAdjacency vertex vertex)
    (hsymmetric : ∀ first second, liftAdjacency first second → liftAdjacency second first)
    {selection : Base → Prop} (deleted : Lift)
    (hstar : TwoAt liftAdjacency
      (fun vertex => selection (projection vertex) ∧ vertex ≠ deleted) deleted) :
    TwoAt baseAdjacency
      (fun vertex => selection vertex ∧ vertex ≠ projection deleted) (projection deleted) := by
  have neighbor_different : ∀ vertex, liftAdjacency deleted vertex →
      projection vertex ≠ projection deleted := by
    intro vertex hedge hequal
    exact hirreflexive _ (hequal ▸ cover.map_edge _ _ hedge)
  rcases hstar with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · refine Or.inl ⟨projection first, projection second,
      ⟨hf.1, neighbor_different first ha⟩, ⟨hs.1, neighbor_different second hb⟩,
      ?_, cover.map_edge _ _ ha, cover.map_edge _ _ hb⟩
    intro hequal
    exact hne (cover.neighbor_injective deleted first second ha hb hequal)
  · refine Or.inr ⟨projection center, projection leaf,
      ⟨hc.1, neighbor_different center ha⟩, ⟨hl.1, ?_⟩,
      cover.map_edge _ _ ha, cover.map_edge _ _ hb⟩
    intro hequal
    exact hl.2 (cover.neighbor_injective center leaf deleted hb (hsymmetric _ _ ha) hequal)

theorem adjacent_deletion_projects {Base Lift : Type}
    {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop}
    {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection)
    {selection : Base → Prop} (deleted outside : Lift)
    (hadjacent : liftAdjacency outside deleted)
    (hsafe : ∀ center, selection center →
      baseAdjacency (projection outside) center → ¬ baseAdjacency center (projection deleted))
    (hstar : TwoAt liftAdjacency
      (fun vertex => selection (projection vertex) ∧ vertex ≠ deleted) outside) :
    TwoAt baseAdjacency
      (fun vertex => selection vertex ∧ vertex ≠ projection deleted) (projection outside) := by
  have neighbor_different : ∀ vertex,
      selection (projection vertex) ∧ vertex ≠ deleted → liftAdjacency outside vertex →
      projection vertex ≠ projection deleted := by
    intro vertex hselected hedge hequal
    exact hselected.2 (cover.neighbor_injective outside vertex deleted hedge hadjacent hequal)
  rcases hstar with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · refine Or.inl ⟨projection first, projection second,
      ⟨hf.1, neighbor_different first hf ha⟩, ⟨hs.1, neighbor_different second hs hb⟩,
      ?_, cover.map_edge _ _ ha, cover.map_edge _ _ hb⟩
    intro hequal
    exact hne (cover.neighbor_injective outside first second ha hb hequal)
  · refine Or.inr ⟨projection center, projection leaf,
      ⟨hc.1, neighbor_different center hc ha⟩, ⟨hl.1, ?_⟩,
      cover.map_edge _ _ ha, cover.map_edge _ _ hb⟩
    intro hequal
    exact hsafe (projection center) hc.1
      (cover.map_edge _ _ ha) (hequal ▸ cover.map_edge _ _ hb)

theorem nonadjacent_failure_private_path {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (hforms : Forms adjacency selection) (deleted outside : Vertex)
    (hfailure : Failure adjacency selection deleted outside)
    (hnonadjacent : ¬ adjacency outside deleted) :
    ∃ support, selection support ∧ adjacency outside support ∧ adjacency support deleted ∧
      (∀ neighbor, selection neighbor → adjacency outside neighbor → neighbor = support) ∧
      (∀ neighbor, selection neighbor → adjacency support neighbor → neighbor = deleted) := by
  classical
  rcases hforms outside hfailure.1 with ⟨first, second, hf, hs, hne, ha, hb⟩ |
    ⟨center, leaf, hc, hl, ha, hb⟩
  · have hfirst : first ≠ deleted := fun heq => hnonadjacent (heq ▸ ha)
    have hsecond : second ≠ deleted := fun heq => hnonadjacent (heq ▸ hb)
    exact False.elim (hfailure.2
      (Or.inl ⟨first, second, ⟨hf, hfirst⟩, ⟨hs, hsecond⟩, hne, ha, hb⟩))
  · have hcenter : center ≠ deleted := fun heq => hnonadjacent (heq ▸ ha)
    have hleaf : leaf = deleted := by
      apply Classical.byContradiction
      intro hne
      exact hfailure.2 (Or.inr ⟨center, leaf, ⟨hc, hcenter⟩, ⟨hl, hne⟩, ha, hb⟩)
    refine ⟨center, hc, ha, hleaf ▸ hb, ?_, ?_⟩
    · intro neighbor hneighbor hedge
      exact nonadjacent_witness_unique_neighbor adjacency selection deleted outside neighbor center
        hfailure hnonadjacent hneighbor hc hedge ha
    · intro neighbor hneighbor hedge
      apply Classical.byContradiction
      intro hne
      exact hfailure.2 (Or.inr ⟨center, neighbor, ⟨hc, hcenter⟩,
        ⟨hneighbor, hne⟩, ha, hedge⟩)

theorem private_path_deletion_fails {Base Lift : Type}
    {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop}
    {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection)
    {selection : Base → Prop} (deleted support outside : Lift)
    (houtside : ¬ selection (projection outside))
    (houtsideSupport : liftAdjacency outside support)
    (hsupportDeleted : liftAdjacency support deleted)
    (huniqueOutside : ∀ neighbor, selection neighbor →
      baseAdjacency (projection outside) neighbor → neighbor = projection support)
    (huniqueSupport : ∀ neighbor, selection neighbor →
      baseAdjacency (projection support) neighbor → neighbor = projection deleted) :
    ¬ Forms liftAdjacency
      (fun vertex => selection (projection vertex) ∧ vertex ≠ deleted) := by
  intro hforms
  have hunique : ∀ neighbor, selection (projection neighbor) →
      liftAdjacency outside neighbor → neighbor = support := by
    intro neighbor hselected hedge
    exact cover.neighbor_injective outside neighbor support hedge houtsideSupport
      (huniqueOutside _ hselected (cover.map_edge _ _ hedge))
  rcases hforms outside (fun hs => houtside hs.1) with
    ⟨first, second, hf, hs, hne, ha, hb⟩ | ⟨center, leaf, hc, hl, ha, hb⟩
  · exact hne ((hunique first hf.1 ha).trans (hunique second hs.1 hb).symm)
  · have hcenter : center = support := hunique center hc.1 ha
    have hleafEdge : liftAdjacency support leaf := hcenter ▸ hb
    exact hl.2 (cover.neighbor_injective support leaf deleted hleafEdge hsupportDeleted
      (huniqueSupport _ hl.1 (cover.map_edge _ _ hleafEdge)))

theorem minimal_pullback_of_safe_certificates {Base Lift : Type}
    {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop}
    {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection)
    (hirreflexive : ∀ vertex, ¬ baseAdjacency vertex vertex)
    (hbaseSymmetric : ∀ first second, baseAdjacency first second → baseAdjacency second first)
    (hliftSymmetric : ∀ first second, liftAdjacency first second → liftAdjacency second first)
    {selection : Base → Prop} (hforms : Forms baseAdjacency selection)
    (hcertificates : HasSafeCertificates baseAdjacency selection) :
    Minimal liftAdjacency (fun vertex => selection (projection vertex)) := by
  classical
  apply minimal_of_single_deletions (forms_pullback cover hforms)
  intro deleted hselected
  rcases hcertificates (projection deleted) hselected with hself | ⟨outside, hfailure, hsafe⟩
  · intro hliftForms
    apply hself
    apply self_deletion_projects cover hirreflexive hliftSymmetric deleted
    exact hliftForms deleted (fun hs => hs.2 rfl)
  ·
    by_cases hadjacent : baseAdjacency outside (projection deleted)
    · obtain ⟨outsideLift, hedge, himage⟩ := cover.neighbor_surjective deleted outside
        (hbaseSymmetric _ _ hadjacent)
      intro hliftForms
      have houtside : ¬ selection (projection outsideLift) := himage.symm ▸ hfailure.1
      have hstar := hliftForms outsideLift (fun hs => houtside hs.1)
      have hprojected := adjacent_deletion_projects cover deleted outsideLift
        (hliftSymmetric _ _ hedge)
        (by simpa only [himage] using hsafe hadjacent) hstar
      exact hfailure.2 (himage ▸ hprojected)
    · obtain ⟨support, hs, houtsideSupport, hsupportDeleted, huniqueOutside, huniqueSupport⟩ :=
        nonadjacent_failure_private_path hforms (projection deleted) outside hfailure hadjacent
      obtain ⟨supportLift, hsEdge, hsImage⟩ := cover.neighbor_surjective deleted support
        (hbaseSymmetric _ _ hsupportDeleted)
      obtain ⟨outsideLift, hoEdge, hoImage⟩ := cover.neighbor_surjective supportLift outside
        (hsImage.symm ▸ hbaseSymmetric _ _ houtsideSupport)
      apply private_path_deletion_fails cover deleted supportLift outsideLift
        (hoImage.symm ▸ hfailure.1) (hliftSymmetric _ _ hoEdge) (hliftSymmetric _ _ hsEdge)
      · intro neighbor hneighbor hedge
        exact (huniqueOutside neighbor hneighbor (hoImage ▸ hedge)).trans hsImage.symm
      · intro neighbor hneighbor hedge
        exact huniqueSupport neighbor hneighbor (hsImage ▸ hedge)

theorem safe_certificates_of_boundary_triangle_free {Vertex : Type}
    {adjacency : Vertex → Vertex → Prop} {selection : Vertex → Prop}
    (hminimal : Minimal adjacency selection)
    (hboundary : BoundaryTriangleFree adjacency selection) :
    HasSafeCertificates adjacency selection := by
  classical
  intro deleted hselected
  by_cases hself : TwoAt adjacency (fun vertex => selection vertex ∧ vertex ≠ deleted) deleted
  · obtain ⟨outside, hfailure⟩ := covered_deletion_has_failure adjacency selection
      hminimal deleted hselected hself
    refine Or.inr ⟨outside, hfailure, ?_⟩
    intro hadjacent center hc hedge
    exact hboundary outside center deleted hfailure.1 hc hselected hedge hadjacent
  · exact Or.inl hself

theorem minimal_pullback_of_boundary_triangle_free {Base Lift : Type}
    {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop}
    {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection)
    (hirreflexive : ∀ vertex, ¬ baseAdjacency vertex vertex)
    (hbaseSymmetric : ∀ first second, baseAdjacency first second → baseAdjacency second first)
    (hliftSymmetric : ∀ first second, liftAdjacency first second → liftAdjacency second first)
    {selection : Base → Prop} (hminimal : Minimal baseAdjacency selection)
    (hboundary : BoundaryTriangleFree baseAdjacency selection) :
    Minimal liftAdjacency (fun vertex => selection (projection vertex)) := by
  exact minimal_pullback_of_safe_certificates cover hirreflexive hbaseSymmetric hliftSymmetric
    hminimal.1 (safe_certificates_of_boundary_triangle_free hminimal hboundary)

theorem minimal_pullback {Base Lift : Type}
    {baseAdjacency : Base → Base → Prop} {liftAdjacency : Lift → Lift → Prop}
    {projection : Lift → Base} (cover : NeighborhoodCover baseAdjacency liftAdjacency projection)
    (hirreflexive : ∀ vertex, ¬ baseAdjacency vertex vertex)
    (hbaseSymmetric : ∀ first second, baseAdjacency first second → baseAdjacency second first)
    (hliftSymmetric : ∀ first second, liftAdjacency first second → liftAdjacency second first)
    (htriangleFree : TriangleFree baseAdjacency)
    {selection : Base → Prop} (hminimal : Minimal baseAdjacency selection) :
    Minimal liftAdjacency (fun vertex => selection (projection vertex)) := by
  apply minimal_pullback_of_boundary_triangle_free cover hirreflexive hbaseSymmetric
    hliftSymmetric hminimal
  intro outside first second _ _ _ hfirst hsecond hedge
  exact htriangleFree outside first second hfirst hedge (hbaseSymmetric _ _ hsecond)

end D5.S3.Combinatorics.Graph.StarForming.CoverPullback
