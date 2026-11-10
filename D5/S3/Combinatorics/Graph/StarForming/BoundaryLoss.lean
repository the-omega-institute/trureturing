/- GID: D5/S3/Combinatorics/Graph/StarForming/BoundaryLoss
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/BoundaryLoss
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.PrivateClauses

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/BoundaryLoss.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.BoundaryLoss

open D5.S3.Combinatorics.Graph.StarForming.Regular D5.S3.Combinatorics.Graph.StarForming.PrivateClauses

def ExportWitness {Vertex : Type} (inside ambient : Vertex → Vertex → Prop)
    (core port selection : Vertex → Prop) (candidate boundary outside : Vertex) : Prop :=
  core boundary ∧ port boundary ∧ selection boundary ∧
    inside boundary candidate ∧ ambient outside boundary ∧ ¬ inside outside boundary ∧
    (∀ vertex, core vertex → selection vertex → inside boundary vertex → vertex = candidate) ∧
    ¬ selection outside ∧
    (∀ vertex, ambient outside vertex → selection vertex → vertex = boundary)

theorem unsupported_has_export {Vertex : Type}
    (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop)
    (hinclusion : ∀ first second, inside first second → ambient first second)
    (hinside : ∀ first second, inside first second → core first ∧ core second)
    (hsymmInside : ∀ first second, inside first second → inside second first)
    (hsymmAmbient : ∀ first second, ambient first second → ambient second first)
    (hunchanged : ∀ vertex, core vertex → ¬ port vertex →
      ∀ neighbor, ambient vertex neighbor → inside vertex neighbor)
    (hminimal : Minimal ambient selection) (candidate : Vertex)
    (hcore : core candidate) (hnonport : ¬ port candidate) (hselected : selection candidate)
    (hunsupported : ¬ ∃ clause,
      Private inside (fun vertex => core vertex ∧ selection vertex) clause candidate) :
    ∃ boundary outside, ExportWitness inside ambient core port selection candidate boundary outside := by
  classical
  obtain ⟨globalClause, hvalid, hsupport, hunique⟩ :=
    ((minimal_iff_private ambient selection).mp hminimal).2 candidate hselected
  have hlocalEdge : ∀ neighbor, ambient neighbor candidate → inside neighbor candidate := by
    intro neighbor hedge
    exact hsymmInside _ _ (hunchanged candidate hcore hnonport neighbor
      (hsymmAmbient _ _ hedge))
  have hprivate : ∀ localClause, Valid inside localClause →
      Support inside localClause candidate →
      (∀ vertex, core vertex ∧ selection vertex → Support inside localClause vertex →
        Support ambient globalClause vertex) → False := by
    intro localClause hvalidLocal hsupportLocal htransfer
    apply hunsupported
    refine ⟨localClause, hvalidLocal, hsupportLocal, ?_⟩
    intro vertex hchosen hlocalSupport
    exact hunique vertex hchosen.2 (htransfer vertex hchosen hlocalSupport)
  cases globalClause with
  | closed center =>
    apply False.elim
    apply hprivate (.closed center) trivial
    · rcases hsupport with hequal | hedge
      · exact Or.inl hequal
      · exact Or.inr (hlocalEdge center hedge)
    · exact fun vertex _ hlocalSupport =>
        support_mono inside ambient hinclusion _ vertex hlocalSupport
  | oriented center neighbor =>
    rcases hsupport with hequal | ⟨hedge, hdifferent⟩ | ⟨hedge, hdifferent⟩
    · apply False.elim
      have holdEdge : inside center neighbor := by
        rw [← hequal]
        exact hunchanged candidate hcore hnonport neighbor (hequal ▸ hvalid)
      exact hprivate (.oriented center neighbor) holdEdge (Or.inl hequal)
        (fun vertex _ hlocalSupport => support_mono inside ambient hinclusion _ vertex hlocalSupport)
    · apply False.elim
      have hcandidateEdge := hlocalEdge center hedge
      by_cases holdEdge : inside center neighbor
      · exact hprivate (.oriented center neighbor) holdEdge
          (Or.inr (Or.inl ⟨hcandidateEdge, hdifferent⟩))
          (fun vertex _ hlocalSupport => support_mono inside ambient hinclusion _ vertex hlocalSupport)
      · apply hprivate (.closed center) trivial (Or.inr hcandidateEdge)
        intro vertex _ hlocalSupport
        rcases hlocalSupport with hsame | hlocalAdjacent
        · exact Or.inl hsame
        · have hdistinct : vertex ≠ neighbor := fun hsame => holdEdge (hsame ▸ hlocalAdjacent)
          exact Or.inr (Or.inl ⟨hinclusion _ _ hlocalAdjacent, hdistinct⟩)
    · have hcandidateEdge := hlocalEdge neighbor hedge
      by_cases holdEdge : inside center neighbor
      · exact False.elim (hprivate (.oriented center neighbor) holdEdge
          (Or.inr (Or.inr ⟨hcandidateEdge, hdifferent⟩))
          (fun vertex _ hlocalSupport => support_mono inside ambient hinclusion _ vertex hlocalSupport))
      have hcoreNeighbor := (hinside _ _ hcandidateEdge).1
      have hport : port neighbor := by
        apply Classical.byContradiction
        intro hnotPort
        exact holdEdge (hsymmInside _ _ (hunchanged neighbor hcoreNeighbor hnotPort center
          (hsymmAmbient _ _ hvalid)))
      have htransfer : ∀ vertex, inside neighbor vertex →
          Support ambient (.oriented center neighbor) vertex := by
        intro vertex hlocalAdjacent
        have hdistinct : vertex ≠ center := by
          intro hsame
          exact holdEdge (hsymmInside _ _ (hsame ▸ hlocalAdjacent))
        exact Or.inr (Or.inr ⟨hinclusion _ _ hlocalAdjacent, hdistinct⟩)
      have hselectedNeighbor : selection neighbor := by
        apply Classical.byContradiction
        intro hnotSelected
        apply hprivate (.closed neighbor) trivial (Or.inr hcandidateEdge)
        intro vertex hchosen hlocalSupport
        rcases hlocalSupport with hsame | hlocalAdjacent
        · exact False.elim (hnotSelected (hsame ▸ hchosen.2))
        · exact htransfer vertex hlocalAdjacent
      have houtside : ¬ selection center := by
        intro hcenter
        exact hdifferent (hunique center hcenter (Or.inl rfl)).symm
      have hnotCandidate : ¬ ambient center candidate := by
        intro hcenterCandidate
        apply hprivate (.closed center) trivial (Or.inr (hlocalEdge center hcenterCandidate))
        intro vertex _ hlocalSupport
        rcases hlocalSupport with hsame | hlocalAdjacent
        · exact Or.inl hsame
        · have hdistinct : vertex ≠ neighbor := fun hsame => holdEdge (hsame ▸ hlocalAdjacent)
          exact Or.inr (Or.inl ⟨hinclusion _ _ hlocalAdjacent, hdistinct⟩)
      refine ⟨neighbor, center, hcoreNeighbor, hport, hselectedNeighbor,
        hcandidateEdge, hvalid, holdEdge, ?_, houtside, ?_⟩
      · intro vertex _ hchosen hlocalAdjacent
        exact hunique vertex hchosen (htransfer vertex hlocalAdjacent)
      · intro vertex hcenterVertex hchosen
        apply Classical.byContradiction
        intro hdistinct
        have hequal := hunique vertex hchosen (Or.inr (Or.inl ⟨hcenterVertex, hdistinct⟩))
        exact hnotCandidate (hequal ▸ hcenterVertex)

theorem exported_owner_unique {Vertex : Type}
    (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop)
    (first second firstBoundary secondBoundary outside : Vertex)
    (hfirst : ExportWitness inside ambient core port selection first firstBoundary outside)
    (hsecond : ExportWitness inside ambient core port selection second secondBoundary outside)
    (hcore : core second) (hselected : selection second) : first = second := by
  have hboundary : secondBoundary = firstBoundary := hfirst.2.2.2.2.2.2.2.2
    secondBoundary hsecond.2.2.2.2.1 hsecond.2.2.1
  have hedge : inside firstBoundary second := hboundary ▸ hsecond.2.2.2.1
  exact (hfirst.2.2.2.2.2.2.1 second hcore hselected hedge).symm

end D5.S3.Combinatorics.Graph.StarForming.BoundaryLoss
