/- GID: D5/S3/Combinatorics/Graph/StarForming/PrivateClauses
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/PrivateClauses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Graph-local witness and selection proofs with exact source hypotheses. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularBound

/-!
Received from the-omega-institute/subquorum-colorings, revision
48728b42d39ab3de5de251c61da5a404ec418a69, formal/StarForming/PrivateClauses.lean.
Copyright 2026 The Omega Institute and contributors. Apache-2.0.
Changes: canonical imports/namespaces; numerical-only suffixes await graph consumers.
All retained local proof bodies and their hypotheses are preserved.
-/

namespace D5.S3.Combinatorics.Graph.StarForming.PrivateClauses

open D5.S3.Combinatorics.Graph.StarForming.Regular

inductive Clause (Vertex : Type) where
  | closed (center : Vertex)
  | oriented (center neighbor : Vertex)

def Valid {Vertex : Type} (adjacency : Vertex → Vertex → Prop) : Clause Vertex → Prop
  | .closed _ => True
  | .oriented center neighbor => adjacency center neighbor

def Support {Vertex : Type} (adjacency : Vertex → Vertex → Prop) :
    Clause Vertex → Vertex → Prop
  | .closed center, vertex => vertex = center ∨ adjacency center vertex
  | .oriented center neighbor, vertex =>
      vertex = center ∨ (adjacency center vertex ∧ vertex ≠ neighbor) ∨
        (adjacency neighbor vertex ∧ vertex ≠ center)

def Hits {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) : Prop :=
  ∀ clause, Valid adjacency clause →
    ∃ vertex, selection vertex ∧ Support adjacency clause vertex

def Private {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (clause : Clause Vertex) (owner : Vertex) : Prop :=
  Valid adjacency clause ∧ Support adjacency clause owner ∧
    ∀ vertex, selection vertex → Support adjacency clause vertex → vertex = owner

theorem forms_iff_hits {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) : Forms adjacency selection ↔ Hits adjacency selection := by
  classical
  constructor
  · intro hforms clause hvalid
    cases clause with
    | closed center =>
      by_cases hselected : selection center
      · exact ⟨center, hselected, Or.inl rfl⟩
      · rcases hforms center hselected with ⟨first, second, hf, _, _, hedge, _⟩ |
            ⟨first, second, hf, _, hedge, _⟩ <;>
          exact ⟨first, hf, Or.inr hedge⟩
    | oriented center neighbor =>
      by_cases hselected : selection center
      · exact ⟨center, hselected, Or.inl rfl⟩
      · rcases hforms center hselected with ⟨first, second, hf, hs, hne, ha, hb⟩ |
            ⟨first, second, hf, hs, ha, hb⟩
        · by_cases hequal : first = neighbor
          · have hsecond : second ≠ neighbor := fun hsame => hne (hequal.trans hsame.symm)
            exact ⟨second, hs, Or.inr (Or.inl ⟨hb, hsecond⟩)⟩
          · exact ⟨first, hf, Or.inr (Or.inl ⟨ha, hequal⟩)⟩
        · by_cases hequal : first = neighbor
          · have hsecond : second ≠ center := by
              intro hsame
              exact hselected (hsame ▸ hs)
            subst first
            exact ⟨second, hs, Or.inr (Or.inr ⟨hb, hsecond⟩)⟩
          · exact ⟨first, hf, Or.inr (Or.inl ⟨ha, hequal⟩)⟩
  · intro hhits center houtside
    obtain ⟨neighbor, hneighbor, hclosed⟩ := hhits (.closed center) trivial
    have hedge : adjacency center neighbor := by
      rcases hclosed with hequal | hadjacent
      · exact False.elim (houtside (hequal ▸ hneighbor))
      · exact hadjacent
    obtain ⟨vertex, hvertex, horiented⟩ := hhits (.oriented center neighbor) hedge
    rcases horiented with hequal | ⟨hadjacent, hdifferent⟩ | ⟨hadjacent, _⟩
    · exact False.elim (houtside (hequal ▸ hvertex))
    · exact Or.inl ⟨vertex, neighbor, hvertex, hneighbor, hdifferent, hadjacent, hedge⟩
    · exact Or.inr ⟨neighbor, vertex, hneighbor, hvertex, hedge, hadjacent⟩

theorem minimal_iff_private {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) :
    Minimal adjacency selection ↔ Hits adjacency selection ∧
      ∀ owner, selection owner → ∃ clause, Private adjacency selection clause owner := by
  classical
  constructor
  · intro hminimal
    have hhits := (forms_iff_hits adjacency selection).mp hminimal.1
    refine ⟨hhits, ?_⟩
    intro owner howner
    apply Classical.byContradiction
    intro hnone
    have hdeleted : Hits adjacency (fun vertex => selection vertex ∧ vertex ≠ owner) := by
      intro clause hvalid
      by_cases hother : ∃ vertex, selection vertex ∧ Support adjacency clause vertex ∧
          vertex ≠ owner
      · obtain ⟨vertex, hvertex, hsupport, hdifferent⟩ := hother
        exact ⟨vertex, ⟨hvertex, hdifferent⟩, hsupport⟩
      · obtain ⟨vertex, hvertex, hsupport⟩ := hhits clause hvalid
        have hequal : vertex = owner := by
          apply Classical.byContradiction
          intro hdifferent
          exact hother ⟨vertex, hvertex, hsupport, hdifferent⟩
        have hsupportOwner : Support adjacency clause owner := hequal ▸ hsupport
        have hprivate : Private adjacency selection clause owner := by
          refine ⟨hvalid, hsupportOwner, ?_⟩
          intro other hselected hsupportOther
          apply Classical.byContradiction
          intro hdifferent
          exact hother ⟨other, hselected, hsupportOther, hdifferent⟩
        exact False.elim (hnone ⟨clause, hprivate⟩)
    exact hminimal.2 _ (fun _ hvertex => hvertex.1)
      ⟨owner, howner, fun hvertex => hvertex.2 rfl⟩
      ((forms_iff_hits adjacency _).mpr hdeleted)
  · rintro ⟨hhits, hprivate⟩
    refine ⟨(forms_iff_hits adjacency selection).mpr hhits, ?_⟩
    intro smaller hsubset hproper hforms
    obtain ⟨owner, howner, hmissing⟩ := hproper
    obtain ⟨clause, hvalid, _, hunique⟩ := hprivate owner howner
    obtain ⟨vertex, hvertex, hsupport⟩ :=
      (forms_iff_hits adjacency smaller).mp hforms clause hvalid
    have hequal := hunique vertex (hsubset vertex hvertex) hsupport
    exact hmissing (hequal ▸ hvertex)

theorem private_owner_unique {Vertex : Type} (adjacency : Vertex → Vertex → Prop)
    (selection : Vertex → Prop) (clause : Clause Vertex) (first second : Vertex)
    (hfirst : selection first) (_hsecond : selection second)
    (hprivateFirst : Private adjacency selection clause first)
    (hprivateSecond : Private adjacency selection clause second) : first = second := by
  exact hprivateSecond.2.2 first hfirst hprivateFirst.2.1

theorem support_mono {Vertex : Type} (inside ambient : Vertex → Vertex → Prop)
    (hinclusion : ∀ first second, inside first second → ambient first second)
    (clause : Clause Vertex) (vertex : Vertex)
    (hsupport : Support inside clause vertex) : Support ambient clause vertex := by
  cases clause with
  | closed center =>
    rcases hsupport with hequal | hedge
    · exact Or.inl hequal
    · exact Or.inr (hinclusion _ _ hedge)
  | oriented center neighbor =>
    rcases hsupport with hequal | ⟨hedge, hdifferent⟩ | ⟨hedge, hdifferent⟩
    · exact Or.inl hequal
    · exact Or.inr (Or.inl ⟨hinclusion _ _ hedge, hdifferent⟩)
    · exact Or.inr (Or.inr ⟨hinclusion _ _ hedge, hdifferent⟩)

def PortWitness {Vertex : Type} (inside : Vertex → Vertex → Prop)
    (core port selection : Vertex → Prop) (candidate : Vertex) : Prop :=
  ∃ boundary, core boundary ∧ port boundary ∧ selection boundary ∧
    inside boundary candidate ∧
    ∀ vertex, core vertex → selection vertex → inside boundary vertex → vertex = candidate

theorem boundary_certificate {Vertex : Type}
    (inside ambient : Vertex → Vertex → Prop) (core port selection : Vertex → Prop)
    (hinclusion : ∀ first second, inside first second → ambient first second)
    (hinside : ∀ first second, inside first second → core first ∧ core second)
    (hsymmInside : ∀ first second, inside first second → inside second first)
    (hsymmAmbient : ∀ first second, ambient first second → ambient second first)
    (hunchanged : ∀ vertex, core vertex → ¬ port vertex →
      ∀ neighbor, ambient vertex neighbor → inside vertex neighbor)
    (hminimal : Minimal ambient selection) (candidate : Vertex)
    (hcore : core candidate) (hnonport : ¬ port candidate) (hselected : selection candidate) :
    (∃ clause, Private inside (fun vertex => core vertex ∧ selection vertex) clause candidate) ∨
      PortWitness inside core port selection candidate := by
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
        Support ambient globalClause vertex) →
      ∃ clause, Private inside (fun vertex => core vertex ∧ selection vertex) clause candidate := by
    intro localClause hvalidLocal hsupportLocal htransfer
    refine ⟨localClause, hvalidLocal, hsupportLocal, ?_⟩
    intro vertex hchosen hlocalSupport
    exact hunique vertex hchosen.2 (htransfer vertex hchosen hlocalSupport)
  cases globalClause with
  | closed center =>
    have hsupportLocal : Support inside (.closed center) candidate := by
      rcases hsupport with hequal | hedge
      · exact Or.inl hequal
      · exact Or.inr (hlocalEdge center hedge)
    exact Or.inl (hprivate (.closed center) trivial hsupportLocal
      (fun vertex _ hlocalSupport => support_mono inside ambient hinclusion _ vertex hlocalSupport))
  | oriented center neighbor =>
    rcases hsupport with hequal | ⟨hedge, hdifferent⟩ | ⟨hedge, hdifferent⟩
    · have holdEdge : inside center neighbor := by
        rw [← hequal]
        exact hunchanged candidate hcore hnonport neighbor (hequal ▸ hvalid)
      exact Or.inl (hprivate (.oriented center neighbor) holdEdge (Or.inl hequal)
        (fun vertex _ hlocalSupport => support_mono inside ambient hinclusion _ vertex hlocalSupport))
    · have hcandidateEdge := hlocalEdge center hedge
      by_cases holdEdge : inside center neighbor
      · exact Or.inl (hprivate (.oriented center neighbor) holdEdge
          (Or.inr (Or.inl ⟨hcandidateEdge, hdifferent⟩))
          (fun vertex _ hlocalSupport => support_mono inside ambient hinclusion _ vertex hlocalSupport))
      · apply Or.inl
        apply hprivate (.closed center) trivial (Or.inr hcandidateEdge)
        intro vertex _ hlocalSupport
        rcases hlocalSupport with hsame | hlocalAdjacent
        · exact Or.inl hsame
        · have hdistinct : vertex ≠ neighbor := fun hsame => holdEdge (hsame ▸ hlocalAdjacent)
          exact Or.inr (Or.inl ⟨hinclusion _ _ hlocalAdjacent, hdistinct⟩)
    · have hcandidateEdge := hlocalEdge neighbor hedge
      by_cases holdEdge : inside center neighbor
      · exact Or.inl (hprivate (.oriented center neighbor) holdEdge
          (Or.inr (Or.inr ⟨hcandidateEdge, hdifferent⟩))
          (fun vertex _ hlocalSupport => support_mono inside ambient hinclusion _ vertex hlocalSupport))
      · have hcoreNeighbor := (hinside _ _ hcandidateEdge).1
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
        by_cases hselectedNeighbor : selection neighbor
        · exact Or.inr ⟨neighbor, hcoreNeighbor, hport, hselectedNeighbor, hcandidateEdge,
            fun vertex _ hchosen hlocalAdjacent => hunique vertex hchosen (htransfer vertex hlocalAdjacent)⟩
        · apply Or.inl
          apply hprivate (.closed neighbor) trivial (Or.inr hcandidateEdge)
          intro vertex hchosen hlocalSupport
          rcases hlocalSupport with hsame | hlocalAdjacent
          · exact False.elim (hselectedNeighbor (hsame ▸ hchosen.2))
          · exact htransfer vertex hlocalAdjacent

end D5.S3.Combinatorics.Graph.StarForming.PrivateClauses
