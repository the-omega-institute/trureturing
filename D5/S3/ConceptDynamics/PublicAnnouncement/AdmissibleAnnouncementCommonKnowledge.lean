/- GID: D5/S3/ConceptDynamics/PublicAnnouncement/AdmissibleAnnouncementCommonKnowledge
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PublicAnnouncement/AdmissibleAnnouncementCommonKnowledge
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A true public announcement is common knowledge on the restricted admitted domain. -/

import D5.S3.ConceptDynamics.Epistemic.DescriptiveAnnouncementCommutation
import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-27):
   * The frozen `CommonKnowledgeAfterAnnouncement` theorem fixes the prior admitted
     domain to `Set.univ`, so it is not an exact hit for the source's arbitrary domain.
   * `OriginalStateAnnouncementReachability` also omits the arbitrary admitted domain.
   * Body-shape searches found `descriptiveCondition` as the canonical restriction
     primitive; it is imported and instantiated rather than redeclared.
   * Pinned Mathlib supplies `Relation.ReflTransGen` but no exact theorem combining
     public restriction, arbitrary agent access, and common knowledge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PublicAnnouncement.AdmissibleAnnouncementCommonKnowledge

open D5.S3.ConceptDynamics.Epistemic.DescriptiveAnnouncementCommutation

/-- If the actual state belongs to the current domain and satisfies the public
announcement, the announced proposition holds at every finitely reachable state
in the canonically restricted post-announcement model. -/
theorem true_public_announcement_is_common_knowledge_on_admitted_domain
    {State Agent : Type*}
    (admitted predicate : Set State)
    (access : Agent -> State -> State -> Prop)
    (anchor : State)
    (anchorAdmitted : anchor ∈ admitted)
    (anchorTrue : anchor ∈ predicate) :
    ∃ announcedActual :
        {state : State // state ∈ descriptiveCondition predicate admitted},
      announcedActual.1 = anchor ∧
        ∀ target :
            {state : State // state ∈ descriptiveCondition predicate admitted},
          Relation.ReflTransGen
              (fun source target =>
                ∃ agent, access agent source.1 target.1)
              announcedActual target ->
            target.1 ∈ predicate := by
  refine ⟨⟨anchor, ?_⟩, rfl, ?_⟩
  · exact ⟨anchorAdmitted, anchorTrue⟩
  · intro target _
    exact target.property.2

/-- A two-state model witnesses the public premises and permits arbitrary
agent-access paths after the false state is removed by the announcement. -/
example :
    ∃ announcedActual :
        {state : Bool //
          state ∈ descriptiveCondition ({true} : Set Bool) Set.univ},
      announcedActual.1 = true ∧
        ∀ target :
            {state : Bool //
              state ∈ descriptiveCondition ({true} : Set Bool) Set.univ},
          Relation.ReflTransGen
              (fun source target => ∃ _ : Unit, source.1 = target.1)
              announcedActual target ->
            target.1 ∈ ({true} : Set Bool) := by
  exact true_public_announcement_is_common_knowledge_on_admitted_domain
    (admitted := Set.univ)
    (predicate := ({true} : Set Bool))
    (access := fun (_ : Unit) (left right : Bool) => left = right)
    (anchor := true) (Set.mem_univ true) rfl

#print axioms true_public_announcement_is_common_knowledge_on_admitted_domain

end D5.S3.ConceptDynamics.PublicAnnouncement.AdmissibleAnnouncementCommonKnowledge
