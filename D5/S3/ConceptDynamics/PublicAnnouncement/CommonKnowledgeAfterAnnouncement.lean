/- GID: D5/S3/ConceptDynamics/PublicAnnouncement/CommonKnowledgeAfterAnnouncement
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PublicAnnouncement/CommonKnowledgeAfterAnnouncement
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A true public announcement makes its announced proposition common knowledge. -/

import D5.S3.ConceptDynamics.Epistemic.DescriptiveAnnouncementCommutation
import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-25):
   * `rg -n -i 'common.*knowledge|publicAnnouncement|announcement' D5/S3/ConceptDynamics`
     found no theorem combining a public restriction with iterated relational knowledge.
   * `DescriptiveAnnouncementCommutation.descriptiveCondition` is the canonical
     repository primitive for public announcement restriction and is imported below.
   * Pinned Mathlib's `Relation.ReflTransGen` supplies the finite-path closure used
     for common knowledge; no exact public-announcement theorem was found.
   * `rg -n 'def .*announcement.*\{x.*predicate|def .*commonKnowledge' D5`
     found no duplicate body shape before introducing the model and step helpers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PublicAnnouncement.CommonKnowledgeAfterAnnouncement

open D5.S3.ConceptDynamics.Epistemic.DescriptiveAnnouncementCommutation

/-- The post-announcement model is the subtype of states admitted by the
canonical descriptive announcement of `predicate` from the universal model. -/
def announcedModel {State : Type*} (predicate : State → Prop) : Type _ :=
  {state : State // state ∈
    descriptiveCondition ({state | predicate state} : Set State) Set.univ}

/-- The actual state embeds into the announced model when it satisfies the
announced predicate. -/
def announcedAnchor {State : Type*} (predicate : State → Prop)
  (anchor : State) (hAnchor : predicate anchor) : announcedModel predicate :=
  ⟨anchor, by
    simp [descriptiveCondition, hAnchor]⟩

/-- One public-information step in the announced model is an edge of one
agent's source accessibility relation. -/
def announcementStep {State Agent : Type*}
    (access : Agent → State → State → Prop)
    {predicate : State → Prop} :
    announcedModel predicate → announcedModel predicate → Prop :=
  fun source target => ∃ agent, access agent source.1 target.1

/-- After a true public announcement, every state reachable by finitely many
agent-information steps still satisfies the announced proposition. This is
common knowledge in the post-announcement model. -/
theorem true_public_announcement_is_common_knowledge
    {State Agent : Type*}
    (access : Agent → State → State → Prop)
    (predicate : State → Prop)
    (anchor : State)
    (hAnchor : predicate anchor) :
    ∃ announcedActual : announcedModel predicate,
      announcedActual.1 = anchor ∧
        ∀ target : announcedModel predicate,
          Relation.ReflTransGen (announcementStep access)
              announcedActual target →
            predicate target.1 := by
  refine ⟨announcedAnchor predicate anchor hAnchor, rfl, ?_⟩
  intro target _
  have hAdmitted := target.property
  simpa [descriptiveCondition] using hAdmitted

/-- A concrete two-world model shows that arbitrary accessibility relations are
allowed while the public announcement removes the false world. -/
example :
    ∃ announcedActual : announcedModel (fun state : Bool => state = true),
      announcedActual.1 = true ∧
        ∀ target : announcedModel (fun state : Bool => state = true),
          Relation.ReflTransGen
              (announcementStep (fun _ left right : Bool => left = right))
              announcedActual target →
            target.1 = true := by
  exact true_public_announcement_is_common_knowledge
    (access := fun _ left right : Bool => left = right)
    (predicate := fun state : Bool => state = true) (anchor := true) rfl

#print axioms true_public_announcement_is_common_knowledge

end D5.S3.ConceptDynamics.PublicAnnouncement.CommonKnowledgeAfterAnnouncement
