/- GID: D5/S3/ConceptDynamics/PublicAnnouncement/OriginalStateAnnouncementReachability
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PublicAnnouncement/OriginalStateAnnouncementReachability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A true announcement is preserved along every restricted access path. -/

import Mathlib.Logic.Relation

/- Library-search audit trail (2026-08-25):
   * Public-announcement, common-knowledge, and restricted-access searches found
     only the frozen subtype predecessor, which does not consume its path premise.
   * `InvariantSafety.invariant_safety` is a broader repository theorem rather
     than the source statement on the announcement restriction.
   * Pinned Mathlib's `Relation.ReflTransGen` induction is the exact finite-path
     primitive used below. No definition or abbreviation is introduced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PublicAnnouncement.OriginalStateAnnouncementReachability

/-- If the actual anchor satisfies the public predicate, then every state
reachable from it through the predicate-restricted union of the agents'
accessibility relations also satisfies the predicate. The carrier remains the
original state type. -/
theorem true_public_announcement_is_common_knowledge_on_original_states
    {State Agent : Type*}
    (access : Agent → State → State → Prop)
    (predicate : State → Prop)
    (anchor : State)
    (hAnchor : predicate anchor) :
    ∀ target,
      Relation.ReflTransGen
          (fun source target : State =>
            predicate source ∧ predicate target ∧
              ∃ agent, access agent source target)
          anchor target →
        predicate target := by
  intro target path
  induction path with
  | refl => exact hAnchor
  | tail _ restrictedStep _ => exact restrictedStep.2.1

#print axioms true_public_announcement_is_common_knowledge_on_original_states

end D5.S3.ConceptDynamics.PublicAnnouncement.OriginalStateAnnouncementReachability
