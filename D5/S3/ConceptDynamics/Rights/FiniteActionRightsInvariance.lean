/- GID: D5/S3/ConceptDynamics/Rights/FiniteActionRightsInvariance
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Rights/FiniteActionRightsInvariance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite compositions of certified atomic actions preserve the safe set. -/

import Mathlib.Data.Set.Function

/- Library-search audit trail (2026-08-26):
   * Repository searches for rights invariance, finite action sequences,
     `List.foldl`, `Set.MapsTo`, and iterated subset preservation found no
     theorem covering a heterogeneous finite action list.
   * Exact pinned-Mathlib hit `Set.MapsTo.comp` proves that two certified maps
     compose, while `Set.MapsTo.iterate` covers repeated use of one fixed map.
     The former is the one-step principle used by the list induction below.
   * The action sequence is written directly as `List.foldl`; no local action
     runner or invariant predicate is introduced beside the canonical forms. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Rights.FiniteActionRightsInvariance

/-- If every certified atomic action maps the safe set into itself, then the
composition selected by every finite action list maps the safe set into itself. -/
theorem finite_action_sequence_preserves_rights
    {State Action : Type*} (safe : Set State) (act : Action -> State -> State)
    (atomicPreserves : forall action, Set.MapsTo (act action) safe safe) :
    forall actions : List Action,
      Set.MapsTo
        (fun state => actions.foldl (fun current action => act action current) state)
        safe safe := by
  intro actions
  induction actions with
  | nil =>
      intro state stateSafe
      exact stateSafe
  | cons action rest inductionHypothesis =>
      intro state stateSafe
      exact inductionHypothesis (atomicPreserves action stateSafe)

#print axioms finite_action_sequence_preserves_rights

end D5.S3.ConceptDynamics.Rights.FiniteActionRightsInvariance
