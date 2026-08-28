/- GID: D5/S3/ConceptDynamics/InterventionLaws/ExperimentalQuotientCharacterization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionLaws/ExperimentalQuotientCharacterization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Experimental targets are exactly functions on the empirical quotient. -/

import D5.S3.ConceptDynamics.Interventions.ExperimentalQuotientUniversality

/- Library-search audit trail (2026-08-26):
   * The exact repository primitives `experimentTrace`, `EmpiricalQuotient`, and
     `empiricalClass` are imported rather than redeclared.
   * The frozen theorem `experimental_quotient_universality` supplies the trace
     factorization clause, but its public signature has only the forward
     constant-target implication.
   * The exact repository theorem `empirical_identifiability` supplies the
     target-factorization equivalence and the varying-within-class obstruction.
   * Repository and pinned-Mathlib searches found no declaration combining all
     three public clauses on the intervention/readout trace carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionLaws.ExperimentalQuotientCharacterization

open D5.S3.ConceptDynamics.EmpiricalIdentifiability
open D5.S3.ConceptDynamics.Interventions.ExperimentalQuotientUniversality

/-- Every intervention trace factors uniquely through the empirical quotient.
A target factors uniquely exactly when it is constant on experimental classes,
and a target varying within one class admits no quotient factor. -/
theorem experimental_quotient_characterization
    {Action State Observation Target : Type _}
    (intervene : Action -> State -> State)
    (observe : State -> Observation)
    (target : State -> Target) :
    (forall actions : List Action,
      ExistsUnique
        (fun descend :
            EmpiricalQuotient (experimentTrace intervene observe) -> List Observation =>
          experimentTrace intervene observe actions =
            descend ∘ empiricalClass (experimentTrace intervene observe))) /\
    (((ExistsUnique
          (fun descend : EmpiricalQuotient (experimentTrace intervene observe) -> Target =>
            target = descend ∘ empiricalClass (experimentTrace intervene observe))) <->
        forall {x y : State},
          (forall actions : List Action,
            experimentTrace intervene observe actions x =
              experimentTrace intervene observe actions y) ->
            target x = target y) /\
      ((exists x y : State,
          (forall actions : List Action,
            experimentTrace intervene observe actions x =
              experimentTrace intervene observe actions y) /\
            Not (target x = target y)) ->
        Not (exists descend :
            EmpiricalQuotient (experimentTrace intervene observe) -> Target,
          target = descend ∘ empiricalClass (experimentTrace intervene observe)))) := by
  constructor
  · exact (experimental_quotient_universality intervene observe target).1
  · exact empirical_identifiability (experimentTrace intervene observe) target

#print axioms experimental_quotient_characterization

end D5.S3.ConceptDynamics.InterventionLaws.ExperimentalQuotientCharacterization
