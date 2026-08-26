/- GID: D5/S3/ConceptDynamics/InterventionsExchange/FactualInterventionConsistency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InterventionsExchange/FactualInterventionConsistency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A factual outcome agrees with the matching intervention under one shared mechanism. -/

/- Library-search audit trail (2026-08-26):
   * The existing intervention family supplies Boolean countermodels and
     interventional/counterfactual tables, but no generic theorem connecting a
     factual treatment to the potential outcome at that same treatment.
   * Body-shape searches for factual-treatment evaluation and matching
     interventions found no D5 primitive to import; the public statement uses
     only its supplied mechanism and assignment and introduces no new `def`.
   * Pinned Mathlib has no causal consistency theorem. Core `congrArg` is the
     exact equality transport used after constructing both outcomes. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.InterventionsExchange.FactualInterventionConsistency

universe uU uX uY

/-- Evaluating one structural outcome mechanism at the factual treatment gives
the same result as imposing that treatment value. -/
theorem factual_intervention_consistency
    {U : Type uU} {X : Type uX} {Y : Type uY}
    (outcome : U -> X -> Y)
    (factualTreatment : U -> X)
    (u : U)
    (x : X)
    (factualTreatmentMatches : factualTreatment u = x) :
    let factualOutcome : Y := outcome u (factualTreatment u)
    let potentialOutcome : X -> Y := fun imposed => outcome u imposed
    factualOutcome = potentialOutcome x := by
  dsimp only
  exact congrArg (outcome u) factualTreatmentMatches

example :
    let factualOutcome : Nat := (fun u x : Nat => u + x) 3 ((fun _ => 2) 3)
    let potentialOutcome : Nat -> Nat := fun imposed =>
      (fun u x : Nat => u + x) 3 imposed
    factualOutcome = potentialOutcome 2 := by
  exact factual_intervention_consistency
    (fun u x : Nat => u + x) (fun _ => 2) 3 2 rfl

#print axioms factual_intervention_consistency

end D5.S3.ConceptDynamics.InterventionsExchange.FactualInterventionConsistency
