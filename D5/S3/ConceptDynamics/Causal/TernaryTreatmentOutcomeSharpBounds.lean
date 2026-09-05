/- GID: D5/S3/ConceptDynamics/Causal/TernaryTreatmentOutcomeSharpBounds
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/TernaryTreatmentOutcomeSharpBounds
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A ternary-treatment ternary-outcome query has closed-form certified sharp bounds. -/

import D5.S3.ConceptDynamics.Causal.FiniteEventCouplingSharpBounds

/- Library-search audit trail (2026-09-03):
   * The causal directory contains Boolean potential-outcome bounds and principal strata,
     but no finite structural response model with multivalued treatment and outcome.
   * Repository searches found no ternary-treatment query whose feasible interval is
     characterized by both a primal witness and a replayable dual certificate.
   * This module instantiates the generic two-event coupling without claiming that every
     multivalued counterfactual query reduces to two indicators. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.TernaryTreatmentOutcomeSharpBounds

open D5.S3.ConceptDynamics.Causal.FiniteEventCouplingSharpBounds

/-- Three treatment levels and three outcome levels. -/
abbrev Treatment := Fin 3
abbrev Outcome := Fin 3

/-- A four-state exogenous response type records whether the endpoint
counterfactual events occur. -/
abbrev ResponseType := Bool × Bool

/-- A finite structural response equation. At treatment zero the target outcome
zero is controlled by the first response bit. Treatment one has the neutral
outcome one. At treatment two the target outcome two is controlled by the
second response bit. -/
def potentialOutcome
    (response : ResponseType)
    (treatment : Treatment) : Outcome :=
  if treatment = (0 : Treatment) then
    if response.1 = true then 0 else 1
  else if treatment = (2 : Treatment) then
    if response.2 = true then 2 else 1
  else
    1

@[simp] theorem potentialOutcome_zero_target_iff
    (response : ResponseType) :
    potentialOutcome response 0 = 0 <-> response.1 = true := by
  rcases response with ⟨left, right⟩
  cases left <;> simp [potentialOutcome]

@[simp] theorem potentialOutcome_one
    (response : ResponseType) :
    potentialOutcome response 1 = 1 := by
  simp [potentialOutcome]

@[simp] theorem potentialOutcome_two_target_iff
    (response : ResponseType) :
    potentialOutcome response 2 = 2 <-> response.2 = true := by
  rcases response with ⟨left, right⟩
  cases right <;> simp [potentialOutcome]

/-- The partial-information model keeps the two endpoint interventional
marginals and an upper bound on endpoint counterfactual disagreement. -/
def IsEndpointModel
    (mass : ResponseType -> Real)
    (zeroTargetMarginal twoTargetMarginal disagreementCap : Real) : Prop :=
  IsEventCoupling mass zeroTargetMarginal twoTargetMarginal /\
    disagreementMass mass <= disagreementCap

/-- The event that treatment zero yields outcome zero and treatment two yields
outcome two is exactly the true-true response cell. -/
def endpointJointQuery (mass : ResponseType -> Real) : Real :=
  mass (true, true)

/-- The generic coupling certificate is a dual certificate for this ternary
structural response model because the endpoint events are exactly the two
response indicators. -/
theorem endpoint_model_dual_certificate
    (mass : ResponseType -> Real)
    (zeroTargetMarginal twoTargetMarginal disagreementCap : Real)
    (model :
      IsEndpointModel
        mass zeroTargetMarginal twoTargetMarginal disagreementCap) :
    EventCouplingDualCertificate
      mass zeroTargetMarginal twoTargetMarginal disagreementCap := by
  exact event_coupling_dual_certificate
    mass zeroTargetMarginal twoTargetMarginal disagreementCap model.1

/-- Replaying the dual certificate gives the closed-form lower and upper bounds
for the ternary-treatment, ternary-outcome endpoint query. -/
theorem endpoint_joint_query_bounds
    (mass : ResponseType -> Real)
    (zeroTargetMarginal twoTargetMarginal disagreementCap : Real)
    (model :
      IsEndpointModel
        mass zeroTargetMarginal twoTargetMarginal disagreementCap) :
    max
        (max 0 (zeroTargetMarginal + twoTargetMarginal - 1))
        ((zeroTargetMarginal + twoTargetMarginal - disagreementCap) / 2) <=
      endpointJointQuery mass /\
      endpointJointQuery mass <=
        min zeroTargetMarginal twoTargetMarginal := by
  exact event_coupling_bounds_with_disagreement_cap
    mass zeroTargetMarginal twoTargetMarginal disagreementCap
    model.1 model.2

/-- Closed-form sharp bounds for a concrete multivalued causal query.

The left side is the feasible interval obtained from normalization,
nonnegativity, the two endpoint interventional marginals, and a disagreement
cap. The right side constructs a normalized finite exogenous law for the
ternary structural equation. Hence every point in the interval, including both
endpoints, is attained. -/
theorem ternary_endpoint_joint_query_sharp_iff
    (zeroTargetMarginal twoTargetMarginal disagreementCap target : Real) :
    (max
          (max 0 (zeroTargetMarginal + twoTargetMarginal - 1))
          ((zeroTargetMarginal + twoTargetMarginal - disagreementCap) / 2) <=
        target /\
        target <= min zeroTargetMarginal twoTargetMarginal) <->
      exists mass : ResponseType -> Real,
        IsEndpointModel
            mass zeroTargetMarginal twoTargetMarginal disagreementCap /\
          endpointJointQuery mass = target := by
  constructor
  · intro bounds
    have realized :=
      (event_coupling_target_feasible_with_disagreement_cap_iff
        zeroTargetMarginal twoTargetMarginal disagreementCap target).mp
        bounds
    rcases realized with
      ⟨mass, feasible, disagreement_cap, target_eq⟩
    exact
      ⟨mass, ⟨feasible, disagreement_cap⟩,
        by simpa [endpointJointQuery] using target_eq⟩
  · rintro ⟨mass, model, target_eq⟩
    have bounds :=
      endpoint_joint_query_bounds
        mass zeroTargetMarginal twoTargetMarginal disagreementCap model
    simpa [target_eq] using bounds

#print axioms endpoint_joint_query_bounds
#print axioms ternary_endpoint_joint_query_sharp_iff

end D5.S3.ConceptDynamics.Causal.TernaryTreatmentOutcomeSharpBounds
