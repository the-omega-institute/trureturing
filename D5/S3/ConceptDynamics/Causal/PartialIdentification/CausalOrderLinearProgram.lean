/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/CausalOrderLinearProgram
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/CausalOrderLinearProgram
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical response-signature event probabilities compile to exact finite linear causal queries with replayable primal-dual bounds. -/

import D5.S3.ConceptDynamics.Causal.FiniteLinearCausalIdentification
import D5.S3.ConceptDynamics.Causal.PartialIdentification.CanonicalResponseSignature

/- Library-search audit trail (2026-09-03):
   * `CanonicalResponseSignature` supplies a finite deterministic response-type
     carrier and proves that every Boolean signature event is a linear
     objective in its mass vector.
   * `FiniteLinearCausalIdentification` supplies layered rational constraints
     and exact primal-dual endpoint certificates, but previously had no
     canonical response-signature event compiler.
   * This module joins those interfaces. It does not yet prove that a particular
     observational data table or partial graph has been compiled completely. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.CausalOrderLinearProgram

open scoped BigOperators
open D5.S3.ConceptDynamics.Causal.FiniteLinearCausalIdentification
open D5.S3.ConceptDynamics.Causal.PartialIdentification.CanonicalResponseSignature

/-- Compile layered constraints on response-signature masses together with one
Boolean counterfactual event into the generic finite linear causal problem. -/
def signatureEventProblem
    {Signature Constraint : Type*}
    [Fintype Signature] [Fintype Constraint]
    (layer : Constraint -> ConstraintLayer)
    (row : Constraint -> Signature -> ℚ)
    (rhs : Constraint -> ℚ)
    (event : Signature -> Bool) :
    FiniteLinearCausalProblem Signature Constraint where
  layer := layer
  row := row
  rhs := rhs
  queryCoefficient := eventCoefficient event

/-- The compiled causal query is definitionally the event mass on canonical
response signatures. -/
theorem signatureEventProblem_query_eq
    {Signature Constraint : Type*}
    [Fintype Signature] [Fintype Constraint]
    (layer : Constraint -> ConstraintLayer)
    (row : Constraint -> Signature -> ℚ)
    (rhs : Constraint -> ℚ)
    (event : Signature -> Bool)
    (mass : Signature -> ℚ) :
    Query (signatureEventProblem layer row rhs event) mass =
      signatureEventMass mass event := by
  unfold Query signatureEventProblem
  exact (signature_event_mass_eq_linearObjective mass event).symm

/-- A rational lower dual certificate for the compiled signature problem proves
a lower bound on the original event probability. -/
theorem signature_event_lower_bound_of_certificate
    {Signature Constraint : Type*}
    [Fintype Signature] [Fintype Constraint]
    (layer : Constraint -> ConstraintLayer)
    (row : Constraint -> Signature -> ℚ)
    (rhs : Constraint -> ℚ)
    (event : Signature -> Bool)
    (lower : ℚ)
    (certificate :
      LowerCertificate (signatureEventProblem layer row rhs event) lower)
    (mass : Signature -> ℚ)
    (feasible :
      Feasible (signatureEventProblem layer row rhs event) mass) :
    lower <= signatureEventMass mass event := by
  rw [← signatureEventProblem_query_eq layer row rhs event mass]
  exact query_lower_bound_of_certificate
    (signatureEventProblem layer row rhs event)
    lower certificate mass feasible

/-- A rational upper dual certificate for the compiled signature problem proves
an upper bound on the original event probability. -/
theorem signature_event_upper_bound_of_certificate
    {Signature Constraint : Type*}
    [Fintype Signature] [Fintype Constraint]
    (layer : Constraint -> ConstraintLayer)
    (row : Constraint -> Signature -> ℚ)
    (rhs : Constraint -> ℚ)
    (event : Signature -> Bool)
    (upper : ℚ)
    (certificate :
      UpperCertificate (signatureEventProblem layer row rhs event) upper)
    (mass : Signature -> ℚ)
    (feasible :
      Feasible (signatureEventProblem layer row rhs event) mass) :
    signatureEventMass mass event <= upper := by
  rw [← signatureEventProblem_query_eq layer row rhs event mass]
  exact query_upper_bound_of_certificate
    (signatureEventProblem layer row rhs event)
    upper certificate mass feasible

/-- The same event evaluated directly on a finite exogenous carrier. -/
def exogenousEventMass
    {Exogenous Signature : Type*}
    [Fintype Exogenous]
    (mass : Exogenous -> ℚ)
    (signatureOf : Exogenous -> Signature)
    (event : Signature -> Bool) : ℚ :=
  ∑ exogenous,
    if event (signatureOf exogenous) then mass exogenous else 0

/-- Pushing an exogenous SCM law to canonical response signatures preserves the
probability of every Boolean counterfactual event. This is the semantic bridge
between an exogenous structural witness and the linear-program objective. -/
theorem signature_event_mass_pushforward
    {Exogenous Signature : Type*}
    [Fintype Exogenous] [Fintype Signature] [DecidableEq Signature]
    (mass : Exogenous -> ℚ)
    (signatureOf : Exogenous -> Signature)
    (event : Signature -> Bool) :
    signatureEventMass
        (pushforwardSignatureMass mass signatureOf) event =
      exogenousEventMass mass signatureOf event := by
  unfold signatureEventMass pushforwardSignatureMass exogenousEventMass
  calc
    (∑ signature,
        if event signature then
          (∑ exogenous,
            if signatureOf exogenous = signature then
              mass exogenous else 0)
        else 0) =
      ∑ signature, ∑ exogenous,
        if event signature then
          (if signatureOf exogenous = signature then
            mass exogenous else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro signature _
          by_cases event_holds : event signature <;>
            simp [event_holds]
    _ = ∑ exogenous, ∑ signature,
        if event signature then
          (if signatureOf exogenous = signature then
            mass exogenous else 0)
        else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ exogenous,
        if event (signatureOf exogenous) then
          mass exogenous else 0 := by
          apply Finset.sum_congr rfl
          intro exogenous _
          by_cases event_holds : event (signatureOf exogenous) <;>
            simp [event_holds]

/-- Every rational primal witness for a finite signature law has a direct
exogenous realization using the signature carrier itself. For event queries,
the realized exogenous probability is exactly the certified LP objective. -/
theorem identity_exogenous_realizes_signature_event
    {Signature : Type*}
    [Fintype Signature] [DecidableEq Signature]
    (mass : Signature -> ℚ)
    (event : Signature -> Bool) :
    exogenousEventMass mass (fun signature => signature) event =
      signatureEventMass mass event := by
  rfl

#print axioms signatureEventProblem_query_eq
#print axioms signature_event_lower_bound_of_certificate
#print axioms signature_event_upper_bound_of_certificate
#print axioms signature_event_mass_pushforward
#print axioms identity_exogenous_realizes_signature_event

end D5.S3.ConceptDynamics.Causal.PartialIdentification.CausalOrderLinearProgram
