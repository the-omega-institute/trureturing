/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/PartialGraphInformationOrder
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/PartialGraphInformationOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Stronger partial causal diagrams induce smaller compatible-model and identified-query sets. -/

import D5.S3.ConceptDynamics.Causal.NonconvexSharpIdentification

/- Library-search audit trail (2026-09-03):
   * `NonconvexSharpIdentification` already contains the generic theorem that a
     bound valid on an outer feasible family remains valid on an inner family.
   * Repository searches found no partial causal diagram object distinguishing
     required and forbidden edges, and no compatibility antitonicity theorem.
   * This module adds only the graph-information semantics, then delegates bound
     transport and endpoint monotonicity to the existing identification core. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialGraphInformationOrder

open D5.S3.ConceptDynamics.Causal.NonconvexSharpIdentification

/-- A partial causal diagram records edges known to be present and edges known
to be absent. Unmentioned pairs remain structurally unresolved. -/
structure PartialCausalDiagram (Node : Type*) where
  requiredEdge : Node -> Node -> Prop
  forbiddenEdge : Node -> Node -> Prop
  coherent : forall source target,
    requiredEdge source target -> not (forbiddenEdge source target)

/-- A complete directed edge relation is compatible with every positive and
negative assertion made by a partial diagram. -/
def Compatible
    {Node : Type*}
    (diagram : PartialCausalDiagram Node)
    (edge : Node -> Node -> Prop) : Prop :=
  (forall source target,
      diagram.requiredEdge source target -> edge source target) /\
    forall source target,
      diagram.forbiddenEdge source target -> not (edge source target)

/-- `stronger` refines `weaker` when it retains every required and forbidden
edge assertion of the weaker diagram and may add further assertions. -/
def Refines
    {Node : Type*}
    (stronger weaker : PartialCausalDiagram Node) : Prop :=
  (forall source target,
      weaker.requiredEdge source target ->
        stronger.requiredEdge source target) /\
    forall source target,
      weaker.forbiddenEdge source target ->
        stronger.forbiddenEdge source target

/-- Diagram information is contravariant to model compatibility: every graph
compatible with a stronger partial diagram is compatible with the weaker one. -/
theorem compatible_antitone
    {Node : Type*}
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (edge : Node -> Node -> Prop)
    (compatible : Compatible stronger edge) :
    Compatible weaker edge := by
  constructor
  · intro source target required
    exact compatible.1 source target (refinement.1 source target required)
  · intro source target forbidden
    exact compatible.2 source target (refinement.2 source target forbidden)

/-- A common model carrier supplies a complete graph and a scalar causal query.
Different partial diagrams restrict the same carrier by compatibility. -/
structure DiagramQueryProblem (Node Model : Type*) where
  graph : Model -> Node -> Node -> Prop
  query : Model -> Real

/-- The generic identification problem induced by one partial diagram. -/
def asIdentificationProblem
    {Node Model : Type*}
    (problem : DiagramQueryProblem Node Model)
    (diagram : PartialCausalDiagram Node) :
    IdentificationProblem Model where
  feasible model := Compatible diagram (problem.graph model)
  query := problem.query

/-- The identified set of query values compatible with a partial diagram. -/
def Identified
    {Node Model : Type*}
    (problem : DiagramQueryProblem Node Model)
    (diagram : PartialCausalDiagram Node)
    (target : Real) : Prop :=
  exists model,
    Compatible diagram (problem.graph model) /\
      problem.query model = target

/-- Stronger partial graph knowledge can only remove query values from the
identified set. -/
theorem identified_set_antitone
    {Node Model : Type*}
    (problem : DiagramQueryProblem Node Model)
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (target : Real)
    (identified : Identified problem stronger target) :
    Identified problem weaker target := by
  rcases identified with ⟨model, compatible, query_eq⟩
  exact ⟨model,
    compatible_antitone stronger weaker refinement
      (problem.graph model) compatible,
    query_eq⟩

/-- A lower bound valid under weaker graph knowledge remains valid after adding
required or forbidden edge information. -/
theorem valid_lower_bound_survives_refinement
    {Node Model : Type*}
    (problem : DiagramQueryProblem Node Model)
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (lower : Real)
    (valid : IsValidLowerBound
      (asIdentificationProblem problem weaker) lower) :
    IsValidLowerBound
      (asIdentificationProblem problem stronger) lower := by
  exact valid_lower_bound_of_outer_relaxation
    (asIdentificationProblem problem stronger)
    (asIdentificationProblem problem weaker)
    (fun _ => rfl)
    (fun model feasible =>
      compatible_antitone stronger weaker refinement
        (problem.graph model) feasible)
    lower valid

/-- The upper-bound counterpart of graph-information refinement. -/
theorem valid_upper_bound_survives_refinement
    {Node Model : Type*}
    (problem : DiagramQueryProblem Node Model)
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (upper : Real)
    (valid : IsValidUpperBound
      (asIdentificationProblem problem weaker) upper) :
    IsValidUpperBound
      (asIdentificationProblem problem stronger) upper := by
  exact valid_upper_bound_of_outer_relaxation
    (asIdentificationProblem problem stronger)
    (asIdentificationProblem problem weaker)
    (fun _ => rfl)
    (fun model feasible =>
      compatible_antitone stronger weaker refinement
        (problem.graph model) feasible)
    upper valid

/-- If the stronger family attains its exact lower endpoint, it cannot lie
below any lower bound valid for the weaker family. -/
theorem lower_endpoint_monotone_under_refinement
    {Node Model : Type*}
    (problem : DiagramQueryProblem Node Model)
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (weakerLower strongerLower : Real)
    (weaker_valid : IsValidLowerBound
      (asIdentificationProblem problem weaker) weakerLower)
    (strongerWitness : Model)
    (stronger_feasible :
      Compatible stronger (problem.graph strongerWitness))
    (stronger_value :
      problem.query strongerWitness = strongerLower) :
    weakerLower <= strongerLower := by
  exact outer_lower_bound_below_inner_witness
    (asIdentificationProblem problem stronger)
    (asIdentificationProblem problem weaker)
    (fun _ => rfl)
    (fun model feasible =>
      compatible_antitone stronger weaker refinement
        (problem.graph model) feasible)
    weakerLower strongerLower weaker_valid
    strongerWitness stronger_feasible stronger_value

/-- If the stronger family attains its exact upper endpoint, it cannot exceed
any upper bound valid for the weaker family. -/
theorem upper_endpoint_monotone_under_refinement
    {Node Model : Type*}
    (problem : DiagramQueryProblem Node Model)
    (stronger weaker : PartialCausalDiagram Node)
    (refinement : Refines stronger weaker)
    (weakerUpper strongerUpper : Real)
    (weaker_valid : IsValidUpperBound
      (asIdentificationProblem problem weaker) weakerUpper)
    (strongerWitness : Model)
    (stronger_feasible :
      Compatible stronger (problem.graph strongerWitness))
    (stronger_value :
      problem.query strongerWitness = strongerUpper) :
    strongerUpper <= weakerUpper := by
  exact inner_witness_below_outer_upper_bound
    (asIdentificationProblem problem stronger)
    (asIdentificationProblem problem weaker)
    (fun _ => rfl)
    (fun model feasible =>
      compatible_antitone stronger weaker refinement
        (problem.graph model) feasible)
    weakerUpper strongerUpper weaker_valid
    strongerWitness stronger_feasible stronger_value

#print axioms compatible_antitone
#print axioms identified_set_antitone
#print axioms lower_endpoint_monotone_under_refinement
#print axioms upper_endpoint_monotone_under_refinement

end D5.S3.ConceptDynamics.Causal.PartialIdentification.PartialGraphInformationOrder
