/- GID: D5/S3/ConceptDynamics/Causal/PartialIdentification/QueryOrderLinearExtension
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Causal/PartialIdentification/QueryOrderLinearExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every certified query-implied partial order admits a linear extension preserving all nontrivial counterfactual precedence obligations. -/

import D5.S3.ConceptDynamics.Causal.PartialIdentification.QueryImpliedCausalOrder
import Mathlib.Order.Extension.Linear

/- Library-search audit trail (2026-09-03):
   * `QueryImpliedCausalOrder` extracts intervention-to-outcome precedence
     obligations and rejects reciprocal requirements, but does not construct a
     complete order in which structural response signatures can be indexed.
   * The repository already uses Mathlib's `extend_partialOrder` for a finite
     Pareto quotient. No causal truth source applies the same theorem to
     query-generated order obligations.
   * This module proves only the extension interface. Soundness of a subsequent
     response-signature LP and invariance across alternative extensions remain
     separate proof obligations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Causal.PartialIdentification.QueryOrderLinearExtension

open D5.S3.ConceptDynamics.Causal.PartialIdentification.QueryImpliedCausalOrder

universe u

/-- A partial-order certificate containing every precedence obligation emitted
by a counterfactual query. The relation is reflexive at the order level. The
separate source-target disequality records that emitted obligations are
nontrivial. -/
structure QueryPartialOrder
    (Node : Type u) [DecidableEq Node]
    (query : CounterfactualQuery Node) where
  relation : Node -> Node -> Prop
  partialOrder : IsPartialOrder Node relation
  containsRequirement : forall {source target},
    QueryRequiresBefore query source target -> relation source target

/-- Every query-generated precedence obligation relates two distinct nodes. -/
theorem query_requirement_source_ne_target
    {Node : Type u} [DecidableEq Node]
    (query : CounterfactualQuery Node)
    {source target : Node}
    (required : QueryRequiresBefore query source target) :
    source ≠ target := by
  rcases required with ⟨atom, _atom_in_query,
    _source_intervened, source_ne_outcome, target_eq⟩
  subst target
  exact source_ne_outcome

/-- A chosen Szpilrajn linear extension of the certified query partial order. -/
noncomputable def linearExtensionRelation
    {Node : Type u} [DecidableEq Node]
    (query : CounterfactualQuery Node)
    (certificate : QueryPartialOrder Node query) :
    Node -> Node -> Prop := by
  letI : IsPartialOrder Node certificate.relation := certificate.partialOrder
  exact (extend_partialOrder certificate.relation).choose

/-- The chosen extension is a linear order relation. -/
theorem linearExtensionRelation_linear
    {Node : Type u} [DecidableEq Node]
    (query : CounterfactualQuery Node)
    (certificate : QueryPartialOrder Node query) :
    IsLinearOrder Node (linearExtensionRelation query certificate) := by
  letI : IsPartialOrder Node certificate.relation := certificate.partialOrder
  simpa [linearExtensionRelation] using
    (extend_partialOrder certificate.relation).choose_spec.1

/-- The chosen linear order contains the certified partial order. -/
theorem linearExtensionRelation_extends
    {Node : Type u} [DecidableEq Node]
    (query : CounterfactualQuery Node)
    (certificate : QueryPartialOrder Node query) :
    forall {left right},
      certificate.relation left right ->
        linearExtensionRelation query certificate left right := by
  letI : IsPartialOrder Node certificate.relation := certificate.partialOrder
  intro left right related
  exact (extend_partialOrder certificate.relation).choose_spec.2 left right related

/-- Every query-implied intervention-to-outcome requirement survives in the
chosen total extension and remains a strict node-level precedence obligation. -/
theorem query_requirement_respected_by_linear_extension
    {Node : Type u} [DecidableEq Node]
    (query : CounterfactualQuery Node)
    (certificate : QueryPartialOrder Node query)
    {source target : Node}
    (required : QueryRequiresBefore query source target) :
    linearExtensionRelation query certificate source target /\
      source ≠ target := by
  constructor
  · exact linearExtensionRelation_extends query certificate
      (certificate.containsRequirement required)
  · exact query_requirement_source_ne_target query required

/-- A complete order suitable for indexing canonical response functions exists
whenever the query obligations have already been embedded in a partial order.
The theorem packages linearity, preservation of the full partial order, and
preservation of every query-generated strict requirement. -/
theorem query_partial_order_has_linear_extension
    {Node : Type u} [DecidableEq Node]
    (query : CounterfactualQuery Node)
    (certificate : QueryPartialOrder Node query) :
    exists extension : Node -> Node -> Prop,
      IsLinearOrder Node extension /\
        (forall {left right},
          certificate.relation left right -> extension left right) /\
        (forall {source target},
          QueryRequiresBefore query source target ->
            extension source target /\ source ≠ target) := by
  refine ⟨linearExtensionRelation query certificate,
    linearExtensionRelation_linear query certificate, ?_, ?_⟩
  · exact linearExtensionRelation_extends query certificate
  · intro source target required
    exact query_requirement_respected_by_linear_extension
      query certificate required

#print axioms query_requirement_source_ne_target
#print axioms query_partial_order_has_linear_extension

end D5.S3.ConceptDynamics.Causal.PartialIdentification.QueryOrderLinearExtension
