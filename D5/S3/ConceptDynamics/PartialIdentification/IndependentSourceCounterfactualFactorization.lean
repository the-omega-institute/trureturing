/- GID: D5/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/PartialIdentification/IndependentSourceCounterfactualFactorization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Certified counterfactual source separation yields product event laws directly under elementary independent disturbance distributions, with no separately supplied block-law factorization premise. -/

import D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping
import D5.S3.ConceptDynamics.PartialIdentification.SeparatedCounterfactualSourceFactorization

/- Library audit (2026-09-06): reuse the existing source-locality compiler,
   partitionedReadoutLaw, and compiled_counterfactual_events_factorize.
   The new equality identifies their partitioned source representation with
   the actual pushforward of independentSourceLaw on Source → Noise.
   No structural equations, evaluation relation, or counterfactual noise copy
   are introduced. This is sufficient source separation, not a complete
   counterfactual-identification algorithm. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.PartialIdentification.IndependentSourceCounterfactualFactorization

open D5.S3.ConceptDynamics.Causal.ParentOrderedStructuralEvaluationSemantics
open D5.S3.ConceptDynamics.PartialIdentification.InterventionExogenousLocality
open D5.S3.ConceptDynamics.PartialIdentification.MarkovianResponseLawFactorization
open D5.S3.ConceptDynamics.PartialIdentification.FiniteIndependentSourceGrouping
open D5.S3.ConceptDynamics.PartialIdentification.SeparatedCounterfactualSourceFactorization

variable {Source Noise : Type*} [DecidableEq Source] [Fintype Source] [Fintype Noise]

/-- The original readout law equals the partitioned representation for every
partition, using component laws derived from the same elementary source family. -/
theorem independentSource_pair_readout_eq_partitioned
    {LeftResponse RightResponse : Type*}
    [Fintype LeftResponse] [Fintype RightResponse]
    [DecidableEq LeftResponse] [DecidableEq RightResponse]
    (laws : Source → FiniteResponseLaw Noise) (support : Finset Source)
    (leftReadout : (Source → Noise) → LeftResponse)
    (rightReadout : (Source → Noise) → RightResponse) :
    (pushforwardResponseLaw (independentSourceLaw laws)
      (fun u => (leftReadout u, rightReadout u))).mass =
    (partitionedReadoutLaw support
      (independentSourceLaw (fun i : {i : Source // i ∈ support} => laws i.1))
      (independentSourceLaw (fun i : {i : Source // i ∉ support} => laws i.1))
      leftReadout rightReadout).mass := by
  exact independentSource_pushforward_regroup laws support
    (fun u => (leftReadout u, rightReadout u))

/-- Disjoint supported readouts factorize under the full elementary product law. -/
theorem independentSource_separated_readouts_factorize
    {LeftResponse RightResponse : Type*}
    [Fintype LeftResponse] [Fintype RightResponse]
    [DecidableEq LeftResponse] [DecidableEq RightResponse]
    [Nonempty LeftResponse] [Nonempty RightResponse]
    (laws : Source → FiniteResponseLaw Noise)
    (leftSupport rightSupport : Finset Source)
    (leftReadout : (Source → Noise) → LeftResponse)
    (rightReadout : (Source → Noise) → RightResponse)
    (left_local : DependsOn leftReadout (leftSupport : Set Source))
    (right_local : DependsOn rightReadout (rightSupport : Set Source))
    (separated : Disjoint leftSupport rightSupport) :
    IsMarkovianTwoComponentLaw
      (pushforwardResponseLaw (independentSourceLaw laws)
        (fun u => (leftReadout u, rightReadout u))).mass := by
  rw [independentSource_pair_readout_eq_partitioned laws leftSupport leftReadout rightReadout]
  exact separated_readouts_factorize leftSupport rightSupport
    (independentSourceLaw (fun i : {i : Source // i ∈ leftSupport} => laws i.1))
    (independentSourceLaw (fun i : {i : Source // i ∉ leftSupport} => laws i.1))
    leftReadout rightReadout left_local right_local separated

/-- Every joint response cell equals the product of its actual marginals on the
original full-source law. Boolean benefit is the cell (true,true). -/
theorem independentSource_separated_readouts_cell_eq_product
    {LeftResponse RightResponse : Type*}
    [Fintype LeftResponse] [Fintype RightResponse]
    [DecidableEq LeftResponse] [DecidableEq RightResponse]
    [Nonempty LeftResponse] [Nonempty RightResponse]
    (laws : Source → FiniteResponseLaw Noise)
    (leftSupport rightSupport : Finset Source)
    (leftReadout : (Source → Noise) → LeftResponse)
    (rightReadout : (Source → Noise) → RightResponse)
    (left_local : DependsOn leftReadout (leftSupport : Set Source))
    (right_local : DependsOn rightReadout (rightSupport : Set Source))
    (separated : Disjoint leftSupport rightSupport)
    (left : LeftResponse) (right : RightResponse) :
    let joint := (pushforwardResponseLaw (independentSourceLaw laws)
      (fun u => (leftReadout u, rightReadout u))).mass
    joint (left, right) = leftResponseMarginal joint left * rightResponseMarginal joint right := by
  dsimp only
  rw [independentSource_pair_readout_eq_partitioned laws leftSupport leftReadout rightReadout]
  exact separated_readouts_cell_eq_product leftSupport rightSupport
    (independentSourceLaw (fun i : {i : Source // i ∈ leftSupport} => laws i.1))
    (independentSourceLaw (fun i : {i : Source // i ∉ leftSupport} => laws i.1))
    leftReadout rightReadout left_local right_local separated left right

/-- End-to-end structural theorem from elementary mutually independent sources.
The support compiler and the existing structural evaluation are unchanged;
block independence is now a derived equality for the full source law. -/
theorem compiled_counterfactual_events_independent_sources
    {n : Nat} {Value LeftQuery RightQuery : Type*}
    [Fintype LeftQuery] [Fintype RightQuery]
    (laws : Source → FiniteResponseLaw Noise)
    (model : StructuralModel n Value (Source → Noise)) (topological : TopologicalOrder model)
    (direct : Fin n → Finset Source) (locality : ExogenousLocality model direct)
    (leftInterventions : LeftQuery → Finset (Fin n))
    (leftAssigned : LeftQuery → Fin n → Value) (leftObserved : LeftQuery → Fin n)
    (leftEvent : (LeftQuery → Value) → Bool)
    (rightInterventions : RightQuery → Finset (Fin n))
    (rightAssigned : RightQuery → Fin n → Value) (rightObserved : RightQuery → Fin n)
    (rightEvent : (RightQuery → Value) → Bool)
    (separated : Disjoint
      (counterfactualSupport model direct leftInterventions leftObserved)
      (counterfactualSupport model direct rightInterventions rightObserved)) :
    IsMarkovianTwoComponentLaw
      (pushforwardResponseLaw (independentSourceLaw laws)
        (fun u =>
          (leftEvent (counterfactualReadout model topological
            leftInterventions leftAssigned leftObserved u),
           rightEvent (counterfactualReadout model topological
            rightInterventions rightAssigned rightObserved u)))).mass := by
  rw [independentSource_pair_readout_eq_partitioned laws
    (counterfactualSupport model direct leftInterventions leftObserved)]
  exact compiled_counterfactual_events_factorize model topological direct locality
    leftInterventions leftAssigned leftObserved leftEvent
    rightInterventions rightAssigned rightObserved rightEvent separated
    (independentSourceLaw (fun i : {i : Source //
      i ∈ counterfactualSupport model direct leftInterventions leftObserved} => laws i.1))
    (independentSourceLaw (fun i : {i : Source //
      i ∉ counterfactualSupport model direct leftInterventions leftObserved} => laws i.1))

#print axioms independentSource_pair_readout_eq_partitioned
#print axioms independentSource_separated_readouts_factorize
#print axioms independentSource_separated_readouts_cell_eq_product
#print axioms compiled_counterfactual_events_independent_sources

end D5.S3.ConceptDynamics.PartialIdentification.IndependentSourceCounterfactualFactorization
