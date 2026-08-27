/- GID: D5/S3/ObserverMemory/PredictionFactors/PositiveConditioningPredictionStability
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/PositiveConditioningPredictionStability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Equal discrete future laws remain equal after conditioning on a positive next outcome. -/

import D5.S3.Divergence.ChainRule

/- Library-search audit trail (2026-08-28):
   * Body-shape searches for finite normalization found the canonical repository
     primitives `marginal` and `conditional` in `Divergence.ChainRule`; they are
     imported instead of redeclared.
   * The closest frozen declaration,
     `posterior_update_depends_only_on_posterior`, is congruence under literal
     equality of an already constructed posterior. It does not expose histories,
     future protocols, joint transcript laws, or history extension.
   * Repository searches for predictive equivalence under positive conditioning
     and pinned-Mathlib searches around conditional probability found no theorem
     packaging the finite joint-law statement below. Pinned Mathlib supplies the
     ordered-field cancellation used after the positive marginal is established. -/

namespace D5.S3.ObserverMemory.PredictionFactors.PositiveConditioningPredictionStability

open D5.S3.Divergence.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- In a finite discrete law model, equal complete joint laws at two histories
remain equal after a common positive-probability action outcome. The public
coherence equations say that the outcome law is the joint-law marginal and that
extending a history realizes the canonical conditional law. -/
theorem predictive_equivalence_preserved_by_positive_conditioning
    {History Action Observation Protocol FutureRecord : Type*}
    [Fintype FutureRecord]
    (jointLaw : History -> Action -> Protocol -> Observation × FutureRecord -> Real)
    (outcomeLaw : History -> Action -> Observation -> Real)
    (futureLaw : History -> Protocol -> FutureRecord -> Real)
    (extendHistory : History -> Action -> Observation -> History)
    (marginalConsistent : forall history action protocol,
      marginal (jointLaw history action protocol) = outcomeLaw history action)
    (conditioned : forall history action observation protocol futureRecord,
      futureLaw (extendHistory history action observation) protocol futureRecord =
        conditional (jointLaw history action protocol) observation futureRecord)
    {history history' : History}
    (samePrediction : forall action protocol,
      jointLaw history action protocol = jointLaw history' action protocol)
    (action : Action) (observation : Observation)
    (positive : 0 < outcomeLaw history action observation) :
    forall protocol,
      futureLaw (extendHistory history action observation) protocol =
        futureLaw (extendHistory history' action observation) protocol := by
  intro protocol
  funext futureRecord
  rw [conditioned, conditioned]
  have sameJoint := samePrediction action protocol
  have sameNumerator :
      jointLaw history action protocol (observation, futureRecord) =
        jointLaw history' action protocol (observation, futureRecord) :=
    congrFun sameJoint (observation, futureRecord)
  have sameMarginal :
      marginal (jointLaw history action protocol) observation =
        marginal (jointLaw history' action protocol) observation :=
    congrArg (fun law => marginal law observation) sameJoint
  have denominatorNonzero :
      marginal (jointLaw history action protocol) observation ≠ 0 := by
    rw [marginalConsistent]
    exact ne_of_gt positive
  have otherDenominatorNonzero :
      marginal (jointLaw history' action protocol) observation ≠ 0 := by
    rw [← sameMarginal]
    exact denominatorNonzero
  rw [conditional]
  apply (div_eq_div_iff denominatorNonzero otherDenominatorNonzero).2
  rw [sameNumerator, sameMarginal]

#print axioms predictive_equivalence_preserved_by_positive_conditioning

end D5.S3.ObserverMemory.PredictionFactors.PositiveConditioningPredictionStability
