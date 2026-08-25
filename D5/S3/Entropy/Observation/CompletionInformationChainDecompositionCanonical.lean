/- GID: D5/S3/Entropy/Observation/CompletionInformationChainDecompositionCanonical
   generality: G
   mirror-B: D5/B/S3/Entropy/Observation/CompletionInformationChainDecompositionCanonical
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: State the observation chain decomposition through canonical source laws. -/

/- Library-search audit trail (2026-08-25):
   * Pinned Mathlib searches for `conditionalEntropy`, finite Shannon entropy, and a finite
     entropy chain rule found no matching real-valued result.
   * The exact repository hits `entropy_chain_rule`, `shannonEntropy_extend_injective`,
     `finiteWordRangeEquiv`, and `stableCompletionEquiv` are used by the imported frozen
     predecessor.
   * The exact canonical source-law hits `nextReadoutJointLaw`, `completionLaw`, and
     `conceptLaw` are imported directly and occur in the public statement below.
   * No new observation law or completion equivalence is declared in this module.
-/

import D5.S3.ConceptDynamics.Completion.CompletionInformationCost
import D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
import D5.S3.Entropy.Observation.CompletionInformationChainDecomposition
import D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability

namespace D5.S3.Entropy.Observation.CompletionInformationChainDecompositionCanonical

open D5.S3.ConceptDynamics.Completion.CompletionInformationCost
open D5.S3.ConceptDynamics.Information.RefinementEntropyMonotonicity
open D5.S3.Divergence.ChainRule
open D5.S3.Entropy.ConditionalEntropy
open D5.S3.Entropy.Forgetting.CapacityMonotone
open D5.S3.Entropy.MaxEntropy
open D5.S3.Entropy.Observation.CompletionInformationChainDecomposition
open D5.S3.ObserverMemory.Prediction.ConditionalEntropyStability
open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- Every finite observation word obeys the Shannon chain rule. At a stable depth, the
canonical realized-word equivalence computes to the completion projection, and the completion
information conditional on the initial readout is the sum of the later readout increments. -/
theorem completion_information_chain_decomposition_canonical {Y O : Type*}
    [Fintype Y] [Fintype O]
    (update : Y -> Y) (readout : Y -> O) (initial : Y -> Real)
    (hinitial : (forall y, 0 <= initial y) ∧ ∑ y, initial y = 1)
    (stableDepth : Nat)
    (hstable :
      Setoid.ker (futureReadoutWord update readout stableDepth) =
        Setoid.ker (futureReadoutWord update readout (stableDepth + 1))) :
    letI : Fintype (CompletedState update readout) :=
      Fintype.ofFinite (CompletedState update readout)
    (forall depth,
      shannonEntropy (conceptLaw initial (futureReadoutWord update readout depth)) =
        shannonEntropy (conceptLaw initial readout) +
          ∑ k ∈ Finset.range depth,
            conditionalEntropy (nextReadoutJointLaw update readout initial k)) ∧
    (forall y,
      stableObservationCompletionEquiv update readout stableDepth hstable
          ⟨futureReadoutWord update readout stableDepth y, ⟨y, rfl⟩⟩ =
        completionProjection update readout y) ∧
    conditionalEntropy
        (completionLaw initial readout (completionProjection update readout)) =
      ∑ k ∈ Finset.range stableDepth,
        conditionalEntropy (nextReadoutJointLaw update readout initial k) := by
  simpa only [conceptLaw, nextReadoutJointLaw, completionLaw,
    observationWordLaw, initialReadoutLaw, observationIncrementJointLaw,
    completionObservationJointLaw] using
    (completion_information_chain_decomposition update readout initial hinitial
      stableDepth hstable)

#print axioms completion_information_chain_decomposition_canonical

end D5.S3.Entropy.Observation.CompletionInformationChainDecompositionCanonical
