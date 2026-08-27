/- GID: D5/S3/ObserverMemory/RefinementClosure/PredictiveCompletionMaximalInvariantQuotient
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementClosure/PredictiveCompletionMaximalInvariantQuotient
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The maximal invariant future kernel carries the canonical predictive quotient. -/

import D5.S3.ObserverMemory.Refinement.PredictionCompletion
import D5.S3.ObserverMemory.RefinementClosure.CompletionKernelGreatestFixedPoint

/- Library-search audit trail (2026-08-27):
   * The frozen family theorem `completion_kernel_is_greatest_fixed_point`
     exactly supplies greatest-fixed-point equality, containment in the current
     readout kernel, forward invariance, and maximality; it is applied directly.
   * Existing canonical primitives `CompletedState`, `completionProjection`,
     `completionReadout`, and `completionUpdate` construct the named quotient
     and its descended structure rather than introducing sibling definitions.
   * The frozen greatest-fixed-point theorem alone is not an exact whole hit for
     the source atom because its public statement does not expose the quotient,
     quotient kernel, or descended readout and update.
   * Pinned Mathlib supplies `Quotient.exact`, `Quotient.sound`, and
     `Quotient.mk_surjective` for the quotient-kernel bridge and uniqueness. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.RefinementClosure.PredictiveCompletionMaximalInvariantQuotient

open D5.S3.Observer.Separation.FiniteFutureCongruence
open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open D5.S3.ObserverMemory.RefinementClosure.CompletionKernelGreatestFixedPoint

/-- The equality kernel of the complete future readout is the greatest
forward-invariant relation inside the current readout kernel. Its canonical
kernel quotient uniquely carries both the current readout and source update. -/
theorem predictive_completion_maximal_invariant_quotient
    {Y O : Type*} (tau : Y -> Y) (q : Y -> O) :
    let completedKernel : StateRelation Y :=
      {pair | Setoid.ker (completeItinerary tau q) pair.1 pair.2}
    let projection : Y -> CompletedState tau q := completionProjection tau q
    let projectionKernel : StateRelation Y :=
      {pair | Setoid.ker projection pair.1 pair.2}
    (projectionKernel = completedKernel) ∧
      (completedKernel = (refinementOperator tau q).gfp) ∧
      (completedKernel <= observationKernel q) ∧
      (∀ pair, pair ∈ completedKernel ->
        (tau pair.1, tau pair.2) ∈ completedKernel) ∧
      (∀ relation : StateRelation Y,
        relation <= observationKernel q ->
        (∀ pair, pair ∈ relation ->
          (tau pair.1, tau pair.2) ∈ relation) ->
        relation <= completedKernel) ∧
      (∃! descendedReadout : CompletedState tau q -> O,
        q = descendedReadout ∘ projection) ∧
      ∃! descendedUpdate : CompletedState tau q -> CompletedState tau q,
        projection ∘ tau = descendedUpdate ∘ projection := by
  dsimp only
  have kernelResult := completion_kernel_is_greatest_fixed_point tau q
  rcases kernelResult with
    ⟨kernelGfp, kernelBelow, kernelInvariant, kernelMaximal⟩
  have projectionKernel :
      ({pair | Setoid.ker (completionProjection tau q) pair.1 pair.2} :
          StateRelation Y) =
        {pair | Setoid.ker (completeItinerary tau q) pair.1 pair.2} := by
    ext pair
    constructor
    · intro sameProjection
      exact Quotient.exact sameProjection
    · intro sameItinerary
      exact Quotient.sound sameItinerary
  refine ⟨projectionKernel, kernelGfp, kernelBelow, kernelInvariant,
    kernelMaximal, ?_, ?_⟩
  · let canonicalReadout := completionReadout tau q
    have canonicalFactors :
        q = canonicalReadout ∘ completionProjection tau q := rfl
    refine ⟨canonicalReadout, canonicalFactors, ?_⟩
    intro candidate candidateFactors
    apply Quotient.mk_surjective.injective_comp_right
    exact candidateFactors.symm.trans canonicalFactors
  · let canonicalUpdate := completionUpdate tau q
    have canonicalFactors :
        completionProjection tau q ∘ tau =
          canonicalUpdate ∘ completionProjection tau q := rfl
    refine ⟨canonicalUpdate, canonicalFactors, ?_⟩
    intro candidate candidateFactors
    apply Quotient.mk_surjective.injective_comp_right
    exact candidateFactors.symm.trans canonicalFactors

#print axioms predictive_completion_maximal_invariant_quotient

end D5.S3.ObserverMemory.RefinementClosure.PredictiveCompletionMaximalInvariantQuotient
