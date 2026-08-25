/- GID: D5/S3/ObserverMemory/RefinementDescent/PredictiveSufficiencyDescent
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/RefinementDescent/PredictiveSufficiencyDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Quotient well-definedness and unique induced update/readout squares. -/

import D5.S3.ObserverMemory.Refinement.PredictionCompletion

/- Library-search audit trail (2026-08-25):
   * The frozen family primitives `CompletedState`, `completionProjection`,
     `completionUpdate`, and `completionReadout` are imported directly; no
     quotient or induced-map object is redeclared.
   * The withdrawn `PredictiveSufficiencyDescent.predictive_sufficiency_descent`
     supplied only computation rules. The stronger public representative
     well-definedness and pair uniqueness below were not found in the repository.
   * Pinned Mathlib exact primitives are `Quotient.exact` for the kernel
     relation, `Quotient.mk_surjective` for representative induction, and
     `congrArg`/`congrFun` for the two commuting squares.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.RefinementDescent.PredictiveSufficiencyDescent

open D5.S3.ObserverMemory.Prediction.ItineraryCompletion
open D5.S3.ObserverMemory.Refinement.PredictionCompletion

/-- Complete-future equivalence makes both the induced update and current
readout independent of representatives, and these two induced maps are the
unique pair whose squares commute with the canonical projection. -/
theorem predictive_sufficiency_descent_well_defined_unique
    {X O : Type*} (update : X -> X) (readout : X -> O) :
    (∀ x y,
      completionProjection update readout x =
          completionProjection update readout y ->
        completionProjection update readout (update x) =
            completionProjection update readout (update y) ∧
          readout x = readout y) ∧
      ∃! induced :
        (CompletedState update readout -> CompletedState update readout) ×
          (CompletedState update readout -> O),
        (∀ x,
          induced.1 (completionProjection update readout x) =
            completionProjection update readout (update x)) ∧
        (∀ x,
          induced.2 (completionProjection update readout x) = readout x) := by
  constructor
  · intro x y hxy
    constructor
    · calc
        completionProjection update readout (update x) =
            completionUpdate update readout
              (completionProjection update readout x) := rfl.symm
        _ = completionUpdate update readout
            (completionProjection update readout y) := congrArg _ hxy
        _ = completionProjection update readout (update y) := rfl
    · exact congrFun (Quotient.exact hxy) 0
  · let induced :
        (CompletedState update readout -> CompletedState update readout) ×
          (CompletedState update readout -> O) :=
      (completionUpdate update readout, completionReadout update readout)
    refine ⟨induced, ?_, ?_⟩
    · constructor
      · intro x
        exact rfl
      · intro x
        exact rfl
    · intro candidate hcandidate
      apply Prod.ext
      · funext state
        rcases Quotient.mk_surjective state with ⟨x, rfl⟩
        exact (hcandidate.1 x).trans rfl.symm
      · funext state
        rcases Quotient.mk_surjective state with ⟨x, rfl⟩
        exact (hcandidate.2 x).trans rfl.symm

#print axioms predictive_sufficiency_descent_well_defined_unique

end D5.S3.ObserverMemory.RefinementDescent.PredictiveSufficiencyDescent
