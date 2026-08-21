/- GID: D5/S3/ObserverMemory/Refinement/CanonicalMapIdentityComposition
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Refinement/CanonicalMapIdentityComposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical maps between predictive completions satisfy identity and composition. -/

import D5.S3.ObserverMemory.Refinement.CascadeCompletion

/- Library-search audit trail (2026-08-21):
   * Repository exact hits `CompletedState`, `completionFactor`, and
     `completion_factor_projection` provide the source-semantic quotient carriers,
     induced map, and representative projection equation; they are applied below.
   * The exact repository hit `observation_refinement_completion` is used by
     `completionFactor` to construct the factor map from the refinement relation.
   * Pinned Mathlib searches found no theorem packaging these identity and
     composition equations; quotient induction and function extensionality are
     used for the remaining equality of maps.
-/

namespace D5.S3.ObserverMemory.Refinement.CanonicalMapIdentityComposition

open D5.S3.ObserverMemory.Refinement.PredictionCompletion
open D5.S3.ObserverMemory.Refinement.CascadeCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The canonical map induced by a factorization of one readout through another. -/
def canonicalMap {Y O P : Type*}
    (update : Y → Y) (fine : Y → O) (coarse : Y → P)
    (forget : O → P) (hfactor : coarse = forget ∘ fine) :
    CompletedState update fine → CompletedState update coarse :=
  completionFactor update fine coarse forget hfactor

/-- Canonical maps of predictive completions have the identity and composition laws. -/
theorem canonical_map_identity_and_composition
    {Y : Type*} [Finite Y] [Nonempty Y] (update : Y → Y) :
    (∀ {O : Type*} (readout : Y → O),
      canonicalMap update readout readout (id : O → O) (by rfl) = id) ∧
      (∀ {O P A : Type*}
        (fine : Y → O) (middle : Y → P) (coarse : Y → A)
        (forgetQR : O → P) (forgetRS : P → A)
        (hQR : middle = forgetQR ∘ fine)
        (hRS : coarse = forgetRS ∘ middle)
        (hQS : coarse = (forgetRS ∘ forgetQR) ∘ fine),
        canonicalMap update fine coarse (forgetRS ∘ forgetQR) hQS =
          canonicalMap update middle coarse forgetRS hRS ∘
            canonicalMap update fine middle forgetQR hQR) := by
  constructor
  · intro O readout
    funext state
    refine Quotient.inductionOn' state (fun y => ?_)
    change completionFactor update readout readout id (by rfl)
        (completionProjection update readout y) =
      completionProjection update readout y
    exact completion_factor_projection update readout readout id (by rfl) y
  · intro O P A fine middle coarse forgetQR forgetRS hQR hRS hQS
    funext state
    refine Quotient.inductionOn' state (fun y => ?_)
    calc
      canonicalMap update fine coarse (forgetRS ∘ forgetQR) hQS
          (completionProjection update fine y) =
        completionProjection update coarse y := by
          change completionFactor update fine coarse (forgetRS ∘ forgetQR) hQS
              (completionProjection update fine y) =
            completionProjection update coarse y
          exact completion_factor_projection update fine coarse
            (forgetRS ∘ forgetQR) hQS y
      _ = canonicalMap update middle coarse forgetRS hRS
          (completionProjection update middle y) := by
        symm
        change completionFactor update middle coarse forgetRS hRS
            (completionProjection update middle y) =
          completionProjection update coarse y
        exact completion_factor_projection update middle coarse forgetRS hRS y
      _ = canonicalMap update middle coarse forgetRS hRS
          (canonicalMap update fine middle forgetQR hQR
            (completionProjection update fine y)) := by
        rw [show canonicalMap update fine middle forgetQR hQR
              (completionProjection update fine y) =
            completionProjection update middle y by
          change completionFactor update fine middle forgetQR hQR
              (completionProjection update fine y) =
            completionProjection update middle y
          exact completion_factor_projection update fine middle forgetQR hQR y]

/- The finite and nonempty carrier hypotheses are inherited from the source setup;
   the map laws themselves use the quotient semantics rather than those instances. -/
#print axioms canonical_map_identity_and_composition

end D5.S3.ObserverMemory.Refinement.CanonicalMapIdentityComposition
