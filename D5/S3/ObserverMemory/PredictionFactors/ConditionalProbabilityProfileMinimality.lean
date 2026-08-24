/- GID: D5/S3/ObserverMemory/PredictionFactors/ConditionalProbabilityProfileMinimality
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/PredictionFactors/ConditionalProbabilityProfileMinimality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every sufficient interface uniquely descends onto the full conditional-law profile. -/

import D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization
import Mathlib.Probability.ProbabilityMassFunction.Basic

/- Library-search audit trail (2026-08-24):
   * Exact family hit `causal_state_factorization` constructs the unique map
     from a sufficient interface image to the realized future-law image and
     proves separation of unequal future laws. It is applied directly.
   * Exact repository hits `Concept`, `Refines`, and `Set.rangeFactorization`
     provide the canonical concept, refinement, and image-valued maps; no
     sibling primitive is redeclared.
   * Pinned-Mathlib exact hit `PMF` in
     `ProbabilityMassFunction.Basic` is the source's discrete probability
     simplex carrier. Repository searches for conditional laws, predictive
     sufficiency, and probability profiles found no theorem specializing the
     canonical factorization to `PMF Y` while retaining finite source states.
   * `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.PredictionFactors.ConditionalProbabilityProfileMinimality

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ObserverMemory.PredictionFactors.CausalStateFactorization

/-- For a finite state space, a concept through which the complete conditional
law factors has a unique realized-image map onto the conditional-law concept.
That map recovers the supplied predictor and every full probability profile,
and distinct profiles must remain distinct at the concept interface. -/
theorem conditional_probability_profile_is_minimal
    {X Y Interface : Type*} [Fintype X]
    (kernel : Concept X (PMF Y)) (interface : Concept X Interface)
    (predictor : Interface -> PMF Y)
    (sufficient : kernel = predictor ∘ interface) :
    (∃! factor : Set.range interface -> Set.range kernel,
      Set.rangeFactorization kernel =
          factor ∘ Set.rangeFactorization interface ∧
        (∀ state, (factor state : PMF Y) = predictor state.1) ∧
        kernel =
          (fun law : Set.range kernel => (law : PMF Y)) ∘
            factor ∘ Set.rangeFactorization interface) ∧
      ∀ x x', kernel x ≠ kernel x' -> interface x ≠ interface x' := by
  rcases causal_state_factorization interface kernel predictor sufficient with
    ⟨⟨factor, ⟨factorizes, factorMatches⟩, unique⟩, separates⟩
  refine ⟨⟨factor, ⟨factorizes, factorMatches, ?_⟩, ?_⟩, separates⟩
  · funext state
    change kernel state = (factor (Set.rangeFactorization interface state) : PMF Y)
    exact congrArg Subtype.val (congrFun factorizes state)
  · intro candidate candidateProperties
    exact unique candidate ⟨candidateProperties.1, candidateProperties.2.1⟩

#print axioms conditional_probability_profile_is_minimal

end D5.S3.ObserverMemory.PredictionFactors.ConditionalProbabilityProfileMinimality
