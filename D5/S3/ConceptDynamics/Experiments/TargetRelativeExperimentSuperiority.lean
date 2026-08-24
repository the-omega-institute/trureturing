/- GID: D5/S3/ConceptDynamics/Experiments/TargetRelativeExperimentSuperiority
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Experiments/TargetRelativeExperimentSuperiority
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Incomparable experiments each admit a target served by one and not the other. -/

import D5.S3.ConceptDynamics.Refinement.RefinementReflexivity

/- Library-search audit trail (2026-08-24):
   * Exact atom-id search across `D5`, `Blueprint`, digestion formalizations, and accepted
     freezes found no prior receipt or declaration.
   * Repository search found the canonical `Concept` and `Refines` primitives in
     `ConceptJoinUniversal` and the exact theorem `refinement_reflexive` in
     `RefinementReflexivity`; this proof imports and applies that theorem directly.
   * Searches for target-relative superiority and incomparable experiment witnesses found
     adjacent experiment-gain results, but no theorem containing both directional witnesses.
   * Local pinned-mathlib search for incomparable existential witnesses found no exact hit;
     external `loogle` and `leansearch` executables are absent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Experiments.TargetRelativeExperimentSuperiority

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.RefinementReflexivity

/-- Incomparable experiments each serve a target that the other experiment does not. -/
theorem incomparable_experiments_have_opposite_target_advantages
    {X E₁ E₂ : Type _} (experiment₁ : Concept X E₁) (experiment₂ : Concept X E₂)
    (incomparable : ¬Refines experiment₁ experiment₂ ∧ ¬Refines experiment₂ experiment₁) :
    (∃ target₁ : Concept X E₁,
        Refines target₁ experiment₁ ∧ ¬Refines target₁ experiment₂) ∧
      (∃ target₂ : Concept X E₂,
        Refines target₂ experiment₂ ∧ ¬Refines target₂ experiment₁) := by
  rcases incomparable with ⟨notFirstThroughSecond, notSecondThroughFirst⟩
  constructor
  · exact ⟨experiment₁, refinement_reflexive experiment₁, notFirstThroughSecond⟩
  · exact ⟨experiment₂, refinement_reflexive experiment₂, notSecondThroughFirst⟩

/-- The incomparability premise is realized by the two coordinate experiments. -/
example :
    let experiment₁ : Concept (Bool × Bool) Bool := Prod.fst
    let experiment₂ : Concept (Bool × Bool) Bool := Prod.snd
    ¬Refines experiment₁ experiment₂ ∧ ¬Refines experiment₂ experiment₁ := by
  dsimp only
  constructor
  · rintro ⟨factor, factors⟩
    have atFalseFalse := congrFun factors (false, false)
    have atTrueFalse := congrFun factors (true, false)
    simp only [Function.comp_apply] at atFalseFalse atTrueFalse
    exact Bool.false_ne_true (atFalseFalse.trans atTrueFalse.symm)
  · rintro ⟨factor, factors⟩
    have atFalseFalse := congrFun factors (false, false)
    have atFalseTrue := congrFun factors (false, true)
    simp only [Function.comp_apply] at atFalseFalse atFalseTrue
    exact Bool.false_ne_true (atFalseFalse.trans atFalseTrue.symm)

#print axioms incomparable_experiments_have_opposite_target_advantages

end D5.S3.ConceptDynamics.Experiments.TargetRelativeExperimentSuperiority
