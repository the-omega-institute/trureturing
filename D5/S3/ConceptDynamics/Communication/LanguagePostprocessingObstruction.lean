/- GID: D5/S3/ConceptDynamics/Communication/LanguagePostprocessingObstruction
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Communication/LanguagePostprocessingObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Processing a language readout cannot recover a distinction absent from that readout. -/

import D5.S3.ConceptDynamics.ConceptFiberDecomposition

/- Library-search audit trail (2026-08-22):
   * Exact repository hit `Concept` is the canonical readout primitive and is
     imported from `ConceptFiberDecomposition` rather than redeclared.
   * `heterogeneous_fiber_forces_misclassification` is adjacent but concerns
     target-valued inference errors rather than arbitrary postprocessing outputs.
   * Exact core/library hits `congrArg` and `Function.comp_apply` are applied
     directly. `Function.Injective.of_comp` and `Function.FactorsThrough.comp_left`
     are more global formulations; no theorem packages this named witness pair.
   * Loogle and LeanSearch executables were absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Communication.LanguagePostprocessingObstruction

open D5.S3.ConceptDynamics.ConceptFiberDecomposition

/-- If two states have the same language output but different phenomenon values,
then every postprocessor generated solely from that language output still gives
the two states equal outputs. The arbitrary codomain includes longer, richer, or
recursively interpreted language-only results. -/
theorem language_postprocessing_preserves_missing_distinction
    {X Language Phenomenon Output : Type _}
    (language : Concept X Language) (phenomenon : Concept X Phenomenon)
    (x y : X)
    (missingDistinction : language x = language y ∧ phenomenon x ≠ phenomenon y) :
    ∀ postprocess : Language -> Output,
      (postprocess ∘ language) x = (postprocess ∘ language) y := by
  intro postprocess
  unfold Function.comp
  exact congrArg postprocess missingDistinction.1

/-- A constant language and identity phenomenon readout satisfy the source's
missing-distinction premise, and every language-only postprocessor preserves
the collision. -/
example :
    ∀ postprocess : Unit -> Nat,
      (postprocess ∘ (fun _ : Bool => ())) false =
        (postprocess ∘ (fun _ : Bool => ())) true := by
  exact language_postprocessing_preserves_missing_distinction
    (fun _ : Bool => ()) id false true ⟨rfl, Bool.false_ne_true⟩

/-- Without the language collision premise, a postprocessed output can distinguish
the two states, so the public conclusion is not unconditional. -/
example :
    ((id : Bool -> Bool) ∘ (id : Bool -> Bool)) false ≠
      ((id : Bool -> Bool) ∘ (id : Bool -> Bool)) true := by
  exact Bool.false_ne_true

#print axioms language_postprocessing_preserves_missing_distinction

end D5.S3.ConceptDynamics.Communication.LanguagePostprocessingObstruction
