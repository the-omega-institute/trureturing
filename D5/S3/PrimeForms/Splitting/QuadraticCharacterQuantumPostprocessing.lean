/- GID: D5/S3/PrimeForms/Splitting/QuadraticCharacterQuantumPostprocessing
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/QuadraticCharacterQuantumPostprocessing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Character fibers survive classical processing and quantum preparation. -/

import D5.S3.PrimeForms.Splitting.QuadraticCharacterProfileRedundancy

/- Library-search audit trail (2026-08-27):
   * Exact family hits `triRingImage`, the three named splitting characters, and
     `quadratic_characters_are_three_ring_products_and_fiber_redundant` supply
     the canonical joint output and every quadratic-character fiber equality.
   * Repository body-shape searches for functions factoring through
     `triRingImage`, character postprocessing, and quantum preparation found no
     theorem packaging the downstream no-go statement.
   * Pinned Mathlib supplies ordinary function congruence and composition; no
     domain-specific packaged theorem is needed or available. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.PrimeForms.Splitting.QuadraticCharacterQuantumPostprocessing

open D5.S3.Factorization.Galois.QuadraticObservationBound
open D5.S3.PrimeForms.Splitting.QuadraticCharacterProfileRedundancy
open D5.S3.PrimeForms.Splitting.ThreeRingProfileFibers

/-- Equal three-ring profiles give equal values for the three generating
characters and every quadratic character. Arbitrary classical processing of
that joint profile, quantum preparation from the processed value, and a final
observation therefore still give equal outputs. -/
theorem quadratic_character_quantum_postprocessing_no_go
    (u v : (ZMod 60)ˣ) (hprofile : triRingImage u = triRingImage v) :
    gaussianCharacter u = gaussianCharacter v ∧
      eisensteinCharacter u = eisensteinCharacter v ∧
      goldenCharacter u = goldenCharacter v ∧
      (∀ extra : QuadraticObserver ((ZMod 60)ˣ), extra u = extra v) ∧
      ∀ (ClassicalOutput QuantumState Observation : Type*)
        (classicalPostprocess : ThreeRingProfile -> ClassicalOutput)
        (quantumPrepare : ClassicalOutput -> QuantumState)
        (observe : QuantumState -> Observation),
        observe (quantumPrepare (classicalPostprocess (triRingImage u))) =
          observe (quantumPrepare (classicalPostprocess (triRingImage v))) := by
  have hfiber :
      ∀ extra : QuadraticObserver ((ZMod 60)ˣ), extra u = extra v :=
    fun extra =>
      quadratic_characters_are_three_ring_products_and_fiber_redundant.2.1
        extra u v hprofile
  refine ⟨hfiber gaussianCharacter, hfiber eisensteinCharacter,
    hfiber goldenCharacter, hfiber, ?_⟩
  intro ClassicalOutput QuantumState Observation classicalPostprocess
    quantumPrepare observe
  exact congrArg (observe ∘ quantumPrepare ∘ classicalPostprocess) hprofile

#print axioms quadratic_character_quantum_postprocessing_no_go

end D5.S3.PrimeForms.Splitting.QuadraticCharacterQuantumPostprocessing
