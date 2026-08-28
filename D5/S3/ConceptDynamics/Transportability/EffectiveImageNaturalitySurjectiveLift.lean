/- GID: D5/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effective-image naturality lifts globally for a surjective readout. -/

import D5.S3.ConceptDynamics.Transport.EffectiveImageNaturality

/- Library-search audit trail (2026-08-26):
   * Exact repository hit `effective_image_naturality` supplies naturality on
     the range of the source readout and is applied directly.
   * Repository searches for a theorem adding the surjective global lift
     found no exact hit. The lift is immediate from the public surjectivity
     premise and the imported image-local theorem.
   * Pinned Mathlib supplies `Function.Surjective` and `Set.range`; no thinner
     source-shaped theorem packages both public clauses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Transportability.EffectiveImageNaturalitySurjectiveLift

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.Transport.EffectiveImageNaturality

/-- A natural transport square descends through both factorizations on the
effective image. If the first readout is surjective, the same equation holds on
its entire codomain. -/
theorem effective_image_naturality_and_surjective_lift
    {XE XEPrime YE YEPrime WE WEPrime : Type*}
    (C : Concept XE YE) (CPrime : Concept XEPrime YEPrime)
    (T : Concept XE WE) (TPrime : Concept XEPrime WEPrime)
    (f : Concept YE WE) (fPrime : Concept YEPrime WEPrime)
    (Xmap : Concept XE XEPrime)
    (Bmap : Concept YE YEPrime)
    (Ymap : Concept WE WEPrime)
    (h_transport : Function.comp TPrime Xmap = Function.comp Ymap T)
    (h_readout : Function.comp CPrime Xmap = Function.comp Bmap C)
    (h_factor : T = Function.comp f C)
    (h_factorPrime : TPrime = Function.comp fPrime CPrime) :
    (forall y, y ∈ Set.range C -> Ymap (f y) = fPrime (Bmap y)) /\
      (Function.Surjective C -> forall y, Ymap (f y) = fPrime (Bmap y)) := by
  have onEffectiveImage := effective_image_naturality C CPrime T TPrime f fPrime
    Xmap Bmap Ymap h_transport h_readout h_factor h_factorPrime
  refine ⟨onEffectiveImage, ?_⟩
  intro surjective y
  obtain ⟨x, rfl⟩ := surjective y
  exact onEffectiveImage (C x) ⟨x, rfl⟩

#print axioms effective_image_naturality_and_surjective_lift

end D5.S3.ConceptDynamics.Transportability.EffectiveImageNaturalitySurjectiveLift
