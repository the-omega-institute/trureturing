/- GID: D5/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transportability/EffectiveImageNaturalitySurjectiveLift
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effective-image naturality lifts globally for a surjective readout. -/

module
prelude
public import D5.S3.ConceptDynamics.Transport.EffectiveImageNaturality

namespace D5.S3.ConceptDynamics.Transportability.EffectiveImageNaturalitySurjectiveLift

open Omega
open D5.S3.ConceptDynamics.Transport.EffectiveImageNaturality

/-- Surjectivity makes image-local naturality hold on the entire codomain. -/
public theorem effective_image_naturality_and_surjective_lift
    {XE : Type u₁} {XEPrime : Type u₂} {YE : Type v₁} {YEPrime : Type v₂}
    {WE : Type w₁} {WEPrime : Type w₂}
    (C : XE → YE) (CPrime : XEPrime → YEPrime)
    (T : XE → WE) (TPrime : XEPrime → WEPrime)
    (f : YE → WE) (fPrime : YEPrime → WEPrime)
    (Xmap : XE → XEPrime) (Bmap : YE → YEPrime) (Ymap : WE → WEPrime)
    (hTransport : ∀ x, Eq (TPrime (Xmap x)) (Ymap (T x)))
    (hReadout : ∀ x, Eq (CPrime (Xmap x)) (Bmap (C x)))
    (hFactor : ∀ x, Eq (T x) (f (C x)))
    (hFactorPrime : ∀ x, Eq (TPrime x) (fPrime (CPrime x))) :
    And (∀ y, EffectiveImage C y → Eq (Ymap (f y)) (fPrime (Bmap y)))
      ((∀ y, EffectiveImage C y) → ∀ y, Eq (Ymap (f y)) (fPrime (Bmap y))) :=
  have onImage := effective_image_naturality C CPrime T TPrime f fPrime
    Xmap Bmap Ymap hTransport hReadout hFactor hFactorPrime
  And.intro onImage (fun surjective y => onImage y (surjective y))

end D5.S3.ConceptDynamics.Transportability.EffectiveImageNaturalitySurjectiveLift
