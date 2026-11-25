/- GID: D5/S3/ConceptDynamics/Transport/EffectiveImageNaturality
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Transport/EffectiveImageNaturality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Transport factorization is natural on the effective image. -/

module
prelude
public import OmegaInit.Core

namespace D5.S3.ConceptDynamics.Transport.EffectiveImageNaturality

open Omega

/-- A coordinate is in the effective image when some input reads out to it. -/
public def EffectiveImage {Input : Type u} {Output : Type v}
    (readout : Input → Output) (coordinate : Output) : Prop :=
  Exists (fun input => Eq (readout input) coordinate)

/-- A natural transport square descends through the readout factorizations
on the effective image of the first readout. -/
public theorem effective_image_naturality
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
    ∀ y, EffectiveImage C y → Eq (Ymap (f y)) (fPrime (Bmap y)) :=
  fun _y inImage => inImage.elim (fun x readout =>
    have commutes := (congrArg Ymap (hFactor x).symm).trans
      ((hTransport x).symm.trans ((hFactorPrime (Xmap x)).trans (congrArg fPrime (hReadout x))))
    Eq.subst (fun coordinate => Eq (Ymap (f coordinate)) (fPrime (Bmap coordinate)))
      readout commutes)

/-- Identity maps on the Booleans realize all four pointwise premises. -/
example :
    let readout : Bool → Bool := fun x => x
    And (∀ x, Eq (readout x) x)
      (And (∀ x, Eq (readout (readout x)) (readout (readout x)))
        (And (∀ x, Eq (readout x) (readout (readout x)))
          (∀ x, Eq (readout x) (readout (readout x))))) :=
  And.intro (fun _ => Eq.refl)
    (And.intro (fun _ => Eq.refl) (And.intro (fun _ => Eq.refl) (fun _ => Eq.refl)))

example : Bool → Bool := fun x => x

end D5.S3.ConceptDynamics.Transport.EffectiveImageNaturality
