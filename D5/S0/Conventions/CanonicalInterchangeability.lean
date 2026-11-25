/- GID: D5/S0/Conventions/CanonicalInterchangeability
   generality: I
   mirror-B: D5/B/S0/Conventions/CanonicalInterchangeability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Faithful digit specifications are canonically interchangeable through decoding. -/

module
prelude
public import OmegaMath.Arithmetic.WDigits.Interchange

namespace D5.S0.Conventions

open Omega Omega.Arithmetic Omega.Arithmetic.WDigits

/-- Faithful digit encodings are canonically interchangeable through their decoded values. -/
public theorem canonical_interchangeability :
    And
      (∀ {Word₁ Word₂ : Type} (source : NumberEncoding Word₁) (destination : NumberEncoding Word₂),
        source.Faithful → destination.Faithful →
        And (_root_.Omega.Arithmetic.WDigits.Bijective (source.transport destination))
          (And (∀ w, Eq (destination.decode (source.transport destination w)) (source.decode w))
            (∀ (predicate : Nat → Prop) w,
              Iff (predicate (source.decode w))
                (predicate (destination.decode (source.transport destination w))))))
      (And (∀ a b, IsCanonical a → IsCanonical b → Eq (decode a) (decode b) → Eq a b)
        (∀ n, Exists fun w => And (IsCanonical w) (Eq (decode w) n))) :=
  And.intro
    (fun source destination hs hd => And.intro (source.transport_bijective destination hs hd)
      (And.intro (source.transport_decode destination hd) (source.transport_predicate destination hd)))
    decode_canonical_bijective

end D5.S0.Conventions
