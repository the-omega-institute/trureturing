/- GID: D5/S0/History/FiniteDescriptionSelfCode
   generality: G
   mirror-B: D5/B/S0/History/FiniteDescriptionSelfCode
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Finite descriptions correspond exactly to their natural-number self-codes. -/

import Mathlib.Logic.Equiv.List

/- Provenance: thin honest wrapper over pinned mathlib's encoding-range
   equivalence (`Encodable.equivRangeEncode`) and its bundled bijectivity
   theorem (`Equiv.bijective`). -/

namespace D5.S0.History.FiniteDescriptionSelfCode

/-- A finite low-level description is a finite bit string. -/
abbrev FiniteDescription := List Bool

/-- The code space contains exactly the natural numbers produced by encoding
finite descriptions. Membership is carried in the subtype. -/
abbrev DescriptionCode :=
  Set.range (Encodable.encode : FiniteDescription -> Nat)

/-- A finite description paired with the proof that its natural code belongs
to the exact code range. -/
def selfEncoding : FiniteDescription ≃ DescriptionCode :=
  Encodable.equivRangeEncode FiniteDescription

/-- Finite descriptions admit lossless self-codes: the typed encoding is both
injective and surjective onto the exact code space. -/
theorem finite_description_self_encoding_bijective :
    Function.Bijective selfEncoding :=
  selfEncoding.bijective

end D5.S0.History.FiniteDescriptionSelfCode
