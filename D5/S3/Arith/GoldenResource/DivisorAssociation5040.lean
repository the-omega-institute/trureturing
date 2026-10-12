/- GID: D5/S3/Arith/GoldenResource/DivisorAssociation5040
   generality: I
   mirror-B: none(waiver:finite-5040-bridge)
   mirror-E: none(waiver:finite-5040-bridge)
   anchors: []
   utility: none
   digest: The 5040 divisor cardinality and the association source/image cardinalities are explicit exact anchors. -/

import D5.S3.Arith.GoldenResource.DivisorAssociationFiber
import D5.S3.Arith.GoldenResource.GoldenDivisorLanguage
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.GoldenResource.DivisorAssociation5040

open D5.S3.Arith.GoldenResource.DivisorAssociationFiber
open D5.S3.Arith.GoldenResource.GoldenDivisorLanguage

/-- The finite source box has the expected product cardinality. -/
theorem box_card (A B C D : ℕ) :
    (box A B C D).card = (A + 1) * (B + 1) * (C + 1) * (D + 1) := by
  simp [box, Finset.card_product, Finset.card_range]
  ring

/-- The four-prime exponent box for 5040 has exactly sixty sources. -/
theorem box_card_5040 : (box 4 2 1 1).card = 60 := by
  rw [box_card]

/-- The diagonal association quotient of the 5040 box has forty-eight positions. -/
theorem image_card_5040 : ((box 4 2 1 1).image q).card = 48 := by
  rw [image_card]

/-- The existing positive-divisor count is exactly the source-box count. -/
theorem divisor_5040_card_eq_box_card :
    Nat.card (GoldenDivisorLanguage.Div 5040) = (box 4 2 1 1).card := by
  rw [divisor_5040_card, box_card_5040]

end D5.S3.Arith.GoldenResource.DivisorAssociation5040
