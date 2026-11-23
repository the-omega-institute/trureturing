/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Data/Tail3
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:finite-exact-certificate)
   anchors: []
   utility: none
   digest: Exact tail constants for a block of labels. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Core

/-! Input data for checks inside the main smooth-predecessor theorem proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

/-- Label inputs for tail block 3. -/
def tailLabels3 : List Nat :=
  ((oddPrimes.drop 20).take 4)

/-- Tail constants for tail block 3. -/
def tailBlock3 : List (Nat × Nat × Nat) :=
  (tails.drop 20).take 4

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
