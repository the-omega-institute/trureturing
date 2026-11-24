/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Data/Tail1
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

/-- Label inputs for tail block 1. -/
def tailLabels1 : List Nat :=
  ((oddPrimes.drop 10).take 5)

/-- Tail constants for tail block 1. -/
def tailBlock1 : List (Nat × Nat × Nat) :=
  (tails.drop 10).take 5

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
