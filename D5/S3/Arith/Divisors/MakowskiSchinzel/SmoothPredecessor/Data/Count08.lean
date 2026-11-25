/- GID: D5/S3/Arith/Divisors/MakowskiSchinzel/SmoothPredecessor/Data/Count08
   generality: I
   mirror-B: none(waiver:source-only-implementation)
   mirror-E: none(waiver:finite-exact-certificate)
   anchors: []
   utility: none
   digest: A block of frontier nodes for candidate enumeration. -/

import D5.S3.Arith.Divisors.MakowskiSchinzel.SmoothPredecessor.Core

/-! Frontier nodes whose weighted smooth folds are summed in one block. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor

/-- Enumeration frontier block 8. -/
def nodes08 : List (List Nat × Nat) :=
  [([3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41,
    43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97], 16)]

end D5.S3.Arith.MakowskiSchinzel.SmoothPredecessor
