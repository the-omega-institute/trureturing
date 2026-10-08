/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base6x8/Data
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base6x8/Data
   mirror-E: none(waiver:semilinear-packing-construction)
   anchors: []
   utility: none
   digest: A periodic table for arbitrarily repeated arc prefixes. -/

import D5.S3.Combinatorics.PathAlignedPacking.Schemes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base6x8.Data

open Schemes

def scheme : Scheme where
  a := 6
  b := 8
  period := 4
  colours := 5
  pumpA := true
  pumpB := true
  colour := ![![4, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 1],
      ![5, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 1],
      ![5, 1, 2, 1, 3, 1, 4, 1, 2, 1, 3, 1, 2, 1],
      ![5, 1, 2, 1, 3, 1, 5, 1, 2, 1, 3, 1, 2, 1]]

end D5.S3.Combinatorics.PathAlignedPacking.Base6x8.Data
