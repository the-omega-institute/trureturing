/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base7x7/Data
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base7x7/Data
   mirror-E: none(waiver:semilinear-packing-construction)
   anchors: []
   utility: none
   digest: A periodic table for arbitrarily repeated arc prefixes. -/

import D5.S3.Combinatorics.PathAlignedPacking.Schemes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base7x7.Data

open Schemes

def scheme : Scheme where
  a := 7
  b := 7
  period := 4
  colours := 5
  pumpA := true
  pumpB := true
  colour := ![![4, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 2],
      ![5, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 2],
      ![5, 1, 2, 1, 3, 1, 2, 4, 1, 2, 1, 3, 1, 2],
      ![5, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1, 3, 1, 2]]

end D5.S3.Combinatorics.PathAlignedPacking.Base7x7.Data
