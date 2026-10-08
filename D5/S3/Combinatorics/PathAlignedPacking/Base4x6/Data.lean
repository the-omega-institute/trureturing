/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base4x6/Data
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base4x6/Data
   mirror-E: none(waiver:semilinear-packing-construction)
   anchors: []
   utility: none
   digest: A periodic table for arbitrarily repeated arc prefixes. -/

import D5.S3.Combinatorics.PathAlignedPacking.Schemes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base4x6.Data

open Schemes

def scheme : Scheme where
  a := 4
  b := 6
  period := 4
  colours := 5
  pumpA := false
  pumpB := true
  colour := ![![1, 2, 1, 3, 4, 1, 2, 1, 3, 4],
      ![1, 2, 1, 3, 4, 1, 2, 1, 3, 5],
      ![1, 2, 1, 3, 4, 1, 2, 1, 3, 5],
      ![2, 1, 3, 1, 5, 1, 2, 1, 3, 1]]

end D5.S3.Combinatorics.PathAlignedPacking.Base4x6.Data
