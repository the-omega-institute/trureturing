/- GID: D5/S3/Combinatorics/PathAlignedPacking/Base10x1/Data
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PathAlignedPacking/Base10x1/Data
   mirror-E: none(waiver:semilinear-packing-construction)
   anchors: []
   utility: none
   digest: A periodic table for arbitrarily repeated arc prefixes. -/

import D5.S3.Combinatorics.PathAlignedPacking.Schemes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PathAlignedPacking.Base10x1.Data

open Schemes

def scheme : Scheme where
  a := 10
  b := 1
  period := 3
  colours := 5
  pumpA := true
  pumpB := false
  colour := ![![3, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2],
      ![5, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1],
      ![4, 1, 2, 1, 3, 1, 2, 5, 1, 2, 1]]

end D5.S3.Combinatorics.PathAlignedPacking.Base10x1.Data
