/- GID: D5/S3/Combinatorics/PopStack/PopStackM3Disjoint
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackM3Disjoint
   mirror-E: none(waiver:first-block-contraction-operation)
   anchors: [mathlib/module/Mathlib.Data.List.Perm.Basic]
   utility: none
   digest: First-block contraction removes the duplicated adjacent rank. -/

import D5.S3.Combinatorics.PopStack.PopStackDecomposition
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackM3Disjoint

open PopStackDefs PopStackInflation PopStackPrime PopStackFamilies

def deflateFirst (permutation : List ℕ) : List ℕ :=
  permutation.getD 1 0 :: (permutation.drop 2).map
    (fun value => if permutation.getD 1 0 < value then value - 1 else value)

end D5.S3.Combinatorics.PopStack.PopStackM3Disjoint
