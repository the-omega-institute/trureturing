/- GID: D5/S3/Combinatorics/PopStack/PopStackContinuation
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PopStack/PopStackContinuation
   mirror-E: none(waiver:ordinary-prefix-continuation)
   anchors: []
   utility: none
   digest: Ordinary prefix continuation inserts the value above the second entry at the front. -/

import D5.S3.Combinatorics.PopStack.PopStackDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.PopStack.PopStackContinuation

open PopStackDefs

def W (permutation : List ℕ) : List ℕ :=
  (permutation.getD 1 0 + 1) :: permutation.map
    (fun entry => if permutation.getD 1 0 < entry then entry + 1 else entry)


end D5.S3.Combinatorics.PopStack.PopStackContinuation
