/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFourBTree
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFourBTree
   mirror-E: none(waiver:b-disjoint-path-enumeration)
   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Recursive disjoint I/X/Y paths retain the distinct B branching edges. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFourBTree

inductive Label
  | I
  | X
  | Y

def Paths : ℕ → Label → Type
  | 0, _ => Unit
  | depth + 1, .I => (Paths depth .Y ⊕ Paths depth .Y) ⊕ Paths depth .I
  | depth + 1, .X => Paths depth .X ⊕ Paths depth .X
  | depth + 1, .Y => (Paths depth .Y ⊕ Paths depth .Y) ⊕ Paths depth .X


end D5.S3.Combinatorics.Fishburn.FishburnTenFourBTree
