/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFourBChildren
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFourBChildren
   mirror-E: none(waiver:b-ranked-insertion-bijection)
   anchors: []
   utility: none
   digest: Canonical B node labels retain the destinations of distinct ranked edges. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFourBInvariant
import D5.S3.Combinatorics.Fishburn.FishburnTenFourBTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFourBChildren

open D5.S3.Combinatorics FishburnDefs FishburnTenFourBTree

noncomputable def label (n : ℕ) (p : List ℕ) : Label := by
  classical
  exact if p = List.range' 1 n then .I else
    if ∃ cut, 0 < cut ∧ cut < n ∧ p.insertIdx cut (n + 1) ∈
      avoiders (n + 1) [[1, 4, 2, 3], [2, 1, 4, 3]] then .Y else .X

def nextLabel : (mark : Label) → Paths 1 mark → Label
  | .I, .inl _ => .Y
  | .I, .inr _ => .I
  | .X, _ => .X
  | .Y, .inl _ => .Y
  | .Y, .inr _ => .X

end D5.S3.Combinatorics.Fishburn.FishburnTenFourBChildren
