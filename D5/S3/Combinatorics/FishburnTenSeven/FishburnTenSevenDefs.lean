/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenDefs
   mirror-E: none(waiver:fixed-fishburn-triple-avoidance-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Egge's Conjecture 10.7 on three Fishburn triple-avoidance classes counted by 2^n - n. -/

import D5.S3.Combinatorics.Fishburn.FishburnDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenDefs

open D5.S3.Combinatorics.Fishburn

/-! Fixed public statement: Egge, *Pattern-Avoiding Fishburn Permutations and Ascent
    Sequences*, arXiv:2208.01484v1, §10, Conjecture 10.7.  `F_n(B)` is
    `FishburnDefs.avoiders`. -/

/-- Conjecture 10.7: for `n ≥ 1`, `|F_n(1324, 2143, 1423)| = |F_n(1324, 2143, 3124)| =
    |F_n(1324, 1423, 3124)| = 2^n - n`. -/
def claim107 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (FishburnDefs.avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [1, 4, 2, 3]]).ncard = 2 ^ n - n ∧
    (FishburnDefs.avoiders n [[1, 3, 2, 4], [2, 1, 4, 3], [3, 1, 2, 4]]).ncard = 2 ^ n - n ∧
    (FishburnDefs.avoiders n [[1, 3, 2, 4], [1, 4, 2, 3], [3, 1, 2, 4]]).ncard = 2 ^ n - n

end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenDefs
