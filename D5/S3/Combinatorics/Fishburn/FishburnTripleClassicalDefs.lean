/- GID: D5/S3/Combinatorics/Fishburn/FishburnTripleClassicalDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTripleClassicalDefs
   mirror-E: none(waiver:fixed-fishburn-triple-versus-classical-statement-definition)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Egge's Conjecture 10.10 on one Fishburn and two classical triple-avoidance classes. -/

import D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTripleClassicalDefs

open D5.S3.Combinatorics
open D5.S3.Combinatorics.Fishburn.FishburnClassicalDefs (classicalAvoiders)

/-! Fixed public statement: Egge, *Pattern-Avoiding Fishburn Permutations and Ascent
    Sequences*, arXiv:2208.01484v1, §10, Conjecture 10.10.  `F_n(B)` is
    `FishburnDefs.avoiders` and `S_n(B)` is `FishburnClassicalDefs.classicalAvoiders`. -/

/-- Conjecture 10.10: for `n ≥ 0`,
    `|F_n(2143, 1423, 3124)| = |S_n(321, 2143, 3124)| = |S_n(231, 4132, 2134)|`. -/
def claim1010 : Prop :=
  ∀ n : ℕ,
    (FishburnDefs.avoiders n [[2, 1, 4, 3], [1, 4, 2, 3], [3, 1, 2, 4]]).ncard =
      (classicalAvoiders n [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]).ncard ∧
    (classicalAvoiders n [[3, 2, 1], [2, 1, 4, 3], [3, 1, 2, 4]]).ncard =
      (classicalAvoiders n [[2, 3, 1], [4, 1, 3, 2], [2, 1, 3, 4]]).ncard

end D5.S3.Combinatorics.Fishburn.FishburnTripleClassicalDefs
