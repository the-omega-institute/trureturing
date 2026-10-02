/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFourAChildren
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFourAChildren
   mirror-E: none(waiver:a-parameterized-insertion-counting)
   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: Identity and positive-cut labels classify the A generating-tree nodes. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFourAInvariant
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFourAChildren

open D5.S3.Combinatorics FishburnDefs

inductive Label
  | I
  | P (run : ℕ)
  | Q (sites : ℕ)
  deriving DecidableEq

noncomputable def label (n : ℕ) (p : List ℕ) : Label := by
  classical
  let sites := Nat.card {cut : ℕ // 0 < cut ∧ cut ≤ p.length ∧
    p.insertIdx cut (n + 1) ∈ avoiders (n + 1) [[1, 3, 2, 4], [2, 1, 4, 3]]}
  exact if p = List.range' 1 n then .I else if p.getD 0 0 = 1 then .P sites else .Q sites

end D5.S3.Combinatorics.Fishburn.FishburnTenFourAChildren
