/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenBParameters
   mirror-E: none(waiver:dependent-normal-form-parameters)
   anchors: [mathlib/module/Mathlib.SetTheory.Cardinal.Finite]
   utility: none
   digest: The second class uses initial-one tails or three interval parameters. -/

import D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenAuxiliary
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBParameters

open D5.S3.Combinatorics Nonnesting Fishburn.FishburnDefs
open FishburnTenSevenAuxiliary

def HStart (size : ℕ) := {p : ↥(avoiders size [[2, 1, 3]]) // p.val.head? = some 1}

def BParameters (size : ℕ) :=
  Σ maximum : {maximum : ℕ // 1 ≤ maximum ∧ maximum ≤ size},
    HStart maximum.val ⊕
      (Σ low : {low : ℕ // 2 ≤ low ∧ low < maximum.val},
        Σ _high : {high : ℕ // low.val ≤ high ∧ high < maximum.val},
          ↥(avoiders (low.val - 2) [[2, 1, 3]]))


end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenBParameters
