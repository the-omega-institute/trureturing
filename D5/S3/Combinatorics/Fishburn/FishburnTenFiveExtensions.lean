/- GID: D5/S3/Combinatorics/Fishburn/FishburnTenFiveExtensions
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Fishburn/FishburnTenFiveExtensions
   mirror-E: none(waiver:ranked-history-extension-decomposition)
   anchors: [mathlib/module/Mathlib.Data.Subtype]
   utility: none
   digest: Split a legal future history at its first new insertion and invert the split. -/

import D5.S3.Combinatorics.Fishburn.FishburnTenFiveHistory
import Mathlib.Data.Subtype

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Fishburn.FishburnTenFiveExtensions

open D5.S3.Combinatorics.Fishburn FishburnDefs FishburnTenFiveHistory

def Extensions (patterns : List (List ℕ)) (depth : ℕ) (history : List ℕ) :=
  {later : List ℕ // later.length = depth + history.length ∧
    LegalHistory patterns later ∧ later.drop depth = history}


end D5.S3.Combinatorics.Fishburn.FishburnTenFiveExtensions
