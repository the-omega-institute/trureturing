/- GID: D5/S3/Combinatorics/Permutation/WordAscents
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/WordAscents
   mirror-E: none(waiver:word-statistic-definition)
   anchors: [mathlib/module/Mathlib.Data.Finset.Card]
   utility: none
   digest: Strict adjacent-ascent count for arbitrary natural-valued words. -/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.List.GetD

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.WordAscents

/-- Adjacent strict ascents, with the final position excluded.
The empty word and every singleton have no adjacent positions. -/
def asc (w : List ℕ) : ℕ :=
  ((Finset.range (w.length - 1)).filter (fun i => w.getD i 0 < w.getD (i + 1) 0)).card

end D5.S3.Combinatorics.Permutation.WordAscents
