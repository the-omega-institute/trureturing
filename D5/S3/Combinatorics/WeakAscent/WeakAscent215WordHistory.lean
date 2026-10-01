/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215WordHistory
   mirror-E: none(waiver:inverse-word-history-replay)
   anchors: [mathlib/module/Mathlib.Data.Finset.Sort]
   utility: none
   digest: Labels sorted legal numerical sites by occurrence for the inverse history replay. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Sites
import D5.S3.Combinatorics.WeakAscent.WeakAscent215Renewal
import Mathlib.Data.Finset.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215WordHistory

open WeakAscentDefs WeakAscentQuadrupleDefs WeakAscent215Renewal
open WeakAscent215Sites

noncomputable def activeValues (word : List ℕ) : List ℕ := by
  classical
  exact ((Finset.range (word.foldr max 0 + 1)).filter fun value =>
    word ++ [value] ∈
      avoiders (word.length + 1) [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]).sort
noncomputable def activeMarks (word : List ℕ) : List Bool := by
  classical
  exact (activeValues word).map fun value => decide (value ∈ word)
end D5.S3.Combinatorics.WeakAscent.WeakAscent215WordHistory
