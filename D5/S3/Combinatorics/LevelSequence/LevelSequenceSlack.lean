/- GID: D5/S3/Combinatorics/LevelSequence/LevelSequenceSlack
   generality: G
   mirror-B: D5/B/S3/Combinatorics/LevelSequence/LevelSequenceSlack
   mirror-E: none(waiver:slack-continuation-counting)
   anchors: [mathlib/module/Mathlib.Data.Finite.Sigma]
   utility: none
   digest: Virtual zero prefixes define the length-graded slack continuation family. -/

import D5.S3.Combinatorics.LevelSequence.LevelSequenceSpine
import Mathlib.Data.Finite.Sigma

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.LevelSequence.LevelSequenceSlack

open LevelSequenceDefs LevelSequenceDescent LevelSequenceSpine

def continuations (slack size : ℕ) : Set (List ℕ) :=
  {tail | tail.length = size ∧ IsLevel (List.replicate slack 0 ++ tail) ∧
    (¬ Contains101 tail ∧ ¬ Contains102 tail) ∧ (tail = [] ∨ 0 < tail.getD 0 0)}

end D5.S3.Combinatorics.LevelSequence.LevelSequenceSlack
