/- GID: D5/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FishburnTenSeven/FishburnTenSevenWords
   mirror-E: none(waiver:reversal-interchange-language-bijection)
   anchors: [mathlib/module/Mathlib.Data.List.Chain, mathlib/module/Mathlib.Data.Set.Basic]
   utility: none
   digest: Three allocation letters define the two languages and reverse-interchange map. -/

import Mathlib.Data.List.Chain
import Mathlib.Data.Set.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWords

inductive Letter where
  | d
  | i
  | j
  deriving DecidableEq

open Letter

def Before (earlier later : Letter) (word : List Letter) : Prop :=
  word.Pairwise (fun left right => left ≠ later ∨ right ≠ earlier)

def languageA (size : ℕ) : Set (List Letter) :=
  {word | word.length = size ∧
    word.IsChain (fun left right => left ≠ j ∨ right ≠ i) ∧ Before j d word}

def languageC (size : ℕ) : Set (List Letter) :=
  {word | word.length = size ∧
    word.IsChain (fun left right => left ≠ j ∨ right ≠ i) ∧ Before d i word}

def swap : Letter → Letter
  | d => d
  | i => j
  | j => i

def phi (word : List Letter) : List Letter := (word.map swap).reverse


end D5.S3.Combinatorics.FishburnTenSeven.FishburnTenSevenWords
