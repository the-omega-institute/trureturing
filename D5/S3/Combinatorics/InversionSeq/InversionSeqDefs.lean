/- GID: D5/S3/Combinatorics/InversionSeq/InversionSeqDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/InversionSeq/InversionSeqDefs
   mirror-E: none(waiver:fixed-inversion-sequence-pattern-class-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Inversion sequences avoiding sets of length-3 patterns and two open Wilf equivalences. -/

import D5.S3.Combinatorics.Nonnesting.NonnestingDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.InversionSeq.InversionSeqDefs

open D5.S3.Combinatorics

/-! Fixed public statements: Callan–Mansour, *Inversion Sequences Avoiding Quadruple
    Length-3 Patterns*, Integers 23 (2023), #A78, §1, Conjecture 1, Classes 152 and 207.
    An inversion sequence of length `n` is `e₁ ⋯ eₙ` with `0 ≤ eᵢ < i`; positions are
    numbered from 0 in Lean, so the condition reads `e.getD i 0 ≤ i`.  Patterns are written
    on the letters `1, 2, 3` (the source writes `0, 1, 2`); containment records equalities as
    well as the relative order (`NonnestingDefs.Occurs`). -/

/-- `e` is an inversion sequence. -/
def IsInversionSeq (e : List ℕ) : Prop := ∀ i < e.length, e.getD i 0 ≤ i

/-- `I_n(B)`: inversion sequences of length `n` avoiding every pattern of `B`. -/
def avoiders (n : ℕ) (B : List (List ℕ)) : Set (List ℕ) :=
  {e | e.length = n ∧ IsInversionSeq e ∧ ∀ σ ∈ B, ¬ Nonnesting.NonnestingDefs.Occurs σ e}

/-- Class 152: `{010, 100, 102, 210} ∼ {011, 201, 210}`, i.e. equal counts for every `n`. -/
def claim152 : Prop :=
  ∀ n : ℕ, (avoiders n [[1, 2, 1], [2, 1, 1], [2, 1, 3], [3, 2, 1]]).ncard =
    (avoiders n [[1, 2, 2], [3, 1, 2], [3, 2, 1]]).ncard

/-- Class 207: `{100, 101, 110, 201} ∼ {101, 110, 120, 210}`, i.e. equal counts for every `n`. -/
def claim207 : Prop :=
  ∀ n : ℕ, (avoiders n [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]).ncard =
    (avoiders n [[2, 1, 2], [2, 2, 1], [2, 3, 1], [3, 2, 1]]).ncard

end D5.S3.Combinatorics.InversionSeq.InversionSeqDefs
