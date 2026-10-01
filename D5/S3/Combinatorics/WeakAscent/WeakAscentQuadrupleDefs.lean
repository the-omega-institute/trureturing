/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscentQuadrupleDefs
   mirror-E: none(waiver:fixed-weak-ascent-quadruple-pattern-class-definitions)
   anchors: [mathlib/module/Mathlib.Data.Set.Card]
   utility: none
   digest: Weak ascent sequences avoiding sets of length-3 patterns and the open Class 215. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscentDefs
import D5.S3.Combinatorics.Nonnesting.NonnestingDefs
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscentQuadrupleDefs

open D5.S3.Combinatorics

/-! Fixed public statement: Callan–Mansour, *Ascent Sequences and Weak Ascent Sequences
    Avoiding a Quadruple of Length-3 Patterns*, Integers 25 (2025), #A80, §1 and Table 2:
    Class 215, the only unresolved case of the classification.  Weak ascent sequences are
    `WeakAscentDefs.IsWeakAscent`; patterns are written on the letters `1, 2, 3` (the source
    writes `0, 1, 2`) and containment records equalities as well as the relative order
    (`NonnestingDefs.Occurs`). -/

/-- `WA_n(B)`: weak ascent sequences of length `n` avoiding every pattern of `B`. -/
def avoiders (n : ℕ) (B : List (List ℕ)) : Set (List ℕ) :=
  {a | a.length = n ∧ WeakAscentDefs.IsWeakAscent a ∧
    ∀ σ ∈ B, ¬ Nonnesting.NonnestingDefs.Occurs σ a}

/-- Class 215: `{100, 101, 110, 201}` and `{021, 101, 201, 210}` are WA-Wilf-equivalent. -/
def claim215 : Prop :=
  ∀ n : ℕ, (avoiders n [[2, 1, 1], [2, 1, 2], [2, 2, 1], [3, 1, 2]]).ncard =
    (avoiders n [[1, 3, 2], [2, 1, 2], [3, 1, 2], [3, 2, 1]]).ncard

end D5.S3.Combinatorics.WeakAscent.WeakAscentQuadrupleDefs
