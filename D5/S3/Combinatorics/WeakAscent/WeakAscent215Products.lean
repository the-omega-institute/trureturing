/- GID: D5/S3/Combinatorics/WeakAscent/WeakAscent215Products
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WeakAscent/WeakAscent215Products
   mirror-E: none(waiver:bigraded-ordered-pure-history-products)
   anchors: [mathlib/module/Mathlib.RingTheory.PowerSeries.Basic]
   utility: none
   digest: Defines the pure-history enumerator by exact length and total gap expenditure. -/

import D5.S3.Combinatorics.WeakAscent.WeakAscent215Pieces
import D5.S3.Combinatorics.WeakAscent.WeakAscent215Finite
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.WeakAscent.WeakAscent215Products

open WeakAscent215Pure WeakAscent215Pieces WeakAscent215Finite

noncomputable def pureSeries : PowerSeries (PowerSeries ℕ) :=
  PowerSeries.mk fun total => PowerSeries.mk fun size =>
    Nat.card {history : PureHistory // history.val.length = size ∧ spend history.val = total}

end D5.S3.Combinatorics.WeakAscent.WeakAscent215Products
