/- GID: D5/S1/Digit/Infinite/SignedSeriesRange
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SignedSeriesRange
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The signed golden series on legal infinite digits fills an interval with unique alternating endpoints. -/

import D5.S1.Digit.Infinite.SuccessorContinuity
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SignedSeriesRange

open D5.S1.Digit.Infinite.SuccessorContinuity
open scoped Topology

/-- The reciprocal of the golden ratio. -/
noncomputable def alpha : ℝ := Real.goldenRatio⁻¹

/-- The lower endpoint of the signed series interval. -/
noncomputable def a : ℝ := -alpha

/-- The upper endpoint of the signed series interval. -/
noncomputable def b : ℝ := alpha ^ 2

/-- The signed golden series, with digits indexed from low to high. -/
noncomputable def signedValue (x : LegalDigits) : ℝ :=
  ∑' j : ℕ, (-1 : ℝ) ^ (j + 1) * alpha ^ (j + 2) * (if x.val j then 1 else 0)

/-- The alternating stream with ones at the even positions. -/
def u : LegalDigits := ⟨fun i => decide (i % 2 = 0), by
  intro j
  simp only [decide_eq_true_eq]
  omega⟩

/-- The alternating stream with ones at the odd positions. -/
def v : LegalDigits := ⟨fun i => decide (i % 2 = 1), by
  intro j
  simp only [decide_eq_true_eq]
  omega⟩

/-- The signed series fills the closed interval, and each endpoint has its unique alternating stream. -/
theorem signed_series_range : Set.range signedValue = Set.Icc a b ∧
    (∀ x : LegalDigits, signedValue x = a ↔ x = u) ∧
    (∀ x : LegalDigits, signedValue x = b ↔ x = v) := by
  sorry

end D5.S1.Digit.Infinite.SignedSeriesRange
