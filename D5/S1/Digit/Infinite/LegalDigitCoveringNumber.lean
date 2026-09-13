/- GID: D5/S1/Digit/Infinite/LegalDigitCoveringNumber
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/LegalDigitCoveringNumber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The least number of closed digit-distance balls covering legal infinite digits is the Fibonacci prefix count. -/

import D5.S1.Digit.Infinite.SuccessorContinuity
import D5.S1.Words.AdmissibleWords.AdmissibleCount
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.LegalDigitCoveringNumber

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Words.AdmissibleWords.AdmissibleCount

noncomputable def digitDist (theta : ℝ) (x y : LegalDigits) : ℝ :=
  if x = y then 0 else theta ^ PiNat.firstDiff x.val y.val

def covers (theta : ℝ) (L m : ℕ) : Prop :=
  ∃ centers : Fin m → LegalDigits, ∀ x : LegalDigits,
    ∃ i : Fin m, digitDist theta x (centers i) ≤ theta ^ L

/-- The exact minimum cardinality of closed prefix balls in the legal digit space. -/
theorem least_covering_number (theta : ℝ) (hθ0 : 0 < theta) (hθ1 : theta < 1) (L : ℕ) :
    IsLeast {m : ℕ | covers theta L m} (Nat.fib (L + 2)) := by
  sorry

end D5.S1.Digit.Infinite.LegalDigitCoveringNumber
