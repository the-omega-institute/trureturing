/- GID: D5/S1/Digit/Infinite/SharpErrorThreshold
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/SharpErrorThreshold
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Sharp closed and open noise thresholds with residual decision margins. -/

import D5.S1.Digit.Infinite.CriticalPrefixSeparation
import Mathlib.Data.Fintype.Lattice
import Mathlib.Algebra.Order.Archimedean.Basic

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.SharpErrorThreshold

open D5.S1.Digit.Infinite.SuccessorContinuity (LegalDigits)
open D5.S1.Digit.Infinite.ClosedObservationCommonTailWidthModel
open D5.S1.Digit.Infinite.CriticalPrefixSeparation
open Set

/-- Actual full-source records for a fixed incoming guard and an open or closed radius. -/
def records (s : Bool) (h : ℕ) (ε : ℝ) (strict : Bool) : Set (Fin (h + 1) → ℝ) :=
  {r | ∃ x : LegalDigits, stateAddress s x ∧
    if strict then dist r (response h x) < ε else dist r (response h x) ≤ ε}

/-- Every compatible full source must have the decoded prefix. -/
def recovers (s : Bool) (h : ℕ) (ε : ℝ) (strict : Bool)
    (decode : records s h ε strict → (Fin h → Label)) : Prop :=
  ∀ (r : records s h ε strict) (x : LegalDigits), stateAddress s x →
    (if strict then dist r.val (response h x) < ε else dist r.val (response h x) ≤ ε) →
    decode r = windowPrefix h x

/-- The adjacent-sample residual at an observed window. -/
noncomputable def sampleResidual (h : ℕ) (r : Fin (h + 1) → ℝ) (j : Fin h) : ℝ :=
  r ⟨j.val, by omega⟩ + g * r ⟨j.val + 1, by omega⟩

end D5.S1.Digit.Infinite.SharpErrorThreshold
