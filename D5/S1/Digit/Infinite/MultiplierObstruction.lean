/- GID: D5/S1/Digit/Infinite/MultiplierObstruction
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/MultiplierObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Multiplication by every natural number at least two has no continuous extension to legal infinite digit streams. -/

import D5.S1.Digit.Infinite.SignedSeriesFibres
import D5.S1.Digit.GoldenZeckendorfLanguage
import D5.S1.Digit.Raw
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.MultiplierObstruction

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit
open scoped Topology
open Filter

/-- The Zeckendorf digit row of a natural number, indexed by Fibonacci weights starting at one. -/
def zRow (n : ℕ) : LegalDigits :=
  ⟨fun j => decide (zeckendorfBit n j = 1), by
    intro j h
    have gap := D5.S1.Digit.GoldenZeckendorfLanguage.canonical_indices_not_adjacent
      (Nat.zeckendorf n) (Nat.isZeckendorfRep_zeckendorf n) (j + 2)
    have h0 : zeckendorfBit n j = 1 := of_decide_eq_true h.1
    have h1 : zeckendorfBit n (j + 1) = 1 := of_decide_eq_true h.2
    apply gap
    constructor
    · by_contra hj
      simp [zeckendorfBit, D5.S0.Conventions.wdigits, hj] at h0
    · by_contra hj
      simp [zeckendorfBit, D5.S0.Conventions.wdigits, Nat.add_assoc] at h1
      exact hj h1⟩

/-- The signed value of a legal digit stream, taken modulo one. -/
noncomputable def phase (x : LegalDigits) : AddCircle (1 : ℝ) := signedValue x

/-- No continuous self-map of the legal streams multiplies every natural digit row by m ≥ 2. -/
set_option maxHeartbeats 800000 in
theorem multiplier_obstruction (m : ℕ) (hm : 2 ≤ m) :
    ¬ ∃ M : LegalDigits → LegalDigits, Continuous M ∧
      ∀ n, M (zRow n) = zRow (m * n) := by
  sorry

end D5.S1.Digit.Infinite.MultiplierObstruction
