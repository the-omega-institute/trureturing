/- GID: D5/S1/Digit/Infinite/PhaseOrbitRelations
   generality: I
   mirror-B: D5/B/S1/Digit/Infinite/PhaseOrbitRelations
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eventual merging of legal streams agrees with circle rotation orbits and phase fibres, with exact merging times at negative phases. -/

import D5.S1.Digit.Infinite.MultiplierObstruction
import D5.S1.Digit.Infinite.InfiniteSuccessorFibres
import D5.S1.Digit.Carry.SuccessorShortest
import Mathlib.Topology.DenseEmbedding
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Data.Set.Countable

set_option autoImplicit false

namespace D5.S1.Digit.Infinite.PhaseOrbitRelations

open D5.S1.Digit.Infinite.SuccessorContinuity
open D5.S1.Digit.Infinite.InfiniteSuccessorFibres
open D5.S1.Digit.Infinite.SignedSeriesRange
open D5.S1.Digit.Infinite.SignedSeriesFibres
open D5.S1.Digit.Infinite.MultiplierObstruction
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit D5.S1.Digit.Carry.Successor
open D5.S1.Digit.Carry.SuccessorShortest
open scoped Topology

/-- The successor as a self-map of the legal digit streams. -/
noncomputable def T (x : LegalDigits) : LegalDigits := ⟨next x.val, next_fibres.1 x⟩

/-- Rotation of the circle by the golden ratio modulo one. -/
noncomputable def rotation (t : AddCircle (1 : ℝ)) : AddCircle (1 : ℝ) :=
  t + (Real.goldenRatio : AddCircle (1 : ℝ))

/-- Two circle points belong to the same rotation orbit. -/
def ER (t s : AddCircle (1 : ℝ)) : Prop :=
  ∃ k : ℤ, s = t + k • (Real.goldenRatio : AddCircle (1 : ℝ))

/-- Two legal streams have equal successor iterates at possibly different times. -/
def ET (x y : LegalDigits) : Prop := ∃ m n : ℕ, T^[m] x = T^[n] y

/-- Two legal streams have equal successor iterates at the same time. -/
def ST (x y : LegalDigits) : Prop := ∃ k : ℕ, T^[k] x = T^[k] y

/-- Two legal streams have the same phase on the circle. -/
def QH (x y : LegalDigits) : Prop := phase x = phase y

set_option maxHeartbeats 800000 in
/-- The eventual-merging relations correspond to rotation orbits and phase fibres. Both orbit
relations are countable Borel equivalence relations. Distinct streams of phase minus j times the
rotation angle merge at the zero row after exactly j successor steps, for every positive j. -/
theorem phase_orbit_relations :
    Equivalence ER ∧ Equivalence ET ∧
    (∀ t, Set.Countable {s | ER t s}) ∧
    (∀ x, Set.Countable {y | ET x y}) ∧
    MeasurableSet {p : AddCircle (1 : ℝ) × AddCircle (1 : ℝ) | ER p.1 p.2} ∧
    @MeasurableSet (LegalDigits × LegalDigits) (borel (LegalDigits × LegalDigits))
      {p | ET p.1 p.2} ∧
    (∀ x y, ET x y ↔ ER (phase x) (phase y)) ∧
    (∀ x y, ST x y ↔ phase x = phase y) ∧
    (∀ j : ℕ, 1 ≤ j → ∀ x y : LegalDigits,
      phase x = -(j • (Real.goldenRatio : AddCircle (1 : ℝ))) →
      phase y = -(j • (Real.goldenRatio : AddCircle (1 : ℝ))) →
      T^[j] x = zRow 0 ∧ T^[j] y = zRow 0 ∧
      (x ≠ y → ∀ i < j, T^[i] x ≠ T^[i] y)) := by
  sorry

end D5.S1.Digit.Infinite.PhaseOrbitRelations
