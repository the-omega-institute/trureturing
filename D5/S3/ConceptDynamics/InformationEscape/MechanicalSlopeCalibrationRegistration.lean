/- GID: D5/S3/ConceptDynamics/InformationEscape/MechanicalSlopeCalibrationRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MechanicalSlopeCalibrationRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Real-parameter CUT readouts retain local slope disagreement and joint phase mismatch volumes. -/

import D5.S1.Words.Mechanical.MechanicalPhaseCalibration
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration

open Set MeasureTheory
open scoped BigOperators
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalSlopeSensitivity
open D5.S1.Words.Mechanical.MechanicalPhaseCalibration
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

abbrev SlopeOutput := ℝ → ℝ → ℕ → Set ℝ
abbrev PhaseOutput := ℝ → ℝ → ℕ → ℝ → ENNReal

/-- Actual phase sets on which finite words disagree after a slope change. -/
def slopeReadout : SlopeOutput := fun alpha beta n => slopeDisagreement alpha beta n

/-- Volume of phases on which simultaneous slope and phase changes alter a word. -/
def phaseReadout : PhaseOutput :=
  fun alpha delta n u => volume (jointMismatchSet alpha delta n u)

local instance : DecidableEq SlopeOutput := Classical.decEq _
local instance : DecidableEq PhaseOutput := Classical.decEq _

def slopeArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := {
    toArena := Arena.ofFintype Unit
    signature := mechanicalReadoutSignature SlopeOutput
    Law := fun realization => ∀ (alpha : ℝ), Irrational alpha → 0 < alpha →
      alpha < 1 → ∀ (n : ℕ),
      ∃ radius : ℝ, 0 < radius ∧ alpha + radius < 1 ∧
        (∀ lower : ℝ, lower ≤ 1 - alpha →
          (∀ i : Fin n, lower ≤
            1 - Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha)) →
          (∀ i j : Fin n, i ≠ j → lower ≤
            |Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha) -
              Int.fract (((j.val + 1 : ℕ) : ℝ) * alpha)|) →
          lower / (2 * ((n : ℝ) + 1)) ≤ radius) ∧
        ∀ delta : ℝ, 0 ≤ delta → delta ≤ radius →
        let c : Fin n → ℝ := fun i =>
          1 - Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha)
        let swept : Fin n → Set ℝ := fun i =>
          Ico (c i - ((i.val + 1 : ℕ) : ℝ) * delta) (c i)
        realization.readout () () alpha (alpha + delta) n = ⋃ i, swept i ∧
        Pairwise (fun i j => Disjoint (swept i) (swept j)) ∧
        volume (realization.readout () () alpha (alpha + delta) n) =
          ENNReal.ofReal ((n : ℝ) * ((n : ℝ) + 1) / 2 * delta) ∧
        ∀ i x, x ∈ swept i → ∀ j : Fin n,
          lowerMechanicalLetter (alpha + delta) x j.val -
            lowerMechanicalLetter alpha x j.val =
            (if j.val = i.val then (1 : ℤ) else 0) -
              (if j.val = i.val + 1 then (1 : ℤ) else 0)
  }
  Domain := ℝ

def phaseArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := {
    toArena := Arena.ofFintype Unit
    signature := mechanicalReadoutSignature PhaseOutput
    Law := fun realization => ∀ (alpha delta g : ℝ) (n : ℕ), 0 < n →
      0 ≤ alpha → alpha < 1 → 0 ≤ alpha + delta → alpha + delta < 1 →
      0 < g →
      (∀ k : Fin n,
        g ≤ 1 - Int.fract (((k.val + 1 : ℕ) : ℝ) * alpha) ∧
        g ≤ Int.fract (((k.val + 1 : ℕ) : ℝ) * alpha)) →
      (∀ i j : Fin n, i ≠ j →
        g ≤ |Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha) -
          Int.fract (((j.val + 1 : ℕ) : ℝ) * alpha)|) →
      (∀ u : ℝ, (∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) →
        realization.readout () () alpha delta n u =
          ENNReal.ofReal (∑ k : Fin (n + 1), |u + (k.val : ℝ) * delta|)) ∧
      ((n : ℝ) * |delta| ≤ g / 4 →
        (∀ k : Fin (n + 1),
          |-(n : ℝ) * delta / 2 + (k.val : ℝ) * delta| ≤ g / 4) ∧
        realization.readout () () alpha delta n (-(n : ℝ) * delta / 2) =
          ENNReal.ofReal (|delta| * (((n + 1)^2 / 4 : ℕ) : ℝ)) ∧
        ∀ u : ℝ, (∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) →
          realization.readout () () alpha delta n (-(n : ℝ) * delta / 2) ≤
            realization.readout () () alpha delta n u)
  }
  Domain := ℝ

def slopeRealization :=
  @mechanicalReadoutRealization SlopeOutput (Classical.decEq _)
    (fun _ : Unit => slopeReadout)

def phaseRealization :=
  @mechanicalReadoutRealization PhaseOutput (Classical.decEq _)
    (fun _ : Unit => phaseReadout)

end D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration
