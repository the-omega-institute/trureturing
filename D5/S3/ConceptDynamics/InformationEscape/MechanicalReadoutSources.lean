/- GID: D5/S3/ConceptDynamics/InformationEscape/MechanicalReadoutSources
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MechanicalReadoutSources
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Independent real mechanical observations retain all analytic parameters. -/

import D5.S1.Words.Mechanical.MechanicalBalance
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.MechanicalReadoutSources

open Set MeasureTheory
open scoped BigOperators
open D5.S1.Words.Mechanical

abbrev PrefixOutput := (ℕ → ℝ) → ℝ → ℝ → ℕ → ℝ
abbrev CompletionOutput := (ℝ → ℝ → ℝ → ℝ) × (ℝ → ℝ → ℝ → ℕ → ℝ)
abbrev SlopeOutput := ℝ → ℝ → ℕ → Set ℝ
abbrev PhaseOutput := ℝ → ℝ → ℕ → ℝ → ENNReal
abbrev SeriesOutput :=
  (ℝ → ℝ → ℝ → ℝ) × (ℝ → ℝ) × (ℝ → ℝ → ℝ → ℝ)

def slopeReadout (alpha beta : ℝ) (n : ℕ) : Set ℝ :=
  {x | x ∈ Set.Ico 0 1 ∧ ∃ k : Fin n,
    lowerMechanicalWord beta x k.val ≠ lowerMechanicalWord alpha x k.val}

def phaseReadout (alpha delta : ℝ) (n : ℕ) (u : ℝ) : ENNReal :=
  volume {x : ℝ | x ∈ Set.Ico 0 1 ∧ ∃ k : Fin n,
    lowerMechanicalWord (alpha + delta) (x + u) k.val ≠
      lowerMechanicalWord alpha x k.val}

def actualPrefix (weights : ℕ → ℝ) (alpha x : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, weights j * (lowerMechanicalLetter alpha x j : ℝ)

def completedReadout (r alpha x : ℝ) : ℝ :=
  ∑' k : ℕ, ((1 - r) * r ^ k) * (lowerMechanicalLetter alpha x k : ℝ)

def finitePrefixReadout (r alpha x : ℝ) (n : ℕ) : ℝ :=
  actualPrefix (fun j => (1 - r) * r ^ j) alpha x n

def actualCompletion : CompletionOutput :=
  (completedReadout, finitePrefixReadout)

def floorSeriesReadout (r alpha x : ℝ) : ℝ :=
  ∑' j : ℕ, (1 - r) ^ 2 * r ^ j *
    (⌊x + ((j + 1 : ℕ) : ℝ) * alpha⌋ : ℝ)

def coefficientMassReadout (r : ℝ) : ℝ :=
  ∑' j : ℕ, (1 - r) ^ 2 * r ^ j * ((j + 1 : ℕ) : ℝ)

def thresholdSeriesReadout (r alpha x : ℝ) : ℝ :=
  ∑' j : ℕ, (1 - r) ^ 2 * r ^ j *
    (∑ i ∈ Finset.range (j + 1),
      if (((i + 1 : ℕ) : ℝ) - x) / ((j + 1 : ℕ) : ℝ) ≤ alpha then
        (1 : ℝ) else 0)

def seriesReadout : SeriesOutput :=
  (floorSeriesReadout, coefficientMassReadout, thresholdSeriesReadout)

abbrev AtomicIndex := Σ n : ℕ, Fin (n + 1)

def atomicPoint (x : ℝ) (a : AtomicIndex) : ℝ :=
  (((a.2.val + 1 : ℕ) : ℝ) - x) / (((a.1 + 1 : ℕ) : ℝ))

def atomicCoefficient (r : ℝ) (a : AtomicIndex) : ℝ :=
  (1 - r) ^ 2 * r ^ a.1

def geometricAtomicMeasure (r x : ℝ) : Measure ℝ :=
  Measure.sum fun a : AtomicIndex =>
    ENNReal.ofReal (atomicCoefficient r a) • Measure.dirac (atomicPoint x a)

structure MassInput where
  ratio : ℝ
  phase : ℝ

def massReadout (input : MassInput) : ENNReal × ENNReal :=
  (geometricAtomicMeasure input.ratio input.phase Set.univ,
    geometricAtomicMeasure input.ratio input.phase (Set.Ioc (0 : ℝ) 1))

def massTarget (input : MassInput) : ENNReal × ENNReal :=
  by
    classical
    exact if 0 ≤ input.ratio ∧ input.ratio < 1 ∧
        input.phase ∈ Set.Ico (0 : ℝ) 1 then (1, 1) else massReadout input

abbrev MassOutput := MassInput → ENNReal × ENNReal

structure DistributionInput where
  ratio : ℝ
  threshold : ℝ
  phase : ℝ

def distributionReadout (input : DistributionInput) : ENNReal :=
  geometricAtomicMeasure input.ratio input.phase (Set.Iic input.threshold)

def distributionTarget (input : DistributionInput) : ENNReal :=
  by
    classical
    exact if 0 ≤ input.ratio ∧ input.ratio < 1 ∧
        input.threshold ∈ Set.Icc (0 : ℝ) 1 ∧ input.phase ∈ Set.Ico (0 : ℝ) 1 then
      ENNReal.ofReal (completedReadout input.ratio input.threshold input.phase)
    else distributionReadout input

abbrev DistributionOutput := DistributionInput → ENNReal

structure HitInput where
  ratio : ℝ
  phase : ℝ
  threshold : ℝ

def hitReadout (input : HitInput) : ENNReal :=
  geometricAtomicMeasure input.ratio input.phase {input.threshold}

def hitTarget (input : HitInput) : ENNReal :=
  by
    classical
    exact if input.phase ∈ Set.Ico (0 : ℝ) 1 ∧
        input.threshold ∈ Set.Ioo (0 : ℝ) 1 then
      ∑' n : ℕ, if ∃ z : ℤ,
          (z : ℝ) = input.phase + (((n + 1 : ℕ) : ℝ)) * input.threshold then
        ENNReal.ofReal ((1 - input.ratio) ^ 2 * input.ratio ^ n) else 0
    else hitReadout input

abbrev HitOutput := HitInput → ENNReal

structure SupportInput where
  ratio : ℝ
  phase : ℝ

def supportReadout (input : SupportInput) : Set ℝ :=
  (geometricAtomicMeasure input.ratio input.phase).support

def supportTarget (input : SupportInput) : Set ℝ :=
  by
    classical
    exact if 0 < input.ratio ∧ input.ratio < 1 ∧
        input.phase ∈ Set.Ico (0 : ℝ) 1 then
      Set.Icc (0 : ℝ) 1 else supportReadout input

abbrev SupportOutput := SupportInput → Set ℝ
abbrev JumpOutput := ℝ → ℝ → ℝ → ℝ

def jumpReadout (r alpha x : ℝ) : ℝ := completedReadout r alpha x

structure PhaseAverageInput where
  ratio : ℝ
  ratioPositive : 0 < ratio
  ratioBelowOne : ratio < 1
  target : Set ℝ
  targetMeasurable : MeasurableSet target
  targetInUnit : target ⊆ Set.Icc (0 : ℝ) 1

def phaseAverageIntegral (input : PhaseAverageInput) : ENNReal :=
  ∫⁻ x in Set.Ico (0 : ℝ) 1,
    geometricAtomicMeasure input.ratio x input.target ∂volume

def phaseAverageVolume (input : PhaseAverageInput) : ENNReal :=
  volume input.target

abbrev PhaseAverageOutput := PhaseAverageInput → ENNReal

end D5.S3.ConceptDynamics.InformationEscape.MechanicalReadoutSources
