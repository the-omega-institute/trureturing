/- GID: D5/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/InformationEscape/MechanicalAtomicMeasureRegistration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Atomic measure laws compare complete readout functions on their admissible real parameters. -/

import D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration

open Set MeasureTheory
open D5.S1.Words.Mechanical
open D5.S1.Words.Mechanical.MechanicalReadoutOrder
open D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
open D5.S3.ConceptDynamics.InformationEscape
open PointwiseRegistrationTemplates
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open scoped Topology

structure MassInput where
  ratio : ℝ
  phase : ℝ
  ratioNonnegative : 0 ≤ ratio
  ratioBelowOne : ratio < 1
  phaseInUnit : phase ∈ Ico (0 : ℝ) 1

def massReadout (input : MassInput) : ENNReal × ENNReal :=
  (geometricAtomicMeasure input.ratio input.phase Set.univ,
    geometricAtomicMeasure input.ratio input.phase (Ioc (0 : ℝ) 1))

def massTarget (_ : MassInput) : ENNReal × ENNReal := (1, 1)

abbrev MassOutput := MassInput → ENNReal × ENNReal

structure DistributionInput where
  ratio : ℝ
  threshold : ℝ
  phase : ℝ
  ratioNonnegative : 0 ≤ ratio
  ratioBelowOne : ratio < 1
  thresholdInUnit : threshold ∈ Icc (0 : ℝ) 1
  phaseInUnit : phase ∈ Ico (0 : ℝ) 1

def distributionReadout (input : DistributionInput) : ENNReal :=
  geometricAtomicMeasure input.ratio input.phase (Iic input.threshold)

def distributionTarget (input : DistributionInput) : ENNReal :=
  ENNReal.ofReal (geometricReadout input.ratio input.threshold input.phase)

abbrev DistributionOutput := DistributionInput → ENNReal

structure HitInput where
  ratio : ℝ
  phase : ℝ
  threshold : ℝ
  phaseInUnit : phase ∈ Ico (0 : ℝ) 1
  thresholdInterior : threshold ∈ Ioo (0 : ℝ) 1

def hitReadout (input : HitInput) : ENNReal :=
  geometricAtomicMeasure input.ratio input.phase {input.threshold}

def hitTarget (input : HitInput) : ENNReal :=
  by
    classical
    exact ∑' n : ℕ, if ∃ z : ℤ,
        (z : ℝ) = input.phase + (((n + 1 : ℕ) : ℝ)) * input.threshold then
      ENNReal.ofReal ((1 - input.ratio) ^ 2 * input.ratio ^ n) else 0

abbrev HitOutput := HitInput → ENNReal

structure SupportInput where
  ratio : ℝ
  phase : ℝ
  ratioPositive : 0 < ratio
  ratioBelowOne : ratio < 1
  phaseInUnit : phase ∈ Ico (0 : ℝ) 1

def supportReadout (input : SupportInput) : Set ℝ :=
  (geometricAtomicMeasure input.ratio input.phase).support

def supportTarget (_ : SupportInput) : Set ℝ := Icc (0 : ℝ) 1

abbrev SupportOutput := SupportInput → Set ℝ

private def unitArena := Arena.ofFintype Unit

private def equalityArena (Y : Type) [DecidableEq Y] : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := homogeneousPointwiseEqArena unitArena Y
  Domain := ℝ

local instance : DecidableEq MassOutput := Classical.decEq _
local instance : DecidableEq DistributionOutput := Classical.decEq _
local instance : DecidableEq HitOutput := Classical.decEq _
local instance : DecidableEq SupportOutput := Classical.decEq _

def massArena := equalityArena MassOutput
def distributionArena := equalityArena DistributionOutput
def hitArena := equalityArena HitOutput
def supportArena := equalityArena SupportOutput

def massRealization := homogeneousPointwiseEqRealization
  (fun _ : Unit => massReadout) (fun _ : Unit => massTarget)
def distributionRealization := homogeneousPointwiseEqRealization
  (fun _ : Unit => distributionReadout) (fun _ : Unit => distributionTarget)
def hitRealization := homogeneousPointwiseEqRealization
  (fun _ : Unit => hitReadout) (fun _ : Unit => hitTarget)
def supportRealization := homogeneousPointwiseEqRealization
  (fun _ : Unit => supportReadout) (fun _ : Unit => supportTarget)

/-- The CUT output keeps the full readout as a function of ratio, slope, and phase. -/
abbrev JumpOutput := ℝ → ℝ → ℝ → ℝ

local instance : DecidableEq JumpOutput := Classical.decEq _

def jumpReadout (_ : Unit) : JumpOutput :=
  fun r alpha x => geometricReadout r alpha x

def leftJumpArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq JumpOutput := Classical.decEq _
    exact {
      toArena := unitArena
      signature := mechanicalReadoutSignature JumpOutput
      Law := fun realization => by
        classical
        exact ∀ (r x alpha : ℝ), 0 < r → r < 1 →
          x ∈ Ico (0 : ℝ) 1 → alpha ∈ Ioo (0 : ℝ) 1 →
          ∃ L : ℝ,
            Filter.Tendsto (fun beta : ℝ => realization.readout () () r beta x)
              (𝓝[<] alpha) (𝓝 L) ∧
            L = (geometricAtomicMeasure r x (Iio alpha)).toReal ∧
            realization.readout () () r alpha x - L =
              ∑' n : ℕ, if ∃ z : ℤ,
                  (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha then
                (1 - r) ^ 2 * r ^ n else 0 }
  Domain := ℝ

def rationalJumpArena : ObjectDomainArena.{0, 0, 0, 0} where
  toPrimitiveLawArena := by
    letI : DecidableEq JumpOutput := Classical.decEq _
    exact {
      toArena := unitArena
      signature := mechanicalReadoutSignature JumpOutput
      Law := fun realization => ∀ (r : ℝ) (p q : ℕ), 0 < r → r < 1 →
        0 < p → p < q → Nat.Coprime p q →
        ∃ L : ℝ,
          Filter.Tendsto (fun beta : ℝ => realization.readout () () r beta 0)
            (𝓝[<] ((p : ℝ) / q)) (𝓝 L) ∧
          realization.readout () () r ((p : ℝ) / q) 0 - L =
            (1 - r) ^ 2 * r ^ (q - 1) / (1 - r ^ q) }
  Domain := ℝ

def jumpRealization := @mechanicalReadoutRealization JumpOutput
  (Classical.decEq _) jumpReadout

end D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration
