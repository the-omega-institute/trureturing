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
import D5.S3.ConceptDynamics.InformationEscape.MechanicalReadoutSources

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

abbrev MassInput := MechanicalReadoutSources.MassInput

def massReadout (input : MassInput) : ENNReal × ENNReal :=
  MechanicalReadoutSources.massReadout input

def massTarget (input : MassInput) : ENNReal × ENNReal :=
  MechanicalReadoutSources.massTarget input

abbrev MassOutput := MassInput → ENNReal × ENNReal

abbrev DistributionInput := MechanicalReadoutSources.DistributionInput

def distributionReadout (input : DistributionInput) : ENNReal :=
  MechanicalReadoutSources.distributionReadout input

def distributionTarget (input : DistributionInput) : ENNReal :=
  MechanicalReadoutSources.distributionTarget input

abbrev DistributionOutput := DistributionInput → ENNReal

abbrev HitInput := MechanicalReadoutSources.HitInput

def hitReadout (input : HitInput) : ENNReal :=
  MechanicalReadoutSources.hitReadout input

def hitTarget (input : HitInput) : ENNReal :=
  MechanicalReadoutSources.hitTarget input

abbrev HitOutput := HitInput → ENNReal

abbrev SupportInput := MechanicalReadoutSources.SupportInput

def supportReadout (input : SupportInput) : Set ℝ :=
  MechanicalReadoutSources.supportReadout input

def supportTarget (input : SupportInput) : Set ℝ :=
  MechanicalReadoutSources.supportTarget input

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

def massRealization := @homogeneousPointwiseEqRealization Unit MassOutput
  (Classical.decEq _)
  (fun _ : Unit => MechanicalReadoutSources.massReadout)
  (fun _ : Unit => MechanicalReadoutSources.massTarget)
def distributionRealization := @homogeneousPointwiseEqRealization Unit DistributionOutput
  (Classical.decEq _)
  (fun _ : Unit => MechanicalReadoutSources.distributionReadout)
  (fun _ : Unit => MechanicalReadoutSources.distributionTarget)
def hitRealization := @homogeneousPointwiseEqRealization Unit HitOutput
  (Classical.decEq _)
  (fun _ : Unit => MechanicalReadoutSources.hitReadout)
  (fun _ : Unit => MechanicalReadoutSources.hitTarget)
def supportRealization := @homogeneousPointwiseEqRealization Unit SupportOutput
  (Classical.decEq _)
  (fun _ : Unit => MechanicalReadoutSources.supportReadout)
  (fun _ : Unit => MechanicalReadoutSources.supportTarget)

/-- The CUT output keeps the full readout as a function of ratio, slope, and phase. -/
abbrev JumpOutput := ℝ → ℝ → ℝ → ℝ

local instance : DecidableEq JumpOutput := Classical.decEq _

def jumpReadout (r alpha x : ℝ) : ℝ :=
  MechanicalReadoutSources.jumpReadout r alpha x

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
  (Classical.decEq _) (fun _ : Unit => MechanicalReadoutSources.jumpReadout)

end D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration
