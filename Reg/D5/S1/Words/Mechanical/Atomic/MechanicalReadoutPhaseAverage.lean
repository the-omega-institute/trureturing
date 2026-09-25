import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration
import Reg.Support.MechanicalPhaseAverageRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration.phaseAverageArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average,
      statementIdentity := "sha256:c5da0649ff1675503963a41a48ceac32ae9c8be19ab3a7d9baf2a52cbbafecea",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration.phaseAverageArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average,
      statementIdentity := "sha256:c5da0649ff1675503963a41a48ceac32ae9c8be19ab3a7d9baf2a52cbbafecea",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage

open Set MeasureTheory
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalPhaseAverageRegistration
open D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
open D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

local instance : DecidableEq PhaseAverageOutput := Classical.decEq _
local instance : DecidableEq phaseAverageArena.State := phaseAverageArena.toArena.stateDecidableEq

def phaseAverageClaim : Prop :=
  ∀ (r : ℝ), 0 < r → r < 1 → ∀ (A : Set ℝ), MeasurableSet A →
    A ⊆ Set.Icc (0 : ℝ) 1 →
      ∫⁻ x in Set.Ico (0 : ℝ) 1, geometricAtomicMeasure r x A ∂volume = volume A

theorem phaseAverageBridge : LegacyPrimitiveRealization phaseAverageArena.toPrimitiveLawArena
    phaseAverageClaim phaseAverageRealization := by
  constructor
  constructor
  · intro h
    change ∀ _ : Unit, (some phaseAverageIntegral : PhaseAverageOutput) =
      some phaseAverageVolume
    intro _
    congr 1
    funext input
    exact h input.ratio input.ratioPositive input.ratioBelowOne input.target
      input.targetMeasurable input.targetInUnit
  · intro h r hr0 hr1 A hA hAunit
    have hFunctions : phaseAverageIntegral = phaseAverageVolume := by
      exact Option.some.inj (h ())
    exact congrFun hFunctions ⟨r, hr0, hr1, A, hA, hAunit⟩

def phaseAverageBad : PrimitiveRealization phaseAverageArena.signature :=
  homogeneousPointwiseEqRealization
    (fun _ : Unit => (none : PhaseAverageOutput))
    (fun _ : Unit => some phaseAverageVolume)

theorem phaseAverageVariation : phaseAverageArena.Law phaseAverageRealization ∧
    ¬ phaseAverageArena.Law phaseAverageBad := by
  constructor
  · exact phaseAverageBridge.equivalence.mp geometric_atomic_phase_average
  · intro h
    have hh := h ()
    exact Option.noConfusion hh

theorem phaseAverageSensitivity : FiniteSlotSensitivity phaseAverageArena.toPrimitiveLawArena := by
  change FiniteSlotSensitivity
    (homogeneousPointwiseEqArena (Arena.ofFintype Unit) PhaseAverageOutput)
  exact homogeneousPointwiseEq_sensitivity (Arena.ofFintype Unit)
    (x := ()) (a := (none : PhaseAverageOutput))
    (b := some phaseAverageVolume) (by simp)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average
  in phaseAverageArena
  readout via (@homogeneousPointwiseEqRealization Unit PhaseAverageOutput
    (Classical.decEq _)
    (fun _ : Unit => some phaseAverageIntegral)
    (fun _ : Unit => some phaseAverageVolume))
  primitives phaseAverageRealization.toPrimitiveBundle
  realization phaseAverageBridge
  variation phaseAverageVariation sensitivity phaseAverageSensitivity
  escape from (Set ℝ) escape continues (open)

end Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
