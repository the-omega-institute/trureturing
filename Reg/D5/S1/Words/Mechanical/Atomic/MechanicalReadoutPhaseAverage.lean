import LeanInformationAudit.Syntax
import D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
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
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure

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
    change ∀ _ : Unit, phaseAverageIntegral = phaseAverageVolume
    intro _
    funext input
    exact h input.ratio input.ratioPositive input.ratioBelowOne input.target
      input.targetMeasurable input.targetInUnit
  · intro h r hr0 hr1 A hA hAunit
    have hFunctions : phaseAverageIntegral = phaseAverageVolume := by
      exact h ()
    exact congrFun hFunctions ⟨r, hr0, hr1, A, hA, hAunit⟩

def phaseAverageBad :
    PrimitiveRealization (homogeneousPointwiseEqSignature Unit PhaseAverageOutput) :=
  homogeneousPointwiseEqRealization
    (fun _ : Unit => (fun _ : PhaseAverageInput => (0 : ENNReal)))
    (fun _ : Unit => (fun _ : PhaseAverageInput => (1 : ENNReal)))

private def emptyInput : PhaseAverageInput where
  ratio := 1 / 2
  ratioPositive := by norm_num
  ratioBelowOne := by norm_num
  target := ∅
  targetMeasurable := MeasurableSet.empty
  targetInUnit := Set.empty_subset _

theorem phaseAverageVariation : phaseAverageArena.Law phaseAverageRealization ∧
    ¬ phaseAverageArena.Law phaseAverageBad := by
  constructor
  · exact phaseAverageBridge.equivalence.mp geometric_atomic_phase_average
  · intro h
    have hh := congrFun (h ()) emptyInput
    exact zero_ne_one hh

theorem phaseAverageSensitivity : FiniteSlotSensitivity phaseAverageArena.toPrimitiveLawArena := by
  change FiniteSlotSensitivity
    (homogeneousPointwiseEqArena (Arena.ofFintype Unit) PhaseAverageOutput)
  have hne : (fun _ : PhaseAverageInput => (0 : ENNReal)) ≠
      (fun _ : PhaseAverageInput => (1 : ENNReal)) := by
    intro h
    exact zero_ne_one (congrFun h emptyInput)
  exact homogeneousPointwiseEq_sensitivity (Arena.ofFintype Unit)
    (x := ()) (a := fun _ : PhaseAverageInput => (0 : ENNReal))
    (b := fun _ : PhaseAverageInput => (1 : ENNReal)) hne

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average
  in phaseAverageArena
  readout via (@homogeneousPointwiseEqRealization Unit PhaseAverageOutput
    (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.phaseAverageIntegral)
    (fun _ : Unit => MechanicalReadoutSources.phaseAverageVolume))
  primitives phaseAverageRealization.toPrimitiveBundle
  realization phaseAverageBridge
  variation phaseAverageVariation sensitivity phaseAverageSensitivity
  escape from (Set ℝ) escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_phase_average
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "phase-average information registration is not declaredValidated"

end Reg.D5.S1.Words.Mechanical.Atomic.MechanicalReadoutPhaseAverage
