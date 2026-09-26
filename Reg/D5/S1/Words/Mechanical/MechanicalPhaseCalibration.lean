import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.phaseArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law,
      statementIdentity := "sha256:46ab84fc00f32e087739c4648260bfde5b9e5b16a6b25ed0fa6ee6b92f10a371",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration.phaseArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law,
      statementIdentity := "sha256:46ab84fc00f32e087739c4648260bfde5b9e5b16a6b25ed0fa6ee6b92f10a371",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration

open Set MeasureTheory
open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical
open _root_.D5.S1.Words.Mechanical.MechanicalPhaseCalibration
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalSlopeCalibrationRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

local instance : DecidableEq PhaseOutput := Classical.decEq _

def phaseClaim : Prop :=
  ∀ (alpha delta g : ℝ) (n : ℕ), 0 < n →
    0 ≤ alpha → alpha < 1 → 0 ≤ alpha + delta → alpha + delta < 1 →
    0 < g →
    (∀ k : Fin n,
      g ≤ 1 - Int.fract (((k.val + 1 : ℕ) : ℝ) * alpha) ∧
      g ≤ Int.fract (((k.val + 1 : ℕ) : ℝ) * alpha)) →
    (∀ i j : Fin n, i ≠ j →
      g ≤ |Int.fract (((i.val + 1 : ℕ) : ℝ) * alpha) -
        Int.fract (((j.val + 1 : ℕ) : ℝ) * alpha)|) →
    (∀ u : ℝ, (∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) →
      volume (jointMismatchSet alpha delta n u) =
        ENNReal.ofReal (∑ k : Fin (n + 1), |u + (k.val : ℝ) * delta|)) ∧
    ((n : ℝ) * |delta| ≤ g / 4 →
      (∀ k : Fin (n + 1),
        |-(n : ℝ) * delta / 2 + (k.val : ℝ) * delta| ≤ g / 4) ∧
      volume (jointMismatchSet alpha delta n (-(n : ℝ) * delta / 2)) =
        ENNReal.ofReal (|delta| * (((n + 1)^2 / 4 : ℕ) : ℝ)) ∧
      ∀ u : ℝ, (∀ k : Fin (n + 1), |u + (k.val : ℝ) * delta| ≤ g / 4) →
        volume (jointMismatchSet alpha delta n (-(n : ℝ) * delta / 2)) ≤
          volume (jointMismatchSet alpha delta n u))

theorem phaseBridge : LegacyPrimitiveRealization phaseArena.toPrimitiveLawArena
    phaseClaim phaseRealization := by
  constructor
  exact Iff.rfl

def phaseBad : PrimitiveRealization phaseArena.signature :=
  @mechanicalReadoutRealization PhaseOutput (Classical.decEq _)
    (fun _ : Unit => fun _ _ _ _ => (1 : ENNReal))

private theorem phaseBad_not_law : ¬ phaseArena.Law phaseBad := by
  intro h
  have hfract : Int.fract (1 / 2 : ℝ) = 1 / 2 :=
    Int.fract_eq_self.mpr ⟨by norm_num, by norm_num⟩
  have hcuts : ∀ k : Fin 1,
      (1 / 2 : ℝ) ≤ 1 - Int.fract (((k.val + 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) ∧
      (1 / 2 : ℝ) ≤ Int.fract (((k.val + 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) := by
    intro k
    have hk : k.val = 0 := by omega
    norm_num [hk, hfract]
  have hgaps : ∀ i j : Fin 1, i ≠ j →
      (1 / 2 : ℝ) ≤
        |Int.fract (((i.val + 1 : ℕ) : ℝ) * (1 / 2 : ℝ)) -
          Int.fract (((j.val + 1 : ℕ) : ℝ) * (1 / 2 : ℝ))| := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hmove : ∀ k : Fin (1 + 1),
      |(0 : ℝ) + (k.val : ℝ) * 0| ≤ (1 / 2 : ℝ) / 4 := by
    intro k
    norm_num
  have heq := (h (1 / 2) 0 (1 / 2) 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hcuts hgaps).1 0 hmove
  simp [phaseBad, mechanicalReadoutRealization] at heq

theorem phaseVariation : phaseArena.Law phaseRealization ∧
    ¬ phaseArena.Law phaseBad := by
  exact ⟨phaseBridge.equivalence.mp
    (fun alpha delta g n hn ha0 ha1 hb0 hb1 hg hcuts hgaps =>
      joint_phase_calibration_law alpha delta g n hn ha0 ha1 hb0 hb1 hg hcuts hgaps),
    phaseBad_not_law⟩

theorem phaseSensitivity : FiniteSlotSensitivity phaseArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨phaseRealization, phaseBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => phaseBad_not_law, fun _ => phaseVariation.1⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law
  in phaseArena
  readout via (@mechanicalReadoutRealization PhaseOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.phaseReadout))
  primitives phaseRealization.toPrimitiveBundle
  realization phaseBridge
  variation phaseVariation sensitivity phaseSensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S1.Words.Mechanical.MechanicalPhaseCalibration.joint_phase_calibration_law
  unless row.any (fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false) do
    throwError "phase-calibration information registration is not declaredValidated"

end Reg.D5.S1.Words.Mechanical.MechanicalPhaseCalibration
