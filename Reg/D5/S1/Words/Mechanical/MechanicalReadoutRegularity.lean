import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.regularityArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump,
      statementIdentity := "sha256:ec5cadfc13b74c2674cf501896fe5df3e646220f47ea03bd784cca87bf988f3e",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.regularityArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump,
      statementIdentity := "sha256:ec5cadfc13b74c2674cf501896fe5df3e646220f47ea03bd784cca87bf988f3e",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity

open Set
open LeanInformationAudit
open D5.S1.Words.Mechanical.MechanicalReadoutRegularity
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : DecidableEq CompletionOutput := Classical.decEq _

theorem regularityBridge : LegacyPrimitiveRealization regularityArena.toPrimitiveLawArena
    (regularityClaim actualCompletion) completionRealization := ⟨Iff.rfl⟩

def badCompletion : PrimitiveRealization regularityArena.signature :=
  @mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => ((fun _ _ _ => (0 : ℝ)), (fun _ _ _ _ => (0 : ℝ))))

theorem regularityVariation : regularityArena.Law completionRealization ∧
    ¬ regularityArena.Law badCompletion := by
  constructor
  · apply regularityBridge.equivalence.mp
    intro r alpha x hr0 hr1 ha
    exact geometric_readout_continuity_and_jump r alpha x hr0 hr1 ha
  · intro h
    have hiff := (h (1 / 2) (1 / 2) (1 / 2)
      (by norm_num) (by norm_num) (by norm_num [Set.mem_Ioo])).1
    have hcontinuous :
        ∀ eps : ℝ, 0 < eps → ∃ radius : ℝ, 0 < radius ∧
          ∀ beta : ℝ, |beta - (1 / 2 : ℝ)| < radius →
            |(badCompletion.readout () ()).1 (1 / 2) beta (1 / 2) -
              (badCompletion.readout () ()).1 (1 / 2) (1 / 2) (1 / 2)| < eps := by
      intro eps heps
      refine ⟨1, by norm_num, ?_⟩
      intro beta _
      simpa [badCompletion, mechanicalReadoutRealization] using heps
    have hno := hiff.mp hcontinuous
    have hneq := hno 1 (by norm_num) 1
    apply hneq
    norm_num

theorem regularitySensitivity : FiniteSlotSensitivity regularityArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨completionRealization, badCompletion, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => regularityVariation.2, fun _ => regularityVariation.1⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump
  in regularityArena
  readout via (@mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => actualCompletion))
  primitives completionRealization.toPrimitiveBundle
  realization regularityBridge
  variation regularityVariation sensitivity regularitySensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  let row := (TemplateBinding.records (← getEnv)).find? fun record =>
    record.occurrence.key.theoremName ==
      `D5.S1.Words.Mechanical.MechanicalReadoutRegularity.geometric_readout_continuity_and_jump
  let valid := row.any fun record => match record.result with
    | .declaredValidated _ => true
    | _ => false
  unless valid do throwError "mechanical regularity registration is not declaredValidated"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutRegularity
