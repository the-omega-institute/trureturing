import LeanInformationAudit.Syntax
import D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.uniformBoundArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound,
      statementIdentity := "sha256:ae5c03ecae8ce575308eb4072fd637ff78f2917f57de945667c4772a48a00d3d",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.iteratedLimitArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_iterated_limit_order,
      statementIdentity := "sha256:f28dc4d6814dcddf3f90d5d2918297cc9dd56b6d3dac67367d483b2bd2377bfb",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.uniformBoundArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound,
      statementIdentity := "sha256:ae5c03ecae8ce575308eb4072fd637ff78f2917f57de945667c4772a48a00d3d",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration.iteratedLimitArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_iterated_limit_order,
      statementIdentity := "sha256:f28dc4d6814dcddf3f90d5d2918297cc9dd56b6d3dac67367d483b2bd2377bfb",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit

open Set Filter
open scoped Topology
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open D5.S3.ConceptDynamics.InformationEscape.MechanicalRealReadoutRegistration

set_option autoImplicit false
set_option relaxedAutoImplicit false

local instance : DecidableEq CompletionOutput := Classical.decEq _

theorem uniformBridge : LegacyPrimitiveRealization uniformBoundArena.toPrimitiveLawArena
    (uniformBoundClaim actualCompletion) completionRealization := ⟨Iff.rfl⟩

theorem limitBridge : LegacyPrimitiveRealization iteratedLimitArena.toPrimitiveLawArena
    (iteratedLimitClaim actualCompletion) completionRealization := ⟨Iff.rfl⟩

def badCompletion : PrimitiveRealization uniformBoundArena.signature :=
  @mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => ((fun _ _ _ => (0 : ℝ)), (fun _ _ _ _ => (0 : ℝ))))

theorem uniformVariation : uniformBoundArena.Law completionRealization ∧
    ¬ uniformBoundArena.Law badCompletion := by
  constructor
  · apply uniformBridge.equivalence.mp
    intro r alpha x hr0 hr1 ha
    exact geometric_readout_uniform_slope_bound r alpha x hr0 hr1 ha
  · intro h
    have hbad := (h (1 / 2) (3 / 4) 0 (by norm_num) (by norm_num)
      (by norm_num [Set.mem_Ico])).1
    norm_num [badCompletion, mechanicalReadoutRealization] at hbad

theorem uniformSensitivity : FiniteSlotSensitivity uniformBoundArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨completionRealization, badCompletion, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => uniformVariation.2, fun _ => uniformVariation.1⟩
  · intro i
    exact Fin.elim0 i

theorem limitVariation : iteratedLimitArena.Law completionRealization ∧
    ¬ iteratedLimitArena.Law badCompletion := by
  constructor
  · apply limitBridge.equivalence.mp
    intro alpha x ha
    exact geometric_readout_iterated_limit_order alpha x ha
  · intro h
    have hlimit := (h (1 / 2) 0 (by norm_num [Set.mem_Ico])).2.1
    have hzero : Tendsto (fun _ : ℝ => (0 : ℝ))
        (𝓝[<] (1 : ℝ)) (𝓝 (0 : ℝ)) := tendsto_const_nhds
    have heq : (1 / 2 : ℝ) = 0 :=
      tendsto_nhds_unique (by simpa [badCompletion, mechanicalReadoutRealization]
        using hlimit) hzero
    norm_num at heq

theorem limitSensitivity : FiniteSlotSensitivity iteratedLimitArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨completionRealization, badCompletion, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => limitVariation.2, fun _ => limitVariation.1⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound
  in uniformBoundArena
  readout via (@mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => actualCompletion))
  primitives completionRealization.toPrimitiveBundle
  realization uniformBridge
  variation uniformVariation sensitivity uniformSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_iterated_limit_order
  in iteratedLimitArena
  readout via (@mechanicalReadoutRealization CompletionOutput (Classical.decEq _)
    (fun _ : Unit => actualCompletion))
  primitives completionRealization.toPrimitiveBundle
  realization limitBridge
  variation limitVariation sensitivity limitSensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_uniform_slope_bound,
      `D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit.geometric_readout_iterated_limit_order] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "mechanical limit registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutUniformLimit
