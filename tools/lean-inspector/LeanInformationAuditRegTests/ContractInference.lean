import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditRegTests.ContractAssertions
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import Reg.Support.LegacyRelations.Preemption
import Reg.D5.S0.Tower.GoldenGapZeckendorf
import Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Reg.D5.S0.History.FinitePrefixAntichainBudget
import Reg.D5.S0.Automata.BoundedStateSampleCompactness
import Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification


namespace LeanInformationAuditRegTests.ContractInference
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape
noncomputable def explicit0 : Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0} (@_root_.D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add) (DependentFamily.Realization _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature) Unit Unit := {
  unitName := `ContractTests.source0.unit,
  realizationName := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩,
  objectArena := .source ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩,
  catalog := `Reg.D5.S0.Tower.GoldenGapZeckendorf.arena,
  localNames := false,
  realization := .source _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
    ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature
    _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration.actual.readout _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration.actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Tower.GoldenGapZeckendorf
    definition := none, coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

noncomputable def inferred0 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add) (DependentFamily.Realization _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature) Unit Unit := {
  unitName := `ContractTests.source0.unit,
  realizationName := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩,
  objectArena := .source ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩,
  catalog := `Reg.D5.S0.Tower.GoldenGapZeckendorf.arena,
  localNames := false,
  realization := .source _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
    ⟨_root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature
    _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration.actual.readout _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration.actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Tower.GoldenGapZeckendorf
    definition := none, coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

noncomputable def explicit1.{u_1} : Contract.Registration.{u_1+1,0,1,0,0,0,u_1+1,u_1,0,0,0,0} (@_root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality.{u_1}) (DependentFamily.Realization _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}.signature) Unit Unit := {
  unitName := `ContractTests.source1.unit,
  realizationName := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨_root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}⟩,
  objectArena := .source ⟨_root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}⟩,
  catalog := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena,
  localNames := false,
  realization := .source _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
    ⟨_root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}.signature
    _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}.actual.readout _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}.actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
    definition := none, coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

noncomputable def inferred1.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality.{u_1}) (DependentFamily.Realization _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}.signature) Unit Unit := {
  unitName := `ContractTests.source1.unit,
  realizationName := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨_root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}⟩,
  objectArena := .source ⟨_root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}⟩,
  catalog := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena,
  localNames := false,
  realization := .source _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
    ⟨_root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}.signature
    _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}.actual.readout _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}.actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
    definition := none, coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

open Lean Meta Elab Command
open LeanInformationAuditRegTests.ContractGuards
run_meta do
  let mut readings := #[]
  for index in [0, 1] do
    let scopeName := `LeanInformationAuditRegTests.ContractInference
    let explicit ← getConstInfo (scopeName.str s!"explicit{index}")
    let inferred ← getConstInfo (scopeName.str s!"inferred{index}")
    let args := explicit.type.getAppArgs
    let inferredArgs := inferred.type.getAppArgs
    let levels := explicit.type.getAppFn.constLevels!
    let inferredLevels := inferred.type.getAppFn.constLevels!
    assertTest s!"inference.application_dimensions.{index}"
      (args.size == 5 && inferredArgs.size == 5 &&
        levels.length == 12 && inferredLevels.length == 12)
    assertTest s!"inference.explicit_and_inferred_equal.{index}"
      (explicit.type == inferred.type && explicit.levelParams == inferred.levelParams)
    readings := readings.push (Json.mkObj [
      ("index", toJson index), ("type_equal", toJson (explicit.type == inferred.type)),
      ("argument_equal", toJson (args.zip inferredArgs |>.map fun (a, b) => a == b)),
      ("universe_equal", toJson (levels.zip inferredLevels |>.map fun (a, b) => a == b)),
      ("universes", toJson (levels.map toString)),
      ("inferred_universes", toJson (inferredLevels.map toString)),
      ("level_parameters", toJson (explicit.levelParams.map toString)),
      ("level_parameters_equal", toJson (explicit.levelParams == inferred.levelParams)),
      ("inferred_universe_positions", toJson ([0,1,2,3,4,5,6,7,8,9,10,11] : List Nat))])
  logInfo m!"CONTRACT_INFERENCE {(toJson readings).compress}"

end LeanInformationAuditRegTests.ContractInference
