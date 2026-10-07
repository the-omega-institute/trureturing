import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Catalog
import D5.S3.ConceptDynamics.InformationEscape.IffRegistrations
import Reg.Support.LegacyRelations.Preemption
import Reg.D5.S0.Tower.GoldenGapZeckendorf
import Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Reg.D5.S0.History.FinitePrefixAntichainBudget
import Reg.D5.S0.Automata.BoundedStateSampleCompactness
import Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification

namespace LeanInformationAuditRegTests.ContractFixtures
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape

noncomputable def source0 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add) (DependentFamily.Realization _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature) Unit Unit := {
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
  options := #[{ name := `maxRecDepth, value := .nat 100000 }],
  coverage := { roots := [
    { owner := `D5.S0.Tower.GoldenGapZeckendorf, declaration := `D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source0, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source0, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source0, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source0, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

noncomputable def source1.{u_1} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality.{u_1}) (DependentFamily.Realization _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}.signature) Unit Unit := {
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
  options := #[{ name := `maxRecDepth, value := .nat 100000 }],
  coverage := { roots := [
    { owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality, declaration := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality, part := .type,
      path := [], levels := [.param `u_1] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source1, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source1, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source1, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source1, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

noncomputable def source2.{u_1, u_2} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.History.FinitePrefixAntichainBudget.result.{u_1, u_2}) (DependentFamily.Realization _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}.signature) Unit Unit := {
  unitName := `ContractTests.source2.unit,
  realizationName := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨_root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}⟩,
  objectArena := .source ⟨_root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}⟩,
  catalog := `Reg.D5.S0.History.FinitePrefixAntichainBudget.arena,
  localNames := false,
  realization := .source _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}
    ⟨_root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}.signature
    _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}.actual.readout _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}.actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.History.FinitePrefixAntichainBudget
    definition := none, coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `maxRecDepth, value := .nat 100000 }],
  coverage := { roots := [
    { owner := `D5.S0.History.FinitePrefixAntichainBudget, declaration := `D5.S0.History.FinitePrefixAntichainBudget.result, part := .type,
      path := [], levels := [.param `u_1, .param `u_2] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source2, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source2, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source2, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source2, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

noncomputable def source3.{u, v, w} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness.{u, v, w}) (DependentFamily.Realization _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}.signature) Unit Unit := {
  unitName := `ContractTests.source3.unit,
  realizationName := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨_root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}⟩,
  objectArena := .source ⟨_root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}⟩,
  catalog := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena,
  localNames := false,
  realization := .source _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}
    ⟨_root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}.signature
    _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}.actual.readout _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}.actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S0.Automata.BoundedStateSampleCompactness
    definition := none, coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `maxRecDepth, value := .nat 100000 }],
  coverage := { roots := [
    { owner := `D5.S0.Automata.BoundedStateSampleCompactness, declaration := `D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness, part := .type,
      path := [], levels := [.param `u, .param `v, .param `w] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source3, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `w] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source3, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `w] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source3, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u, .param `v, .param `w] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source3, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u, .param `v, .param `w] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

noncomputable def source4.{u_1, u_2, u_3, u_4} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification.{u_1, u_2, u_3, u_4}) (DependentFamily.Realization _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}.signature) Unit Unit := {
  unitName := `ContractTests.source4.unit,
  realizationName := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨_root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}⟩,
  objectArena := .source ⟨_root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}⟩,
  catalog := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena,
  localNames := false,
  realization := .source _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
    ⟨_root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (DependentFamily.realize _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}.signature
    _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}.actual.readout _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}.actual.anchor),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
    definition := none, coordinates := #[], readouts := #[] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `maxRecDepth, value := .nat 100000 }],
  coverage := { roots := [
    { owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification, declaration := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification, part := .type,
      path := [], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source4, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source4, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source4, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.source4, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [.param `u_1, .param `u_2, .param `u_3, .param `u_4] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def enrollment.{t, s, r, o, a} :
    Contract.TemplateEnrollment.{_, 0} (@DependentFamily.realize.{t, s, r, o, a}) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize
  version := 1
  constructors := #[]
  options := #[]
  bodyFact := `LeanInformationAuditRegTests.ContractFixtures.enrollmentBodyFact
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily,
      declaration := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize,
      part := .type, path := [], levels := [.param `t, .param `s, .param `r, .param `o, .param `a] },
    { owner := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily,
      declaration := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize,
      part := .value, path := [], levels := [.param `t, .param `s, .param `r, .param `o, .param `a] }], facts := [] } }

def enrollmentBodyFact.{t, s, r, o, a} : Contract.NodeFact :=
  .equal (@DependentFamily.realize.{t, s, r, o, a})
    (fun S readout anchor => ⟨readout, anchor⟩)
    { owner := `LeanInformationAuditRegTests.ContractFixtures,
      declaration := `LeanInformationAuditRegTests.ContractFixtures.enrollment,
      part := .type, path := [.argument], levels := [.param `t, .param `s, .param `r, .param `o, .param `a] }
    { owner := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily,
      declaration := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize,
      part := .value, path := [], levels := [.param `t, .param `s, .param `r, .param `o, .param `a] }
    rfl

open IffRegistrations IffRegistrationTemplates
local instance : DecidableEq openCodeArena.State := openCodeArena.stateDecidableEq

def localLegacy : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.localLegacy.unit,
  realizationName := `ContractTests.localLegacy.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := false,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := true,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .evidence ⟨open_lawSensitive⟩ (by first | exact open_lawSensitive | exact ⟨_, _, open_lawSensitive⟩),
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.localLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.localLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.localLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.localLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def generatedLegacy : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.generatedLegacy.unit,
  realizationName := `ContractTests.generatedLegacy.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := true,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := false,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .evidence ⟨open_lawSensitive⟩ (by first | exact open_lawSensitive | exact ⟨_, _, open_lawSensitive⟩),
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def generatedContinuing : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.generatedContinuing.unit,
  realizationName := `ContractTests.generatedContinuing.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := true,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := false,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .evidence ⟨open_lawSensitive⟩ (by first | exact open_lawSensitive | exact ⟨_, _, open_lawSensitive⟩),
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .evidence ⟨True.intro⟩,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedContinuing, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedContinuing, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedContinuing, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedContinuing, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def localFromObject : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.localFromObject.unit,
  realizationName := `ContractTests.localFromObject.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := false,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := true,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .evidence ⟨open_lawSensitive⟩ (by first | exact open_lawSensitive | exact ⟨_, _, open_lawSensitive⟩),
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.localFromObject, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.localFromObject, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.localFromObject, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.localFromObject, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def generatedLocal : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.generatedLocal.unit,
  realizationName := `ContractTests.generatedLocal.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := true,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := true,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .evidence ⟨open_lawSensitive⟩ (by first | exact open_lawSensitive | exact ⟨_, _, open_lawSensitive⟩),
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedLocal, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedLocal, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedLocal, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.generatedLocal, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def continuingLegacy : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.continuingLegacy.unit,
  realizationName := `ContractTests.continuingLegacy.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := false,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := true,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .evidence ⟨open_lawSensitive⟩ (by first | exact open_lawSensitive | exact ⟨_, _, open_lawSensitive⟩),
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := some Nat,
  sourceSelection := none,
  continuation := .evidence ⟨True.intro⟩,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.continuingLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.continuingLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.continuingLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.continuingLegacy, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
local instance : DecidableEq endStateOmitsPreemptingCauseArena.State :=
  endStateOmitsPreemptingCauseArena.stateDecidableEq

def finiteSource : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} end_state_omits_preempting_cause (DependentFamily.Realization _root_.Reg.Support.LegacyRelations.Preemption.signature) Unit Unit := {
  unitName := `ContractTests.finite.unit,
  realizationName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization,
  realizationSource := none,
  generated := false,
  arena := .law ⟨endStateOmitsPreemptingCauseArena⟩,
  objectArena := .law ⟨endStateOmitsPreemptingCauseArena⟩,
  catalog := `ContractTests.finite,
  localNames := true,
  realization := .legacy endStateOmitsPreemptingCauseArena endStateOmitsPreemptingCauseRealization
    endStateOmitsPreemptingCauseRealization.toPrimitiveBundle
    ⟨end_state_omits_preempting_cause_realization⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit end_state_omits_preempting_cause_realization end_state_omits_preempting_cause)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (DependentFamily.realize _root_.Reg.Support.LegacyRelations.Preemption.signature
    _root_.Reg.Support.LegacyRelations.Preemption.actual.readout
    _root_.Reg.Support.LegacyRelations.Preemption.actual.anchor),
  variation := .evidence ⟨_root_.Reg.Support.LegacyRelations.Preemption.finite_variation⟩ (by first | exact _root_.Reg.Support.LegacyRelations.Preemption.finite_variation | exact ⟨_, _, _root_.Reg.Support.LegacyRelations.Preemption.finite_variation⟩),
  sensitivity := .evidence ⟨_root_.Reg.Support.LegacyRelations.Preemption.finite_sensitivity⟩ (by exact _root_.Reg.Support.LegacyRelations.Preemption.finite_sensitivity),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
    definition := none, coordinates := #[], readouts := #[{
      path := #["fn", "arg"], stateBinder := 0, functionOperand := false
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true }] },
  continuation := .unknown,
  familyRecord := some ⟨_, ⟨_root_.Reg.Support.LegacyRelations.Preemption.registration⟩⟩,
  options := #[],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause, declaration := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.finiteSource, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.finiteSource, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.finiteSource, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.finiteSource, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def root : Contract.RootCatalog := {
  data := {
    rootId := `ContractTests.root
    expected := #[{
      statement := _
      proof := D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
      theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
      objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
      statementIdentity := some "sha256:fixture"
      registrationModuleName := `LeanInformationAuditRegTests.ContractFixtures }]
    source := #[{
      statement := _
      proof := D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
      theoremName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
      objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena
      statementIdentity := none
      registrationModuleName := `LeanInformationAuditRegTests.ContractFixtures }]
    baseline := #[], companionPrefix := some `ContractTests } }

private noncomputable def privateSeal : Contract.Seal.{0,0} := {
  rootId := `ContractTests.root
  catalogs := #[]
  options := #[] }

def missingVariation : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.missingVariation.unit,
  realizationName := `ContractTests.missingVariation.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := false,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := true,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .absent,
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.missingVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.missingVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.missingVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.missingVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def unknownVariation : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.unknownVariation.unit,
  realizationName := `ContractTests.unknownVariation.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := false,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := true,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .unknown,
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.unknownVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.unknownVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.unknownVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.unknownVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def unsupportedVariation : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.unsupportedVariation.unit,
  realizationName := `ContractTests.unsupportedVariation.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := false,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := true,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .unsupported `Nat.zero,
  sensitivity := .evidence ⟨open_slotSensitive⟩ (by exact open_slotSensitive),
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.unsupportedVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.unsupportedVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.unsupportedVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.unsupportedVariation, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

def partialSensitivity : Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled (PrimitiveRealization openCodeArena.signature) (Type) True := {
  unitName := `ContractTests.partialSensitivity.unit,
  realizationName := `ContractTests.partialSensitivity.bridge,
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge,
  generated := false,
  arena := .law ⟨openCodeArena⟩,
  objectArena := .law ⟨openCodeArena⟩,
  catalog := `ContractTests.catalog,
  localNames := true,
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨open_bridge⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit open_bridge D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled)⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i)),
  variation := .evidence ⟨open_lawSensitive⟩ (by first | exact open_lawSensitive | exact ⟨_, _, open_lawSensitive⟩),
  sensitivity := .unsupported `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_lawSensitive,
  partialSensitivity := some {
    readouts := [
      ⟨⟨true⟩, .evidence ⟨open_slotSensitive⟩ (open_slotSensitive.1 true)⟩,
      ⟨⟨false⟩, .absent⟩],
    readoutsNodup := by simp,
    readoutsComplete := by
      intro i
      rcases i with ⟨i⟩
      cases i <;> simp,
    anchors := [],
    anchorsNodup := by simp,
    anchorsComplete := by intro i; exact Fin.elim0 i.down },
  escapeFrom := none,
  sourceSelection := none,
  continuation := .absent,
  familyRecord := none,
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }],
  coverage := { roots := [
    { owner := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling, declaration := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled, part := .type,
      path := [], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.partialSensitivity, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.partialSensitivity, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.partialSensitivity, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `LeanInformationAuditRegTests.ContractFixtures, declaration := `LeanInformationAuditRegTests.ContractFixtures.partialSensitivity, part := .value,
      path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [] },
  exclusion := none, finiteLift := none, roleEnumeration := none, anchorEnumeration := none }

end LeanInformationAuditRegTests.ContractFixtures
