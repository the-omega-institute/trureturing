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

noncomputable def source0 : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add) DependentFamily.Arena DependentFamily.Arena
    (DependentFamily.Realization _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature) Unit Unit Unit Unit Unit := {
  targetName := `D5.S0.Tower.GoldenGapZeckendorf.wdigits_fib_add
  unitName := `ContractTests.source0.unit
  realizationName := `Reg.D5.S0.Tower.GoldenGapZeckendorf.registration
  realizationSource := none
  generated := false
  arena := ⟨`Reg.D5.S0.Tower.GoldenGapZeckendorf.arena, _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩
  objectArena := ⟨`Reg.D5.S0.Tower.GoldenGapZeckendorf.arena, _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena⟩
  catalog := `Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
  localNames := false
  realization := .source _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena
    ⟨`Reg.D5.S0.Tower.GoldenGapZeckendorf.registration, _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration⟩
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.arena.signature
    _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration.actual.readout _root_.Reg.D5.S0.Tower.GoldenGapZeckendorf.registration.actual.anchor)
  variation := none
  sensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Tower.GoldenGapZeckendorf
    definition := none, coordinates := #[], readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

noncomputable def source1.{u_1} : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality.{u_1}) DependentFamily.Arena DependentFamily.Arena
    (DependentFamily.Realization _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}.signature) Unit Unit Unit Unit Unit := {
  targetName := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.depth_budget_iid_greedy_optimality
  unitName := `ContractTests.source1.unit
  realizationName := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration
  realizationSource := none
  generated := false
  arena := ⟨`Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena, _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}⟩
  objectArena := ⟨`Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena, _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}⟩
  catalog := `Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena
  localNames := false
  realization := .source _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}
    ⟨`Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration, _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}⟩
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.arena.{u_1}.signature
    _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}.actual.readout _root_.Reg.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.registration.{u_1}.actual.anchor)
  variation := none
  sensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
    definition := none, coordinates := #[], readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

noncomputable def source2.{u_1, u_2} : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S0.History.FinitePrefixAntichainBudget.result.{u_1, u_2}) DependentFamily.Arena DependentFamily.Arena
    (DependentFamily.Realization _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}.signature) Unit Unit Unit Unit Unit := {
  targetName := `D5.S0.History.FinitePrefixAntichainBudget.result
  unitName := `ContractTests.source2.unit
  realizationName := `Reg.D5.S0.History.FinitePrefixAntichainBudget.registration
  realizationSource := none
  generated := false
  arena := ⟨`Reg.D5.S0.History.FinitePrefixAntichainBudget.arena, _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}⟩
  objectArena := ⟨`Reg.D5.S0.History.FinitePrefixAntichainBudget.arena, _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}⟩
  catalog := `Reg.D5.S0.History.FinitePrefixAntichainBudget.arena
  localNames := false
  realization := .source _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}
    ⟨`Reg.D5.S0.History.FinitePrefixAntichainBudget.registration, _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}⟩
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.arena.{u_1, u_2}.signature
    _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}.actual.readout _root_.Reg.D5.S0.History.FinitePrefixAntichainBudget.registration.{u_1, u_2}.actual.anchor)
  variation := none
  sensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.History.FinitePrefixAntichainBudget
    definition := none, coordinates := #[], readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

noncomputable def source3.{u, v, w} : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness.{u, v, w}) DependentFamily.Arena DependentFamily.Arena
    (DependentFamily.Realization _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}.signature) Unit Unit Unit Unit Unit := {
  targetName := `D5.S0.Automata.BoundedStateSampleCompactness.bounded_state_sample_compactness
  unitName := `ContractTests.source3.unit
  realizationName := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration
  realizationSource := none
  generated := false
  arena := ⟨`Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena, _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}⟩
  objectArena := ⟨`Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena, _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}⟩
  catalog := `Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena
  localNames := false
  realization := .source _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}
    ⟨`Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration, _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}⟩
  readout := some (DependentFamily.realize _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.arena.{u, v, w}.signature
    _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}.actual.readout _root_.Reg.D5.S0.Automata.BoundedStateSampleCompactness.registration.{u, v, w}.actual.anchor)
  variation := none
  sensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Automata.BoundedStateSampleCompactness
    definition := none, coordinates := #[], readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

noncomputable def source4.{u_1, u_2, u_3, u_4} : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification.{u_1, u_2, u_3, u_4}) DependentFamily.Arena DependentFamily.Arena
    (DependentFamily.Realization _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}.signature) Unit Unit Unit Unit Unit := {
  targetName := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.period_classification
  unitName := `ContractTests.source4.unit
  realizationName := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration
  realizationSource := none
  generated := false
  arena := ⟨`Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena, _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}⟩
  objectArena := ⟨`Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena, _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}⟩
  catalog := `Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena
  localNames := false
  realization := .source _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}
    ⟨`Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration, _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}⟩
  readout := some (DependentFamily.realize _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.arena.{u_1, u_2, u_3, u_4}.signature
    _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}.actual.readout _root_.Reg.D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification.registration.{u_1, u_2, u_3, u_4}.actual.anchor)
  variation := none
  sensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.ContextUpdates.ExactSnapshotPeriodClassification
    definition := none, coordinates := #[], readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `maxRecDepth, value := .nat 100000 }] }

def enrollment.{t, s, r, o, a} :
    Contract.TemplateEnrollment.{_, 0} (@DependentFamily.realize.{t, s, r, o, a}) := {
  name := `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.realize
  version := 1
  constructors := #[]
  options := #[] }

open IffRegistrations IffRegistrationTemplates
local instance : DecidableEq openCodeArena.State := openCodeArena.stateDecidableEq

def localLegacy : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
    PrimitiveLawArena PrimitiveLawArena (PrimitiveRealization openCodeArena.signature)
    (openCodeArena.Law openRealization ∧ ¬ openCodeArena.Law
      (iffRealization (fun _ : Fin 5 => true) (fun _ => false)))
    (LeanInformationAudit.FiniteSlotSensitivity openCodeArena) (Type) True Unit := {
  targetName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  unitName := `ContractTests.localLegacy.unit
  realizationName := `ContractTests.localLegacy.bridge
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge
  generated := false
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  catalog := `ContractTests.catalog
  localNames := true
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge, open_bridge⟩
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_lawSensitive,
    open_lawSensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_slotSensitive,
    open_slotSensitive⟩
  escapeFrom := none
  sourceSelection := none
  continuation := .absent
  familyRecord := none
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }] }

def generatedLegacy : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
    PrimitiveLawArena PrimitiveLawArena (PrimitiveRealization openCodeArena.signature)
    (openCodeArena.Law openRealization ∧ ¬ openCodeArena.Law
      (iffRealization (fun _ : Fin 5 => true) (fun _ => false)))
    (LeanInformationAudit.FiniteSlotSensitivity openCodeArena) (Type) True Unit := {
  targetName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  unitName := `ContractTests.generatedLegacy.unit
  realizationName := `ContractTests.generatedLegacy.bridge
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge
  generated := true
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  catalog := `ContractTests.catalog
  localNames := false
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge, open_bridge⟩
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_lawSensitive,
    open_lawSensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_slotSensitive,
    open_slotSensitive⟩
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }] }

def generatedContinuing : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
    PrimitiveLawArena PrimitiveLawArena (PrimitiveRealization openCodeArena.signature)
    (openCodeArena.Law openRealization ∧ ¬ openCodeArena.Law
      (iffRealization (fun _ : Fin 5 => true) (fun _ => false)))
    (LeanInformationAudit.FiniteSlotSensitivity openCodeArena) (Type) True Unit := {
  targetName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  unitName := `ContractTests.generatedContinuing.unit
  realizationName := `ContractTests.generatedContinuing.bridge
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge
  generated := true
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  catalog := `ContractTests.catalog
  localNames := false
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge, open_bridge⟩
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_lawSensitive,
    open_lawSensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_slotSensitive,
    open_slotSensitive⟩
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .evidence ⟨`True.intro, True.intro⟩
  familyRecord := none
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }] }

def localFromObject : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
    PrimitiveLawArena PrimitiveLawArena (PrimitiveRealization openCodeArena.signature)
    (openCodeArena.Law openRealization ∧ ¬ openCodeArena.Law
      (iffRealization (fun _ : Fin 5 => true) (fun _ => false)))
    (LeanInformationAudit.FiniteSlotSensitivity openCodeArena) (Type) True Unit := {
  targetName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  unitName := `ContractTests.localFromObject.unit
  realizationName := `ContractTests.localFromObject.bridge
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge
  generated := false
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  catalog := `ContractTests.catalog
  localNames := true
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge, open_bridge⟩
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_lawSensitive,
    open_lawSensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_slotSensitive,
    open_slotSensitive⟩
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .absent
  familyRecord := none
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }] }

def generatedLocal : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
    PrimitiveLawArena PrimitiveLawArena (PrimitiveRealization openCodeArena.signature)
    (openCodeArena.Law openRealization ∧ ¬ openCodeArena.Law
      (iffRealization (fun _ : Fin 5 => true) (fun _ => false)))
    (LeanInformationAudit.FiniteSlotSensitivity openCodeArena) (Type) True Unit := {
  targetName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  unitName := `ContractTests.generatedLocal.unit
  realizationName := `ContractTests.generatedLocal.bridge
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge
  generated := true
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  catalog := `ContractTests.catalog
  localNames := true
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge, open_bridge⟩
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_lawSensitive,
    open_lawSensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_slotSensitive,
    open_slotSensitive⟩
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .absent
  familyRecord := none
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }] }

def continuingLegacy : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
    PrimitiveLawArena PrimitiveLawArena (PrimitiveRealization openCodeArena.signature)
    (openCodeArena.Law openRealization ∧ ¬ openCodeArena.Law
      (iffRealization (fun _ : Fin 5 => true) (fun _ => false)))
    (LeanInformationAudit.FiniteSlotSensitivity openCodeArena) (Type) True Unit := {
  targetName := `D5.S3.ConceptDynamics.Answering.AssertionSettlementCeiling.open_permits_only_unsettled
  unitName := `ContractTests.continuingLegacy.unit
  realizationName := `ContractTests.continuingLegacy.bridge
  realizationSource := some `D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge
  generated := false
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.openCodeArena, openCodeArena⟩
  catalog := `ContractTests.catalog
  localNames := true
  realization := .legacy openCodeArena openRealization openRealization.toPrimitiveBundle
    ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_bridge, open_bridge⟩
  readout := some (@iffRealization (Fin 5)
    (fun i => openPermissionReadout i) (fun i => openUnsettledReadout i))
  variation := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_lawSensitive,
    open_lawSensitive⟩
  sensitivity := some ⟨`D5.S3.ConceptDynamics.InformationEscape.IffRegistrations.open_slotSensitive,
    open_slotSensitive⟩
  escapeFrom := some Nat
  sourceSelection := none
  continuation := .evidence ⟨`True.intro, True.intro⟩
  familyRecord := none
  options := #[{ name := `maxHeartbeats, value := .nat 2000000 },
    { name := `pp.unicode.fun, value := .bool true }] }

open D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause
open D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause
local instance : DecidableEq endStateOmitsPreemptingCauseArena.State :=
  endStateOmitsPreemptingCauseArena.stateDecidableEq

def finiteSource : Contract.Registration.{_, _, _, _, _, _, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    end_state_omits_preempting_cause
    PrimitiveLawArena PrimitiveLawArena
    (DependentFamily.Realization _root_.Reg.Support.LegacyRelations.Preemption.signature)
    (FiniteLawVariation endStateOmitsPreemptingCauseArena)
    (FiniteSlotSensitivity endStateOmitsPreemptingCauseArena) Unit Unit
    (DependentFamily.Registration _root_.Reg.Support.LegacyRelations.Preemption.arena
      EndStateOmitsPreemptingCauseStatement) := {
  targetName := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause
  unitName := `ContractTests.finite.unit
  realizationName := `D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization
  realizationSource := none
  generated := false
  arena := ⟨`D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena,
    endStateOmitsPreemptingCauseArena⟩
  objectArena := ⟨`D5.S3.ConceptDynamics.InformationEscapeArenas.EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena,
    endStateOmitsPreemptingCauseArena⟩
  catalog := `ContractTests.finite
  localNames := true
  realization := .legacy endStateOmitsPreemptingCauseArena endStateOmitsPreemptingCauseRealization
    endStateOmitsPreemptingCauseRealization.toPrimitiveBundle
    ⟨`D5.S3.ConceptDynamics.InformationEscapeRealizations.EndStateOmitsPreemptingCause.end_state_omits_preempting_cause_realization,
      end_state_omits_preempting_cause_realization⟩
  readout := some (DependentFamily.realize _root_.Reg.Support.LegacyRelations.Preemption.signature
    _root_.Reg.Support.LegacyRelations.Preemption.actual.readout
    _root_.Reg.Support.LegacyRelations.Preemption.actual.anchor)
  variation := some ⟨`Reg.Support.LegacyRelations.Preemption.finite_variation,
    _root_.Reg.Support.LegacyRelations.Preemption.finite_variation⟩
  sensitivity := some ⟨`Reg.Support.LegacyRelations.Preemption.finite_sensitivity,
    _root_.Reg.Support.LegacyRelations.Preemption.finite_sensitivity⟩
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Attribution.EndStateOmitsPreemptingCause
    definition := none, coordinates := #[], readouts := #[{
      path := #["fn", "arg"], stateBinder := 0, functionOperand := false
      stateOperand := some #["fn", "fn", "arg"], booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := some ⟨`Reg.Support.LegacyRelations.Preemption.registration,
    _root_.Reg.Support.LegacyRelations.Preemption.registration⟩
  options := #[] }

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

private noncomputable def privateSeal : Contract.Seal := { rootId := `ContractTests.root, options := #[] }

end LeanInformationAuditRegTests.ContractFixtures
