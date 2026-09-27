import LeanInformationAudit.Census.Query
import Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
import Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
import Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
import Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SharedArenaPeers
import Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers
import Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
import LeanInformationAudit.SealCommand

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.Catalogs.SharedArenaPeers
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SharedArenaPeers },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer,
      statementIdentity := "sha256:1a6132946d7a8891764ed2653324de2bf30ed7e60a456bc3718245df3f8e4916",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber,
      statementIdentity := "sha256:cb61e898923980980a8546c9854a68fceece05576107f21c3d55ce166b9297aa",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable,
      statementIdentity := "sha256:a8c89fcc1db5d6e828261153109783acdf6c889d18caab542dfa8b17800caf2c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not,
      statementIdentity := "sha256:8b649e1191e8e2c40391ae6cd263fafc09d16bf7c6c684f60f8ff7430cc97052",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, theoremName := `D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation,
      statementIdentity := "sha256:87ec84d0c4c656a0524de84c33660dda95d43fde6d2b8c2284d448a1efbb5391",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual,
      statementIdentity := "sha256:fd8c5bad3c9b38d167e59ff3889f6897c82fdd7070d8feaae13528062ac13140",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SharedArenaPeers },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer,
      statementIdentity := "sha256:1a6132946d7a8891764ed2653324de2bf30ed7e60a456bc3718245df3f8e4916",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber,
      statementIdentity := "sha256:cb61e898923980980a8546c9854a68fceece05576107f21c3d55ce166b9297aa",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable,
      statementIdentity := "sha256:a8c89fcc1db5d6e828261153109783acdf6c889d18caab542dfa8b17800caf2c",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena, theoremName := `D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not,
      statementIdentity := "sha256:8b649e1191e8e2c40391ae6cd263fafc09d16bf7c6c684f60f8ff7430cc97052",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, theoremName := `D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention,
      statementIdentity := "sha256:65c74f1a6b6342639e4c773a4de5bbcd925ebae300eebf640b0cab6f5e4b2984",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena, theoremName := `D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation,
      statementIdentity := "sha256:87ec84d0c4c656a0524de84c33660dda95d43fde6d2b8c2284d448a1efbb5391",
      registrationModuleName := `Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness }]
  companionPrefix := some `Reg.Catalogs.SharedArenaPeers }


namespace Reg.Catalogs.SharedArenaPeers

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
open _root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
open _root_.D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
open _root_.D5.S3.ConceptDynamics.ConceptJoinUniversal
open FourthFifthArenas
attribute [local instance] modelFintype modelDecidableEq

def interventionCatalog : Catalog finiteInterventionArena := Catalog.ofVector ![
  _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable.«Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit,
  _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber.«Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit,
  _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer.«Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit,
  _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual.«Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit,
  _root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not.«Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit]
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner
open _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion
open _root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative
open _root_.D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization
open _root_.D5.S3.ConceptDynamics.ConceptJoinUniversal
open FourthFifthArenas
attribute [local instance] modelFintype modelDecidableEq

theorem intervention_unique_zero (i : Fin 5) : interventionCatalog.uniqueCaptureCount i = 0 := by
  fin_cases i
  · exact (interventionCatalog.same_kernel_both_zero (0 : Fin 5) (1 : Fin 5) (by change (0 : Fin 5) ≠ 1; decide) (fun _ _ => Iff.rfl)).1
  · exact (interventionCatalog.same_kernel_both_zero (1 : Fin 5) (0 : Fin 5) (by change (1 : Fin 5) ≠ 0; decide) (fun _ _ => Iff.rfl)).1
  · exact (interventionCatalog.same_kernel_both_zero (2 : Fin 5) (0 : Fin 5) (by change (2 : Fin 5) ≠ 0; decide) (fun _ _ => Iff.rfl)).1
  · exact (interventionCatalog.same_kernel_both_zero (3 : Fin 5) (0 : Fin 5) (by change (3 : Fin 5) ≠ 0; decide) (fun _ _ => Iff.rfl)).1
  · exact (interventionCatalog.same_kernel_both_zero (4 : Fin 5) (0 : Fin 5) (by change (4 : Fin 5) ≠ 0; decide) (fun _ _ => Iff.rfl)).1
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
open InformationEscapeArenas.ObservationIntervention

def observationCatalog : Catalog finiteObservationInterventionArena := Catalog.ofVector ![
  _root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation.«Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__information_unit,
  _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.«Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__information_unit]
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT
open _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation
open _root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness
open InformationEscapeArenas.ObservationIntervention

theorem observation_unique_zero (i : Fin 2) : observationCatalog.uniqueCaptureCount i = 0 := by
  fin_cases i
  · exact (observationCatalog.same_kernel_both_zero (0 : Fin 2) (1 : Fin 2) (by change (0 : Fin 2) ≠ 1; decide) (fun _ _ => Iff.rfl)).1
  · exact (observationCatalog.same_kernel_both_zero (1 : Fin 2) (0 : Fin 2) (by change (1 : Fin 2) ≠ 0; decide) (fun _ _ => Iff.rfl)).1
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT

theorem all_peers_trivial :
    (∀ i, interventionCatalog.TrivialInCatalog i) ∧ (∀ i, observationCatalog.TrivialInCatalog i) := by
  constructor
  · intro i; exact Finset.card_eq_zero.mp (intervention_unique_zero i)
  · intro i; exact Finset.card_eq_zero.mp (observation_unique_zero i)
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT

theorem no_peer_lowers_escape :
    (∀ i, ¬ interventionCatalog.LowersEscape i) ∧
    (∀ i, ¬ observationCatalog.LowersEscape i) := by
  exact ⟨fun i => (Catalog.trivialInCatalog_iff_not_lowersEscape _ _ finiteIntervention_nondegenerate).mp
    (all_peers_trivial.1 i),
    fun i => (Catalog.trivialInCatalog_iff_not_lowersEscape _ _ finiteObservation_nondegenerate).mp
      (all_peers_trivial.2 i)⟩
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT

open Lean Meta LeanInformationAudit in
run_cmd do
  let catalogs ← prepareCatalogs
  unless catalogs.size == 2 do throwError "expected two maximal canonical catalogs"
  for (prepared, expected) in catalogs.zip #[``interventionCatalog, ``observationCatalog] do
    Lean.Elab.Command.liftTermElabM do
      unless ← isDefEq prepared.type (← inferType (mkConst expected)) do
        throwError "measured catalog uses a different canonical arena: {expected}"
      -- The engine's empty vector tail is extensionally empty, not definitionally
      -- the vecEmpty term. Check every actual unit in its complete finite vector.
      for unit in prepared.record.units do
        let bound ← mkAppM ``LT.lt #[mkNatLit unit.index, mkNatLit prepared.record.units.size]
        let position ← mkAppM ``Fin.mk #[mkNatLit unit.index, ← mkDecideProof bound]
        let measured ← mkAppM ``Catalog.theoremAt #[mkConst expected, position]
        unless ← isDefEq measured (mkConst unit.unitName) do
          throwError "measured catalog differs at occurrence {unit.theoremName}"
    logInfo m!"MAXIMAL_CATALOG_VALIDATED: {prepared.record.arenaName}; occurrences={prepared.record.units.size}"
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT

#guard_msgs (error) in
#seal_information_theory
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT

open Lean Meta LeanInformationAudit in
run_meta do
  let env ← getEnv
  let records := SealRecords.forRoot env env.header.mainModule
  unless records.map (·.theorems.size) == #[5, 2] &&
      records.map (·.fullEscapeCount) == #[0, 24] do
    throwError "expected both complete maximal catalogs with unchanged escape counts"
  for record in records do
    unless (match record.verdict with
        | .redundant certificate => env.contains certificate
        | .irredundant _ => false) do
      throwError "zero-capture catalog requires a published redundancy certificate"
    for occurrence in record.theorems do
      unless occurrence.uniqueCaptureCount == 0 &&
          occurrence.withoutEscapeCount == record.fullEscapeCount &&
          (match occurrence.certificate with
          | .trivial certificate => env.contains certificate
          | .positive _ => false) do
        throwError "every peer requires a zero-capture triviality certificate"
  if SealRecords.systemCatalogIrredundant env env.header.mainModule then
    throwError "redundant maximal catalogs cannot certify system irredundancy"
  let index ← CensusQuery.indexScope env.header.mainModule
  let head ← IO.Process.output { cmd := "git", args := #["rev-parse", "HEAD"] }
  unless head.exitCode == 0 do throwError "cannot read checkout identity"
  let entries := InformationRegistry.entries env
  unless entries.size == 7 do throwError "expected seven registered occurrences"
  for entry in entries do
    let key : StatementKey := ⟨entry.theoremName, theoremStatementIdentity env entry.theoremName⟩
    match ← CensusQuery.assess index head.stdout.trimAscii.toString key with
    | .certified (.trivialInCatalog payload) =>
        unless payload.root == env.header.mainModule do
          throwError "triviality certificate belongs to a different root"
        logInfo m!"CENSUS_QUERY_TRIVIAL: {entry.theoremName}; registered=true; positive=false"
    | _ => throwError "maximal catalog lacks certified triviality for {entry.theoremName}"
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT

#print axioms no_peer_lowers_escape
end

section
open _root_.D5.S3.ConceptDynamics
open _root_.D5.S3.ConceptDynamics.InformationEscape
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
open _root_.D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers
open RegistrationTemplates
open _root_.D5.S3.ConceptDynamics.InformationEscapeArenas
open SharedArenaFiniteTemplates
open EscapeRecord
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.CIRPT

#print axioms all_peers_trivial
end

end Reg.Catalogs.SharedArenaPeers

#print axioms _root_.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.intervention_strictly_weaker_than_counterfactual.«Reg.D5.S3.ConceptDynamics.Interventions.InterventionCounterfactualSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner.counterfactual_kernel_strictly_finer.«Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualKernelStrictlyFiner/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_varies_on_coupling_fiber.«Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms _root_.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion.boolean_counterfactual_not_identifiable.«Reg.D5.S3.ConceptDynamics.Interventions.CounterfactualIdentifiabilityCriterion/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms _root_.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative.interventional_marginal_sufficient_but_counterfactual_joint_not.«Reg.D5.S3.ConceptDynamics.Sufficiency.SufficiencyIsTargetRelative/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteInterventionArena/finiteProbe».__information_unit
#print axioms _root_.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.observation_strictly_weaker_than_intervention.«Reg.D5.S3.ConceptDynamics.Interventions.ObservationInterventionSeparation.SharedArenaPeers/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__information_unit
#print axioms _root_.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness.intervention_kernel_strictly_finer_than_observation.«Reg.D5.S3.ConceptDynamics.InterventionLaws.ObservationInterventionKernelStrictness/D5.S3.ConceptDynamics.InformationEscape.SharedArenaPeers.finiteObservationInterventionArena/finiteProbe».__information_unit
