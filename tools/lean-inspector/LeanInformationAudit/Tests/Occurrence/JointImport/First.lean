import LeanInformationAudit.Tests.Occurrence.JointImport.Shared

open Lean LeanInformationAudit LeanInformationAudit.Tests.Occurrence.JointImport

-- Each independently compiled root publishes genuine qualified companions.
run_cmd do
  let root := (← getEnv).header.mainModule
  let rows : Array SnapshotOccurrence := #[{
    objectArenaName := ``arena, theoremName := ``shared
    statementIdentity := theoremStatementIdentity (← getEnv) ``shared
    registrationModuleName := root }]
  RootCatalogs.declare {
    rootId := root, expected := rows, source := rows, baseline := rows
    companionPrefix := some root }

register_information_theorem shared in arena
  primitives readout.toPrimitiveBundle realization bridge

#seal_information_theory

-- Source-level companion references must resolve in their own sealing module.
open LeanInformationAudit.Tests.Occurrence.JointImport.First in
#check LeanInformationAudit.Tests.Occurrence.JointImport.shared.__information_unit
open LeanInformationAudit.Tests.Occurrence.JointImport.First in
#check LeanInformationAudit.Tests.Occurrence.JointImport.shared.__lowers_escape
open LeanInformationAudit.Tests.Occurrence.JointImport.First in
#check LeanInformationAudit.Tests.Occurrence.JointImport.shared.__escape_enriched
open LeanInformationAudit.Tests.Occurrence.JointImport.First in
#check LeanInformationAudit.Tests.Occurrence.JointImport.arena.__information_catalog
open LeanInformationAudit.Tests.Occurrence.JointImport.First in
#check LeanInformationAudit.Tests.Occurrence.JointImport.arena.__catalog_irredundant
