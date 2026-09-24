import LeanInformationAudit.Tests.Occurrence.JointImport.Shared

open Lean LeanInformationAudit LeanInformationAudit.Tests.Occurrence.JointImport

-- Expected rows come from the named theorem and explicit contributor, before
-- registration; none is obtained from InformationRegistry or seal output.
run_cmd do
  let root := (← getEnv).header.mainModule
  let expected : Array SnapshotOccurrence := #[{
    objectArenaName := `LeanInformationAudit.Tests.Occurrence.JointImport.arena
    theoremName := `LeanInformationAudit.Tests.Occurrence.JointImport.shared
    statementIdentity := theoremStatementIdentity (← getEnv)
      `LeanInformationAudit.Tests.Occurrence.JointImport.shared
    registrationModuleName := root }]
  RootCatalogs.declare {
    rootId := root, expected, source := expected, baseline := expected
    companionPrefix := some root }

register_information_theorem shared in arena
  primitives readout.toPrimitiveBundle
  realization inline readout := by exact ⟨Iff.rfl⟩

#seal_information_theory

run_cmd do
  let env ← getEnv
  let owner := `LeanInformationAudit.Tests.Occurrence.JointImport.shared
  for suffix in #[theoremUnitSuffix, primitiveRealizationSuffix,
      "__lowers_escape", "__escape_enriched"] do
    let generated := env.header.mainModule ++ owner.str suffix
    unless localCompanionName env owner suffix == generated &&
        env.contains generated && !(env.contains (owner.str suffix)) do
      throwError "root contract must publish qualified companions without old-name aliases"
