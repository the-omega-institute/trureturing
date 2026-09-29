import LeanInformationAuditAnalysis.Tests.RootContract.Producer

open Lean LeanInformationAudit
open LeanInformationAudit.Tests.Occurrence.JointImport

-- Resolve the public qualified name through ordinary imported Lean syntax.
open LeanInformationAuditAnalysis.Tests.RootContract.Producer in
#check LeanInformationAudit.Tests.Occurrence.JointImport.shared.__information_unit
open LeanInformationAuditAnalysis.Tests.RootContract.Producer in
#check LeanInformationAudit.Tests.Occurrence.JointImport.shared.__primitive_realization

expect_information_occurrence shared in arena
  from "LeanInformationAuditAnalysis.Tests.RootContract.Producer"

#seal_information_theory

run_cmd do
  let env ← getEnv
  let root := `LeanInformationAuditAnalysis.Tests.RootContract.Producer
  let owner := `LeanInformationAudit.Tests.Occurrence.JointImport.shared
  for suffix in #[theoremUnitSuffix, primitiveRealizationSuffix,
      "__lowers_escape", "__escape_enriched"] do
    let generated := root ++ owner.str suffix
    let some index := env.getModuleIdxFor? generated
      | throwError "imported companion is missing its compiler owner"
    unless env.header.moduleNames[index.toNat]! == root do
      throwError "qualified companion is not owned by the registering module"
  let some contract := RootCatalogs.find? env root
    | throwError "root contract was lost across imports"
  unless contract.expected.size == 1 && contract.companionPrefix == some root do
    throwError "imported root contract changed"
  if (RootCatalogs.find? env env.header.mainModule).isSome then
    throwError "an imported contract must not select a downstream root"
