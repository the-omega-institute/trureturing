import LeanInformationAuditRegTests.ContractGuards
import LeanInformationAuditRegTests.ContractReferenceFixtures.Auxiliary
import LeanInformationAuditRegTests.ContractReferenceFixtures.ElaborationEquation
import LeanInformationAuditRegTests.ContractReferenceFixtures.ElaborationDefinition
import LeanInformationAuditRegTests.ContractReferenceFixtures.ImportedElaboration

import LeanInformationAuditRegTests.ContractReferenceFixtures.Coexistence
import LeanInformationAuditRegTests.ContractFixtures

namespace LeanInformationAuditRegTests.ContractAuxiliaries
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  let owner := `LeanInformationAuditRegTests.ContractFixtures
  let source ← IO.FS.readFile (← Discovery.moduleSource owner)
  let entries ← SourceAudit.parse (← getEnv) source owner.toString
  let parent := `LeanInformationAuditRegTests.ContractFixtures.partialSensitivity
  let .defnInfo info ← getConstInfo parent | throwError "fixture:definition"
  let definition : Discovery.Definition := ⟨owner, info, ← Discovery.requireRange parent⟩
  let proof := parent.str "_proof_1"
  assertTest "auxiliary.proof.live"
    (← Discovery.generatedEntryProof owner entries #[definition] (← getEnv) proof)
  assertTest "auxiliary.proof.same_module"
    (!(← Discovery.generatedEntryProof `Other.Module entries #[definition] (← getEnv) proof))
  assertTest "auxiliary.proof.live_path"
    (!(← Discovery.generatedEntryProof owner entries #[] (← getEnv) proof))
  let authored := entries.map fun entry =>
    if entry.sourceName == some parent then
      { entry with authoredNames := entry.authoredNames.push proof } else entry
  assertTest "auxiliary.proof.authored_inventory"
    (!(← Discovery.generatedEntryProof owner authored #[definition] (← getEnv) proof))
  assertTest "auxiliary.proof.value_rejected"
    (!(← Discovery.generatedEntryProof owner entries #[definition] (← getEnv) parent))

run_meta do
  let imported := `LeanInformationAuditRegTests.ContractReferenceFixtures.ImportedElaboration
  let error ← try
    discard <| Discovery.discoverWithStructure #[] #[imported]
    pure "accepted"
  catch ex => ex.toMessageData.toString
  assertTest "auxiliary.negative.ImportedElaboration"
    (error.startsWith "contract.reg:contract_reference_outside_entry:")
  logInfo m!"CONTRACT_DIAGNOSTIC auxiliary.ImportedElaboration {error}"
  for fixture in #["ElaborationEquation", "ElaborationDefinition"] do
    let owner := `LeanInformationAuditRegTests.ContractReferenceFixtures ++ fixture.toName
    let error ← try
      discard <| Discovery.discoverWithStructure #[] #[owner]
      pure "accepted"
    catch ex => ex.toMessageData.toString
    assertTest s!"auxiliary.negative.{fixture}"
      (error.startsWith "contract.reg:contract_reference_outside_entry:")
    logInfo m!"CONTRACT_DIAGNOSTIC auxiliary.{fixture} {error}"
    let parent := `ContractReferenceFixtures ++ fixture.toName ++ `entry
    let .defnInfo info ← getConstInfo parent | throwError "fixture:definition"
    let definition : Discovery.Definition := ⟨owner, info, ← Discovery.requireRange parent⟩
    let source ← IO.FS.readFile (← Discovery.moduleSource owner)
    let entries ← SourceAudit.parse (← getEnv) source owner.toString
    assertTest s!"auxiliary.authored_elaboration.{fixture}"
      (!(← Discovery.generatedEntryAuxiliary owner entries #[definition] (← getEnv)
        (parent.str "eq_def")))
    let entryOnly := entries.filter (·.sourceName == some parent)
    let name := parent.str (if fixture == "ElaborationEquation" then "eq_2" else "eq_def")
    let permission ← Discovery.generatedEntryAuxiliary owner entryOnly #[definition] (← getEnv) name
    assertTest s!"auxiliary.permission.{fixture}" (!permission)
  let owner := `LeanInformationAuditRegTests.ContractReferenceFixtures.Auxiliary
  let source ← IO.FS.readFile (← Discovery.moduleSource owner)
  let definitions ← Discovery.auditModule owner source
  let entries ← SourceAudit.parse (← getEnv) source owner.toString
  for suffix in #["eq_1", "eq_def"] do
    let name := `ContractReferenceFixtures.Auxiliary.entry |>.str suffix
    assertTest s!"auxiliary.positive.{suffix}"
      (← Discovery.generatedEntryAuxiliary owner entries definitions (← getEnv) name)
    let authored := entries.map fun entry =>
      if entry.sourceName == some `ContractReferenceFixtures.Auxiliary.entry then
        { entry with authoredNames := entry.authoredNames.push name } else entry
    assertTest s!"auxiliary.authored_inventory.{suffix}"
      (!(← Discovery.generatedEntryAuxiliary owner authored definitions (← getEnv) name))
    assertTest s!"auxiliary.same_module.{suffix}"
      (!(← Discovery.generatedEntryAuxiliary `Other.Module entries definitions (← getEnv) name))
run_meta do
  let owner := `LeanInformationAuditRegTests.ContractReferenceFixtures.Coexistence
  let error ← try
    let source ← IO.FS.readFile (← Discovery.moduleSource owner)
    let entries ← SourceAudit.parse (← getEnv) source owner.toString
    assertTest "auxiliary.coexistence.reg_syntax"
      (SourceAudit.auditRegCommands `Reg.Coexistence entries).isOk
    let definitions ← Discovery.auditModule owner source
    for suffix in #["eq_1", "eq_def"] do
      assertTest s!"auxiliary.coexistence.{suffix}"
        (← Discovery.generatedEntryAuxiliary owner entries definitions (← getEnv)
          (`ContractReferenceFixtures.Coexistence.entry |>.str suffix))
    pure "accepted"
  catch ex => ex.toMessageData.toString
  assertTest "auxiliary.coexistence.discovery" (error == "accepted")
  logInfo m!"CONTRACT_DIAGNOSTIC coexistence {error}"
end LeanInformationAuditRegTests.ContractAuxiliaries
