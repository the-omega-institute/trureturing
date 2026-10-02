import LeanInformationAuditRegTests.ContractFixtures
import LeanInformationAuditRegTests.ContractNegative

namespace LeanInformationAuditRegTests.ContractInventory
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

run_meta do
  let owner := `LeanInformationAuditRegTests.ContractFixtures
  let source ← IO.FS.readFile (← LeanInformationAudit.Repository.source
    "tools/lean-inspector/LeanInformationAuditRegTests/ContractFixtures.lean")
  let aliasType := "LeanInformationAuditRegTests.ContractNegative.AliasType"
  let value := "LeanInformationAuditRegTests.ContractNegative.forwarded"
  for (label, extra) in #[
      ("alias_abbrev", s!"abbrev extra : {aliasType} := {value}"),
      ("alias_opaque", s!"opaque extra : {aliasType} := {value}"),
      ("alias_instance", s!"instance extra : {aliasType} := {value}"),
      ("theorem", "theorem extra : True := by trivial"),
      ("axiom", "axiom extra : True")] do
    let path ← IO.FS.createTempFile
    try
      path.1.putStr (source ++ "\n" ++ extra ++ "\n")
      path.1.flush
      let mut error := "accepted"
      try discard <| Discovery.discover #[owner] fun _ => pure path.2
      catch ex => error := ← ex.toMessageData.toString
      assertTest s!"inventory.{label}_source_without_compiled_entry"
        (error.startsWith "contract.discovery:compiled_inventory_missing")
      logInfo m!"CONTRACT_DIAGNOSTIC inventory.{label} {error}"
    finally IO.FS.removeFile path.2

end LeanInformationAuditRegTests.ContractInventory
