import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractLiteralFixtures.Macro
macro "contractLiteralMacro" : term => `(Lean.Name.anonymous)
def macroMetadata : LeanInformationAudit.Contract.Seal := {
  rootId := contractLiteralMacro
  options := #[] }
end LeanInformationAuditRegTests.ContractLiteralFixtures.Macro
