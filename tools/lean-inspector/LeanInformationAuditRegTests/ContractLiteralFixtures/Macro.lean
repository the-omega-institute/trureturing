import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractLiteralFixtures.Macro
macro "contractLiteralMacro" : term => `(Lean.Name.anonymous)
def macroMetadata : LeanInformationAudit.Contract.Seal.{0,0} := {
  rootId := contractLiteralMacro
  catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractLiteralFixtures.Macro
