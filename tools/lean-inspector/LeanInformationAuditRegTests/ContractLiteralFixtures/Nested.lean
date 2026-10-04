import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractLiteralFixtures.Nested
def nestedMetadata : LeanInformationAudit.Contract.RootCatalog := {
  data := {
    rootId := .anonymous
    expected := #[]
    source := #[]
    baseline := #[]
    companionPrefix := some (by exact Lean.Name.anonymous) } }
end LeanInformationAuditRegTests.ContractLiteralFixtures.Nested
