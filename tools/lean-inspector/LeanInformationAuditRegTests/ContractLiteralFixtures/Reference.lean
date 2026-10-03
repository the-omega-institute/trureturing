import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractLiteralFixtures.Reference
def metadataName : Lean.Name := .anonymous
def referencedMetadata : LeanInformationAudit.Contract.Seal := {
  rootId := metadataName
  options := #[] }
end LeanInformationAuditRegTests.ContractLiteralFixtures.Reference
