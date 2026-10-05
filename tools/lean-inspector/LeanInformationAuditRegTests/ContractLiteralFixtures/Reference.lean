import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractLiteralFixtures.Reference
def metadataName : Lean.Name := .anonymous
def referencedMetadata : LeanInformationAudit.Contract.Seal.{0,0} := {
  rootId := metadataName
  catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractLiteralFixtures.Reference
