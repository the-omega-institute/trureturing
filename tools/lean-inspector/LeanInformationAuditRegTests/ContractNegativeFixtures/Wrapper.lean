import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Wrapper
structure Box where
  value : LeanInformationAudit.Contract.Seal.{0,0}
def bad : Box := ⟨{ rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }⟩
end LeanInformationAuditRegTests.ContractNegativeFixtures.Wrapper
