import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Wrapper
structure Box where
  value : LeanInformationAudit.Contract.Seal
def bad : Box := ⟨{ rootId := Lean.Name.anonymous, options := #[] }⟩
end LeanInformationAuditRegTests.ContractNegativeFixtures.Wrapper
