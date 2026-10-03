import LeanInformationAuditContract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Alias
abbrev AliasType := LeanInformationAudit.Contract.Seal
def bad : AliasType := { rootId := Lean.Name.anonymous, options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Alias
