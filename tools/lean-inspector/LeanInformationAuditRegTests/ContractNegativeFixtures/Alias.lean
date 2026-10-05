import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractNegativeFixtures.Alias
abbrev AliasType := LeanInformationAudit.Contract.Seal
def bad : AliasType := { rootId := Lean.Name.anonymous, catalogs := #[], options := #[] }
end LeanInformationAuditRegTests.ContractNegativeFixtures.Alias
