import LeanInformationAuditInterface.Contract.Catalog
namespace ArchitectureFixtures.HelperBody
def entry : LeanInformationAudit.Contract.Seal := { rootId := `root, options := #[] }
def optionCount : Nat := (show LeanInformationAudit.Contract.Seal from entry).options.size
end ArchitectureFixtures.HelperBody
