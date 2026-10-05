import LeanInformationAuditInterface.Contract.Catalog
namespace ArchitectureFixtures.HelperBody
def entry : LeanInformationAudit.Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
def optionCount : Nat := (show LeanInformationAudit.Contract.Seal.{0,0} from entry).options.size
end ArchitectureFixtures.HelperBody
