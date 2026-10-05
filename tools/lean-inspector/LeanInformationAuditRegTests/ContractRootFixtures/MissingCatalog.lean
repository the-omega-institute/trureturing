import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.MissingCatalog
def sealEntry : Contract.Seal.{0,0} := { rootId := `ContractRoot, catalogs := #[], options := #[] }
end ContractRootFixtures.MissingCatalog
