import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.MissingCatalog
def sealEntry : Contract.Seal := { rootId := `ContractRoot, options := #[] }
end ContractRootFixtures.MissingCatalog
