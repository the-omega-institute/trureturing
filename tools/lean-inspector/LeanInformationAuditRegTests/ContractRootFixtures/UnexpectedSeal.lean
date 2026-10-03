import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractRootFixtures.UnexpectedSeal
def sealEntry : Contract.Seal := { rootId := `ContractRoot, options := #[] }
end ContractRootFixtures.UnexpectedSeal
