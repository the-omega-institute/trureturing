import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.TypeLambda
def value : (fun T : Type => T) Contract.Seal := { rootId := `root, options := #[] }
end ContractReferenceFixtures.TypeLambda
