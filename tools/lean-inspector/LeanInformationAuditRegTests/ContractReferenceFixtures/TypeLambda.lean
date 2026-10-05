import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.TypeLambda
def value : (fun T : Type _ => T) Contract.Seal := { rootId := `root, catalogs := #[], options := #[] }
end ContractReferenceFixtures.TypeLambda
