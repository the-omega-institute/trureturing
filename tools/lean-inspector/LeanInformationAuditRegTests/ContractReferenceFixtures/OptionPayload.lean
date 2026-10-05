import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.OptionPayload
def value : Option Contract.Seal := some { rootId := `root, catalogs := #[], options := #[] }
end ContractReferenceFixtures.OptionPayload
