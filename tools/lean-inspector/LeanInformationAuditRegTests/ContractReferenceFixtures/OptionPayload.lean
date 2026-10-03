import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.OptionPayload
def value : Option Contract.Seal := some { rootId := `root, options := #[] }
end ContractReferenceFixtures.OptionPayload
