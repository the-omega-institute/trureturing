import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.SigmaPayload
def value : Sigma (fun _ : Unit => Contract.Seal) := ⟨(), { rootId := `root, catalogs := #[], options := #[] }⟩
end ContractReferenceFixtures.SigmaPayload
