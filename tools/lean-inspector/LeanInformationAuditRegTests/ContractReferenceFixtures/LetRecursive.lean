import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.LetRecursive
def entry : Contract.Seal := { rootId := `root, options := #[] }
def helper : Unit :=
  let rec entryChild (_ : Unit) : Contract.Seal := entry
  let _ := entryChild ()
  ()
end ContractReferenceFixtures.LetRecursive
