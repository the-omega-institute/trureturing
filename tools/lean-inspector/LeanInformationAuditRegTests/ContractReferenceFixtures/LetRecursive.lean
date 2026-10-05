import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.LetRecursive
def entry : Contract.Seal.{0,0} := { rootId := `root, catalogs := #[], options := #[] }
def helper : Unit :=
  let rec entryChild (_ : Unit) : Contract.Seal.{0,0} := entry
  let _ := entryChild ()
  ()
end ContractReferenceFixtures.LetRecursive
