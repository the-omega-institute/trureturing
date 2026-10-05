import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.NestedCarrier
def box : Option (Type 1 × Unit) := some (Contract.Seal.{0,0}, ())
def value : (box.getD (ULift.{1} Unit, ())).1 := { rootId := `root, catalogs := #[], options := #[] }
end ContractReferenceFixtures.NestedCarrier
