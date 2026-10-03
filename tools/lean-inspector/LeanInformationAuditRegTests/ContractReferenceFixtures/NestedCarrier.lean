import LeanInformationAuditContract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.NestedCarrier
def box : Option (Type × Unit) := some (Contract.Seal, ())
def value : (box.getD (Unit, ())).1 := { rootId := `root, options := #[] }
end ContractReferenceFixtures.NestedCarrier
