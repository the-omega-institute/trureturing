import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit
namespace ContractReferenceFixtures.RefPayload
def value : Contract.Ref Nat := { name := `Nat, value := 1 }
end ContractReferenceFixtures.RefPayload
