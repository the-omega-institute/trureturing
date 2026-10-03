import LeanInformationAuditContract.Catalog
namespace Boundary.NegInstance
local instance : Neg Int := ⟨fun _ => Int.ofNat 99⟩
def entry : LeanInformationAudit.Contract.Seal := {
  rootId := `root, options := #[{ name := `integer, value := .int (-7) }] }
end Boundary.NegInstance
