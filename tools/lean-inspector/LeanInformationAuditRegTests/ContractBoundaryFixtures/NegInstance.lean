import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.NegInstance
local instance : Neg Int := ⟨fun _ => Int.ofNat 99⟩
def entry : LeanInformationAudit.Contract.Seal.{0,0} := {
  rootId := `root, catalogs := #[], options := #[{ name := `integer, value := .int (-7) }] }
end Boundary.NegInstance
