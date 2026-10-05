import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.IntInstance
local instance : OfNat Int 7 := ⟨Int.ofNat 99⟩
def entry : LeanInformationAudit.Contract.Seal.{0,0} := {
  rootId := `root, catalogs := #[], options := #[{ name := `integer, value := .int 7 }] }
end Boundary.IntInstance
