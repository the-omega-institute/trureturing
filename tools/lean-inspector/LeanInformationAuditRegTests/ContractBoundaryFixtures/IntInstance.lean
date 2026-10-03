import LeanInformationAuditInterface.Contract.Catalog
namespace Boundary.IntInstance
local instance : OfNat Int 7 := ⟨Int.ofNat 99⟩
def entry : LeanInformationAudit.Contract.Seal := {
  rootId := `root, options := #[{ name := `integer, value := .int 7 }] }
end Boundary.IntInstance
