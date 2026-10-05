import LeanInformationAuditInterface.Contract.Catalog
namespace LeanInformationAuditRegTests.ReviewBoundaryFixtures.Constructors
def literal : LeanInformationAudit.Contract.Seal.{0,0} := {
 rootId := Lean.Name.str (Lean.Name.num Lean.Name.anonymous (Nat.succ Nat.zero)) "λ😀"
 catalogs := #[],
  options := #[⟨`test.bool, .bool Bool.false⟩,
   { name := `test.nat, value := .nat (Nat.succ (Nat.succ Nat.zero)) },
   { name := `test.intCtor, value := .int (Int.ofNat 3) },
   { name := `test.name, value := .name (.str .anonymous "item") },
   { name := `test.str, value := .string "字面" }] }
end LeanInformationAuditRegTests.ReviewBoundaryFixtures.Constructors
