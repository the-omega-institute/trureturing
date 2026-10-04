import LeanInformationAuditInterface.Contract.Catalog

namespace LeanInformationAuditRegTests.ContractLiteralFixtures.Literals
def literalSeal : LeanInformationAudit.Contract.Seal := {
  rootId := .str (.num .anonymous 7) "root"
  options := #[
    { name := `test.integer, value := .int (.negSucc 4) },
    { name := `test.string, value := .string "λ😀" },
    { name := `test.bool, value := .bool true },
    { name := `test.name, value := .name (.str .anonymous "entry") }] }
end LeanInformationAuditRegTests.ContractLiteralFixtures.Literals
