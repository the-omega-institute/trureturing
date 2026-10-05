import LeanInformationAuditInterface.Contract.Catalog
open Lean LeanInformationAudit.Contract
namespace Boundary.LiteralGrammar
def parenthesized : (LeanInformationAudit.Contract.Seal) := {
  rootId := Name.str (Name.num Name.anonymous (Nat.succ Nat.zero)) "root"
  catalogs := #[],
  options := #[
    ({ name := `nat.annotated, value := .nat (7 : Nat) } : OptionSetting),
    ⟨`nat.chain, .nat (.succ (.succ .zero))⟩,
    { name := `int.ofNatMethod, value := .int (OfNat.ofNat 8) },
    { name := `int.negMethod, value := .int (Neg.neg (8 : Int)) },
    { name := `int.positive, value := .int 7 },
    { name := `int.negative, value := .int (-7) },
    { name := `int.negZero, value := .int (-0) },
    { name := `int.ofNat, value := .int (Int.ofNat (Nat.succ Nat.zero)) },
    { name := `int.negSucc, value := .int (Int.negSucc 4) },
    { name := `bool, value := .bool Bool.true },
    { name := `string, value := .string "λ😀" },
    { name := `name, value := .name (.str .anonymous "entry") }] }
end Boundary.LiteralGrammar
