import LeanInformationAuditRegTests.ContractGuards

namespace LeanInformationAuditRegTests.ContractLiterals
open Lean Meta Elab Command LeanInformationAudit.Contract
open LeanInformationAuditRegTests.ContractGuards

def selection : SourceSelection := {
  owner := `D5.Test
  definition := some { owner := `D5.Test, name := `D5.Test.claim, path := #["arg"] }
  coordinates := #[0, 2]
  readouts := #[{
    path := #["body", "arg"]
    stateBinder := 2
    functionOperand := true
    stateOperand := some #["arg"], booleanPredicate := true }] }

def settingValues : Array OptionSetting := #[
  { name := `Elab.async, value := .bool true },
  { name := `autoImplicit, value := .bool false },
  { name := `backward.isDefEq.respectTransparency, value := .bool false },
  { name := `backward.isDefEq.respectTransparency.types, value := .bool false },
  { name := `internal.cmdlineSnapshots, value := .bool true },
  { name := `linter.mathlibStandardSet, value := .bool true },
  { name := `maxHeartbeats, value := .nat 2000000 },
  { name := `maxRecDepth, value := .nat 100000 },
  { name := `maxSynthPendingDepth, value := .nat 3 },
  { name := `pp.unicode.fun, value := .bool true },
  { name := `relaxedAutoImplicit, value := .bool false },
  { name := `trace.InformationRegistration.check, value := .bool true },
  { name := `test.integer, value := .int (.negSucc 4) },
  { name := `test.string, value := .string "λ😀" },
  { name := `test.name, value := .name (.str (.num (.str .anonymous "_private") 7) "entry") }]

def duplicates : Array OptionSetting := #[
  { name := `maxRecDepth, value := .nat 1 }, { name := `maxRecDepth, value := .nat 2 }]

def constructorTypes : TemplateEnrollment.{_, 0} (@Nat.succ) := {
  name := `Nat.succ, version := 1, constructors := #[{ name := `Nat, type := Nat }], options := #[] }

run_meta do
  let .ok s := Literal.sourceSelection (← getConstInfo ``selection).value!
    | throwError "[FAIL] literal.selection"
  assertTest "literal.selection_all_fields"
    (s.owner == `D5.Test && s.definition.any (fun d => d.name == `D5.Test.claim && d.path == #["arg"]) &&
      s.coordinates == #[0, 2] && s.readouts.any (fun r => r.stateBinder == 2 &&
        r.functionOperand && r.booleanPredicate && r.stateOperand == some #["arg"]))
  let .ok values := Literal.options (← getConstInfo ``settingValues).value!
    | throwError "[FAIL] literal.options"
  assertTest "literal.options_census_twelve_keys" ((#[`Elab.async, `autoImplicit, `backward.isDefEq.respectTransparency,
      `backward.isDefEq.respectTransparency.types, `internal.cmdlineSnapshots,
      `linter.mathlibStandardSet, `maxHeartbeats, `maxRecDepth, `maxSynthPendingDepth,
      `pp.unicode.fun, `relaxedAutoImplicit, `trace.InformationRegistration.check,
      `test.integer, `test.string, `test.name]).all values.contains)
  assertTest "literal.raw_name_numeric_component"
    (values.find? `test.name == some (.ofName (.str (.num (.str .anonymous "_private") 7) "entry")))
  assertTest "literal.integer_string"
    (values.find? `test.integer == some (.ofInt (-5)) &&
      values.find? `test.string == some (.ofString "λ😀"))
  let error : String := match Literal.options (← getConstInfo ``duplicates).value! with
    | .ok _ => "accepted"
    | .error error => error
  assertTest "literal.duplicate_option" (error == "contract.literal:options:duplicate:maxRecDepth")
  let .defnInfo info ← getConstInfo ``constructorTypes | throwError "setup: enrollment"
  let input ← Decoder.enrollment (← getEnv).header.mainModule info ""
  assertTest "literal.type_reference" (input.constructors == #[`Nat] && input.name == `Nat.succ)

end LeanInformationAuditRegTests.ContractLiterals
