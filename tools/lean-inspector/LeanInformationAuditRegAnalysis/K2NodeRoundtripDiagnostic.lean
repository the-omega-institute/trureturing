import LeanInformationAuditRegTests.Fixtures.ProvenanceFacts
import LeanInformationAudit.Contract.NodeFacts

namespace K2NodeRoundtripDiagnostic
open Lean Meta LeanInformationAudit.Contract

private def kind : Expr → String
  | .bvar _ => "bvar" | .fvar _ => "fvar" | .mvar _ => "mvar"
  | .sort _ => "sort" | .const _ _ => "const" | .app _ _ => "app"
  | .lam _ _ _ _ => "lam" | .forallE _ _ _ _ => "forall"
  | .letE _ _ _ _ _ => "let" | .lit _ => "literal"
  | .mdata _ _ => "metadata" | .proj _ _ _ => "projection"

private def difference (path : List String) (field expected actual : String) : Json :=
  Json.mkObj [("path", toJson path), ("field", toJson field),
    ("expected", toJson expected), ("actual", toJson actual)]

private partial def compare (expected actual : Expr) (path : List String := []) : Option Json :=
  if expected.equal actual then none else
  match expected, actual with
  | .bvar a, .bvar b => some (difference path "bvar" (toString a) (toString b))
  | .fvar a, .fvar b => some (difference path "fvar" (toString a.name) (toString b.name))
  | .mvar a, .mvar b => some (difference path "mvar" (toString a.name) (toString b.name))
  | .sort a, .sort b => some (difference path "level" (reprStr a) (reprStr b))
  | .const a aLevels, .const b bLevels =>
    if a != b then some (difference path "constant" (toString a) (toString b))
    else some (difference path "levels" (reprStr aLevels) (reprStr bLevels))
  | .app af aa, .app bf ba =>
    (compare af bf (path ++ ["function"])).orElse fun _ =>
      compare aa ba (path ++ ["argument"])
  | .lam an aType ab ai, .lam bn bt bb bi
  | .forallE an aType ab ai, .forallE bn bt bb bi =>
    if an != bn then some (difference path "binderName" (toString an) (toString bn))
    else if ai != bi then some (difference path "binderInfo" (reprStr ai) (reprStr bi))
    else (compare aType bt (path ++ ["domain"])).orElse fun _ =>
      compare ab bb (path ++ ["body"])
  | .letE an aType av ab ai, .letE bn bt bv bb bi =>
    if an != bn then some (difference path "binderName" (toString an) (toString bn))
    else if ai != bi then some (difference path "letNondependent" (toString ai) (toString bi))
    else (compare aType bt (path ++ ["letType"])).orElse fun _ =>
      (compare av bv (path ++ ["letValue"])).orElse fun _ =>
        compare ab bb (path ++ ["letBody"])
  | .lit a, .lit b => some (difference path "literal" (reprStr a) (reprStr b))
  | .mdata a ab, .mdata b bb =>
    if a.entries != b.entries then some (difference path "metadata" (reprStr a) (reprStr b))
    else compare ab bb (path ++ ["metadata"])
  | .proj an ai ab, .proj bn bi bb =>
    if an != bn then some (difference path "projectionName" (toString an) (toString bn))
    else if ai != bi then some (difference path "projectionIndex" (toString ai) (toString bi))
    else compare ab bb (path ++ ["projection"])
  | _, _ => some (difference path "expressionKind" (kind expected) (kind actual))

private def operands (find : Name → Option ConstantInfo) (value : Expr) : Except String (Array (String × Expr × Expr)) := do
  let e ← Literal.referencedValue find value
  let args := e.getAppArgs
  match e.getAppFn.constName?.getD .anonymous with
  | ``NodeFact.data | ``NodeFact.proof =>
    unless args.size == 3 do throw "diagnostic:classification_arity"
    return #[("value", args[1]!, args[2]!)]
  | ``NodeFact.type =>
    unless args.size == 2 do throw "diagnostic:type_arity"
    return #[("type", args[0]!, args[1]!)]
  | ``NodeFact.exact | ``NodeFact.equal =>
    unless args.size == 6 do throw "diagnostic:relation_arity"
    return #[("left", args[1]!, args[3]!), ("right", args[2]!, args[4]!)]
  | ``NodeFact.equivalent =>
    unless args.size == 5 do throw "diagnostic:equivalent_arity"
    return #[("left", args[0]!, args[2]!), ("right", args[1]!, args[3]!)]
  | _ => throw "diagnostic:unsupported_constructor"

def publish : MetaM Unit := do
  let some output ← IO.getEnv "K2_NODE_ROUNDTRIP_OUTPUT"
    | throwError "K2_NODE_ROUNDTRIP_OUTPUT required"
  let env ← getEnv
  let owner := fun name => match env.getModuleIdxFor? name with
    | some index => some env.header.modules[index.toNat]!.module
    | none => if (env.find? name).isSome then some env.mainModule else none
  let view : NodeFacts.View := { find := env.find?, owner, external := fun _ => false }
  let coverageName := `LeanInformationAuditRegTests.Fixtures.ProvenanceFacts.coverage
  let some (.defnInfo coverage) := env.find? coverageName | throwError "coverage absent"
  let fields ← IO.ofExcept <| Literal.fields env.find? ``NodeCoverage coverage.value 2
  let names ← IO.ofExcept <| Literal.list "diagnostic.facts"
    (← IO.ofExcept <| Literal.resolveReferences env.find? fields[1]!)
  let mut failed : Array Json := #[]
  let mut compared := 0
  for expression in names do
    let name ← IO.ofExcept <| Literal.name "diagnostic.fact" expression
    let some (.defnInfo info) := env.find? name | throwError "fact absent: {name}"
    for (side, actual, location) in ← IO.ofExcept (operands env.find? info.value) do
      let atNode ← IO.ofExcept <| NodeFacts.coordinate env.find? location
      let expected ← IO.ofExcept <| NodeFacts.locate view atNode
      compared := compared + 1
      if let some mismatch := compare expected actual then
        failed := failed.push <| Json.mkObj [
          ("fact", toJson name), ("side", toJson side),
          ("declaration", toJson atNode.declaration), ("part", toJson (reprStr atNode.part)),
          ("coordinatePath", toJson (atNode.path.map reprStr)), ("difference", mismatch)]
  IO.FS.writeFile output ((Json.mkObj [
    ("facts", toJson names.size), ("operands", toJson compared),
    ("failedOperands", toJson failed.size), ("mismatches", toJson failed)]).pretty ++ "\n")

run_meta publish

end K2NodeRoundtripDiagnostic
