import Reg.D5.S3.Combinatorics.LatticeWalkNearMaximalArea
import LeanInformationAudit.Tests.Assessment

test_imported_assessment

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.LatticeWalkSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] {rule}"

run_meta do
  let owner := `D5.S3.Combinatorics.LatticeWalkNearMaximalArea
  let target := owner ++ `result
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == target)
    | throwError "missing original occurrence"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "missing source claim"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated _ := record.result
    | throwError "registration rejected: {(← TemplateBinding.recordJson record).compress}"
  unless record.escape.fromObject.isSome && record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "incomplete four slots"
  let some selection := claim.escapeInput.sourceSelection | throwError "missing source selection"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let some definition := scope.definition | throwError "missing original named entry"
  unless definition.name == owner ++ `claim && info.type.equal (mkConst (owner ++ `claim)) do
    throwError "wrong exact source"
  mustReject "source.absent_occurrence" do
    discard <| (SourceScope.resolve info { selection with definition := none }).run 524288
  mustReject "source.dictionary_or_proof_coordinate" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[2] }).run 524288
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope
      (mkConst (`Reg ++ owner ++ `signature)) (mkConst (`Reg ++ owner ++ `rejected))).run 524288
  let .forallE n nd (.forallE k kd (.forallE hk _ rest hbi) kbi) nbi := definition.value
    | throwError "missing original strict near-maximal range"
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct definition.value
      (.forallE n nd (.forallE k kd (.forallE hk (mkConst ``True) rest hbi) kbi) nbi)).run 524288
  let rec dropSecond : Expr → Expr
    | .forallE n d b bi => .forallE n d (dropSecond b) bi
    | e => if e.isAppOfArity ``And 2 then e.getAppArgs[0]! else e
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct definition.value (dropSecond definition.value)).run 524288
  for name in #[target, event.realizationName] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard axiom closure"
  logInfo m!"[PASS] complete original LatticeWalk source and four-slot contract"

end LeanInformationAuditRegTests.LatticeWalkSourceContract
