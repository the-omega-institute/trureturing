import Reg.D5.S3.Constants.Billiards.CollidingBlocksRecords
import Reg.D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality
import Reg.D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling

import LeanInformationAuditRegTests.NegativeNamedEntry
import LeanInformationAuditRegTests.CompiledNamedClaimWire

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.NamedClaimSourceContract

private partial def changeQuantifier : Expr → Expr
  | .forallE n d b bi => .forallE n d (changeQuantifier b) bi
  | e => if e.isAppOfArity ``Exists 2 then
      match e.getAppArgs[1]! with
      | .lam n d b bi => .forallE n d b bi
      | _ => e
    else e

private partial def dropExistence : Expr → Expr
  | .forallE n d b bi => .forallE n d (dropExistence b) bi
  | e => if e.isAppOfArity ``And 2 then e.getAppArgs[1]! else e

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] named source rejects {rule}"

run_meta do
  let owners := #[`D5.S3.Constants.Billiards.CollidingBlocksRecords,
    `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality,
    `D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling]
  let mut exportSelection := #[]
  for owner in owners do
    let target := owner ++ `result
    let env ← getEnv
    let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == target)
      | throwError "original occurrence absent: {target}"
    let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
      | throwError "original claim absent: {target}"
    let record ← TemplateBinding.assess event (some claim)
    let .declaredValidated cert := record.result
      | throwError "named source failed: {(← TemplateBinding.recordJson record).compress}"
    unless record.escape.fromObject.isSome && record.escape.bridgeKind == "source-equivalence" &&
        record.escape.continuation.any (·.kind == "open") do throwError "four slots incomplete"
    let some selection := claim.escapeInput.sourceSelection | throwError "selection missing"
    let info ← getConstInfo target
    let (scope, _) ← (SourceScope.resolve info selection).run 524288
    unless info.type.equal (mkConst (owner ++ `claim)) && scope.source.equal info.type &&
        scope.telescope.isEmpty && scope.levels.isEmpty do throwError "raw theorem root changed"
    let some definition := scope.definition | throwError "entry absent"
    unless definition.name == owner ++ `claim && definition.owner == owner do
      throwError "wrong original definition"
    mustReject "source.absent_occurrence" do
      discard <| (SourceScope.resolve info { selection with definition := none }).run 524288
    mustReject "source.telescope_reconstruction" do
      let .forallE n d b _ := definition.value | throwError "original n binder absent"
      discard <| (SourceScope.reconstruct definition.value (.forallE n d b .implicit)).run 524288
    mustReject "source.statement_reconstruction" do
      let .forallE n d (.forallE hn _ body bi) nbi := definition.value
        | throwError "original guard absent"
      discard <| (SourceScope.reconstruct definition.value
        (.forallE n d (.forallE hn (mkConst ``True) body bi) nbi)).run 524288
    if owner == `D5.S3.StatisticalMechanics.RandomWalks.KnightWalkRangeIntegrality then
      mustReject "source.statement_reconstruction" do
        discard <| (SourceScope.reconstruct definition.value
          (changeQuantifier definition.value)).run 524288
    if owner == `D5.S3.StatisticalMechanics.Sandpiles.TorusColumnToppling then
      mustReject "source.statement_reconstruction" do
        discard <| (SourceScope.reconstruct definition.value
          (dropExistence definition.value)).run 524288
    if owner == `D5.S3.Constants.Billiards.CollidingBlocksRecords then
      mustReject "source.statement_reconstruction" do
        let .forallE n d (.forallE hn hd (.forallE ha _ body bi) hbi) nbi := definition.value
          | throwError "record antecedent absent"
        discard <| (SourceScope.reconstruct definition.value
          (.forallE n d (.forallE hn hd (.forallE ha (mkConst ``True) body bi) hbi) nbi)).run 524288
    mustReject "source.dictionary_or_proof_coordinate" do
      discard <| (SourceScope.resolve info { selection with coordinates := #[1] }).run 524288
    let regOwner := `Reg ++ owner
    mustReject "source.actual_observation" do
      discard <| (SourceScope.validateFields scope (mkConst (regOwner ++ `signature))
        (mkConst (regOwner ++ `rejected))).run 524288
    mustReject "source.operand_identity" do
      discard <| SourceOperands.check target #[mkConst target] 524288 none (some definition.value)
    -- Inspect discarded truth/decision/proof operands before reducing the actual readout.
    let actual := mkConst (regOwner ++ `actual)
    let decision ← mkAppM ``Classical.propDecidable #[info.type]
    for (domain, argument) in #[(mkSort .zero, info.type),
        (info.type, mkConst target), (← inferType decision, decision)] do
      let tainted := mkApp (.lam `ignored domain actual .default) argument
      mustReject "source.operand_identity" do
        discard <| SourceOperands.check target #[tainted] 524288 none (some definition.value)
    for name in #[target, event.realizationName] do
      let axioms ← collectAxioms name
      unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
        throwError "nonstandard axiom closure"
      logInfo m!"NAMED_AXIOMS {name}: {axioms}"
    exportSelection := exportSelection.push (regOwner, #[event.key])
    logInfo m!"[PASS] original named claim declared_validated: {target} {cert.evidenceRef}"
  let negativeOwner := `D5.S3.Quantum.Information.NiceErrorBasisNonNormalStabilizer
  let some negativeEvent := (TemplateBinding.inventory (← getEnv)).find?
      (·.key.theoremName == negativeOwner ++ `result)
    | throwError "fourth original occurrence absent"
  exportSelection := exportSelection.push (`Reg ++ negativeOwner, #[negativeEvent.key])
  let wire := (Json.arr (← TemplateBinding.reportJson exportSelection)).compress
  IO.FS.writeFile ((← Repository.root) / ".lake/build/named-claim-source-evidence.json") (wire ++ "\n")
  unless wire == CompiledNamedClaimWire.canonical do
    throwError "named claim fixture differs from production export"

end LeanInformationAuditRegTests.NamedClaimSourceContract
