import Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm

open Lean Meta LeanInformationAudit
open Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm
namespace LeanInformationAuditRegTests.BosonSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] Boson rejects {rule}"

private def replaceAt : List String → Expr → MetaM Expr
  | [], _ => pure (mkConst ``True)
  | "fn" :: steps, .app f a => return .app (← replaceAt steps f) a
  | "arg" :: steps, .app f a => return .app f (← replaceAt steps a)
  | "body" :: steps, .forallE n d b bi => return .forallE n d (← replaceAt steps b) bi
  | "domain" :: steps, .forallE n d b bi => return .forallE n (← replaceAt steps d) b bi
  | _, _ => throwError "original regression clause absent"

run_meta do
  let target := ``D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.result
  let source ← IO.FS.readBinFile ((← Repository.root) / "D5/S3/Quantum/FockSpace/BosonOrderingStirlingClosedForm.lean")
  unless Sha256.hex source == "a21529b9b1a8c81e92ae81395307c000d5aa83a867224a57f70f08bddfc95259" do throwError "original source changed"
  let env ← getEnv
  let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == target)
    | throwError "expected one original occurrence"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "original claim missing"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated cert := record.result
    | throwError "registration failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "four slots incomplete"
  let some selection := claim.escapeInput.sourceSelection | throwError "selection missing"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let some definition := scope.definition | throwError "named claim entry missing"
  let #[readout] := scope.readouts | throwError "expected one readout"
  unless scope.source.equal info.type && scope.telescope.isEmpty && scope.levels.isEmpty &&
      definition.name == `D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm.claim &&
      definition.path == #[] &&
      selection.coordinates == #[0, 1] &&
      readout.context.size == 4 && selection.readouts[0]!.stateBinder == 3 do
    throwError "original raw statement or observation scope changed"
  mustReject "source.absent_occurrence" do
    discard <| (SourceScope.resolve info { selection with definition := none }).run 524288
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope (mkConst ``signature)
      (mkConst ``rejected)).run 524288
  mustReject "source.operand_identity" do
    discard <| SourceOperands.check target #[mkConst target] 524288 none (some definition.value)
  mustReject "source.duplicate_occurrence" do
    discard <| (SourceScope.resolve info { selection with
      readouts := selection.readouts ++ selection.readouts }).run 524288
  -- The original guards, branches, quantifiers and conclusion cannot be omitted.
  for path in #[
      #["body", "body", "domain"],
      #["body", "body", "body", "body"]] do
    let changed ← replaceAt path.toList definition.value
    mustReject "source.statement_reconstruction" do
      discard <| (SourceScope.reconstruct scope.expanded
        changed).run 524288
  for name in #[target, ``registration, ``rejected_law] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard axiom closure: {name}: {axioms}"
    logInfo m!"BOSON_AXIOMS {name}: {axioms}"
  let wire := (Json.arr (← TemplateBinding.reportJson #[(`Reg.D5.S3.Quantum.FockSpace.BosonOrderingStirlingClosedForm, #[event.key])])).compress
  IO.FS.writeFile ((← Repository.root) / ".lake/build/boson-source-evidence.json") (wire ++ "\n")
  logInfo m!"[PASS] Boson original declared_validated evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.BosonSourceContract
