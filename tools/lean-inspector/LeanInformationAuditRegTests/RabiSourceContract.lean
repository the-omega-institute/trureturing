import Reg.D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials

open Lean Meta LeanInformationAudit
open Reg.D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials
namespace LeanInformationAuditRegTests.RabiSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] Rabi rejects {rule}"

private def replaceAt (path : List String) (value : Expr)
    (expected : Option Expr := none) : MetaM Expr := do
  match path, value with
  | [], original =>
    if let some expected := expected then
      unless original.equal expected do throwError "original regression clause incorrectly targeted"
    pure (mkConst ``True)
  | "fn" :: steps, .app f a => return .app (← replaceAt steps f expected) a
  | "arg" :: steps, .app f a => return .app f (← replaceAt steps a expected)
  | "body" :: steps, .forallE n d b bi =>
    return .forallE n d (← replaceAt steps b expected) bi
  | "domain" :: steps, .forallE n d b bi =>
    return .forallE n (← replaceAt steps d expected) b bi
  | _, _ => throwError "original regression clause absent"

run_meta do
  let target := ``D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials.result
  let source ← IO.FS.readBinFile ((← Repository.root) / "D5/S3/Quantum/Dynamics/TwoPhotonRabiConstraintPolynomials.lean")
  unless Sha256.hex source == "0323904e42d3bad872983c1fa35607c5b682b0b7f1072319ee4d3b1ca5fd5d2d" do throwError "original source changed"
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
      definition.name == `D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials.claim &&
      definition.path == #[] &&
      selection.coordinates == #[0, 1, 3] &&
      readout.context.size == 5 && selection.readouts[0]!.stateOperand == some #["arg"] do
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
  -- Check each exact guard domain; a bad path must fail before mustReject.
  let coefficientDomain ← withLocalDeclD `N (mkConst ``Nat) fun N =>
    withLocalDeclD `i (mkConst ``Nat) fun i => do
      let guard ← mkAppM ``LE.le #[i, N]
      -- Six intervening binders separate i from N in the original clause.
      return (guard.abstract #[N, i]).liftLooseBVars 1 6
  let coefficientChanged ← replaceAt
    ["body", "body", "body", "arg", "body", "body", "body", "body", "fn", "arg", "body", "domain"]
    definition.value (some coefficientDomain)
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct scope.expanded coefficientChanged).run 524288
  logInfo m!"[PASS] Rabi rejects i <= N binder domain mutation"
  let positiveDomain ← withLocalDeclD `y (mkConst ``Real) fun y => do
    let zero ← mkNumeral (mkConst ``Real) 0
    return (← mkAppM ``LT.lt #[zero, y]).abstract #[y]
  let positiveChanged ← replaceAt
    ["body", "body", "body", "arg", "body", "body", "body", "body", "arg", "body", "domain"]
    definition.value (some positiveDomain)
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct scope.expanded positiveChanged).run 524288
  logInfo m!"[PASS] Rabi rejects 0 < y binder domain mutation"
  -- The original guards, branches, quantifiers and conclusion cannot be omitted.
  for path in #[
      #["body", "body", "domain"],
      #["body", "body", "body", "fn", "arg", "body"],
      #["body", "body", "body", "arg", "body", "domain"],
      #["body", "body", "body", "arg", "body", "body", "body", "domain"],
      #["body", "body", "body", "arg", "body", "body", "body", "body", "fn", "arg", "body", "body"],
      #["body", "body", "body", "arg", "body", "body", "body", "body", "arg", "body", "body"]] do
    let changed ← replaceAt path.toList definition.value
    mustReject "source.statement_reconstruction" do
      discard <| (SourceScope.reconstruct scope.expanded
        changed).run 524288
  for name in #[target, ``registration, ``rejected_law] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard axiom closure: {name}: {axioms}"
    logInfo m!"RABI_AXIOMS {name}: {axioms}"
  let wire := (Json.arr (← TemplateBinding.reportJson #[(`Reg.D5.S3.Quantum.Dynamics.TwoPhotonRabiConstraintPolynomials, #[event.key])])).compress
  IO.FS.writeFile ((← Repository.root) / ".lake/build/rabi-source-evidence.json") (wire ++ "\n")
  logInfo m!"[PASS] Rabi original declared_validated evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.RabiSourceContract
