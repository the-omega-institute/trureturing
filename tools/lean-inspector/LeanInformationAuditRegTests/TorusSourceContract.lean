import Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
import LeanInformationAuditRegTests.CompiledTorusWire

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.TorusSourceContract

set_option trace.InformationRegistration.check true

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] Torus rejects {rule}"

private partial def dropClause : Expr → Expr
  | .forallE n d b bi => .forallE n d (dropClause b) bi
  | .letE n d v b nd => .letE n d v (dropClause b) nd
  | e => if e.isAppOfArity ``And 2 then e.getAppArgs[1]! else e

private partial def replaceLet (value : Expr) : Expr → Expr
  | .forallE n d b bi => .forallE n d (replaceLet value b) bi
  | .letE n d _ b nd => .letE n d value b nd
  | e => e

run_meta do
  let target := ``D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.result
  let owner := `Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution
  let source ← IO.FS.readBinFile ((← Repository.root) /
    "D5/S3/Fourier/Asymptotics/TorusOrbitEquidistribution.lean")
  unless Sha256.hex source == "c3f04b199c1259b849fe76e72cc7bb3c29c0dafbbc452f1f66a1023a924d3bbe" do
    throwError "Torus original source changed"
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == target)
    | throwError "Torus original occurrence missing"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "Torus original claim missing"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated cert := record.result
    | throwError "Torus source registration failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "Torus four slots incomplete"
  let some selection := claim.escapeInput.sourceSelection | throwError "Torus selection missing"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  unless scope.telescope.size == 3 && scope.levels.length == 1 do
    throwError "Torus original telescope or rigid universes changed"
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct info.type (dropClause info.type)).run 524288
  for (coordinates, rule) in #[(#[0], "source.coordinate_dependency"),
      (#[0,1,2], "source.dictionary_or_proof_coordinate"), (#[0,2,3], "source.let_coordinate")] do
    mustReject rule do
      discard <| (SourceScope.resolve info { selection with coordinates }).run 524288
  let changedValue ← (SourceScope.inContext scope.telescope fun locals => do
    let raw := scope.readouts[0]?.map (·.context[3]!.domain) |>.getD (mkConst ``False)
    let value ← mkAppOptM ``Top.top #[some (raw.instantiateRev locals), none]
    pure (value.abstract locals)).run 524288
  mustReject "source.let_reconstruction" do
    discard <| (SourceScope.reconstruct info.type (replaceLet changedValue.1 info.type)).run 524288
  let signature := mkConst ``Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.signature
    (event.levelParams.map Level.param)
  let rejected := mkConst ``Reg.D5.S3.Fourier.Asymptotics.TorusOrbitEquidistribution.rejected
    (event.levelParams.map Level.param)
  let failure ← try
    discard <| (SourceScope.validateFields scope signature rejected).run 524288
    pure "accepted"
  catch e => e.toMessageData.toString
  unless failure.contains "source.actual_observation" do throwError "wrong actual accepted: {failure}"
  for name in #[target, event.realizationName] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard Torus axioms"
    logInfo m!"TORUS_AXIOMS {name}: {axioms}"
  let wire := (Json.arr (← TemplateBinding.reportJson #[(owner, #[event.key])])).compress
  IO.FS.writeFile ((← Repository.root) / ".lake/build/torus-source-evidence.json") (wire ++ "\n")
  unless wire == CompiledTorusWire.canonical do throwError "Torus compiled wire differs from production export"
  logInfo m!"[PASS] Torus full original source declared_validated evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.TorusSourceContract
