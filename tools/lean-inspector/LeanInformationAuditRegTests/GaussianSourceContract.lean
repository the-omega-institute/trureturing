import Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit

open Lean Meta LeanInformationAudit

namespace LeanInformationAuditRegTests.GaussianSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] Gaussian rejects {rule}"

/-- Remove one actual conjunct under both existential witnesses. -/
private partial def dropConclusion (keep : Nat) : Expr → Expr
  | .forallE n d b bi => .forallE n d (dropConclusion keep b) bi
  | .lam n d b bi => .lam n d (dropConclusion keep b) bi
  | e =>
    if e.isAppOfArity ``And 2 then e.getAppArgs[keep]!
    else if e.isAppOfArity ``Exists 2 then
      mkApp2 e.getAppFn e.getAppArgs[0]! (dropConclusion keep e.getAppArgs[1]!)
    else e

run_meta do
  let target := ``D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.result
  let owner := `Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit
  let source ← IO.FS.readBinFile ((← Repository.root) /
    "D5/S3/Fourier/Asymptotics/CountableGaussianQuadraticLimit.lean")
  unless Sha256.hex source == "82443192d04cd30c222f5f914436c735e92f59c190461f508ceeec999d545e70" do
    throwError "Gaussian original source changed"
  let env ← getEnv
  let some event := (TemplateBinding.inventory env).find? (·.key.theoremName == target)
    | throwError "Gaussian original occurrence missing"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "Gaussian original claim missing"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated cert := record.result
    | throwError "Gaussian source registration failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "Gaussian four slots incomplete"
  let some selection := claim.escapeInput.sourceSelection | throwError "Gaussian selection missing"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  unless scope.telescope.size == 12 && scope.levels.isEmpty &&
      selection.coordinates == #[0, 4, 5, 12, 13] &&
      (scope.readouts[0]?.map (·.context.size)).getD 0 == 15 && selection.readouts[0]!.stateBinder == 14 do
    throwError "Gaussian full telescope or nested coordinates changed"
  for keep in #[0, 1] do
    mustReject "source.statement_reconstruction" do
      discard <| (SourceScope.reconstruct info.type (dropConclusion keep info.type)).run 524288
  for coordinates in #[#[0, 4, 5], #[0, 4, 5, 12]] do
    mustReject "source.coordinate_dependency" do
      discard <| (SourceScope.resolve info { selection with coordinates }).run 524288
  let signature := mkConst ``Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.signature
  let rejected := mkConst ``Reg.D5.S3.Fourier.Asymptotics.CountableGaussianQuadraticLimit.rejected
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope signature rejected).run 524288
  for name in #[target, event.realizationName] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard Gaussian axioms"
    logInfo m!"GAUSSIAN_AXIOMS {name}: {axioms}"
  let wire := (Json.arr (← TemplateBinding.reportJson #[(owner, #[event.key])])).compress
  IO.FS.writeFile ((← Repository.root) / ".lake/build/gaussian-source-evidence.json") (wire ++ "\n")
  logInfo m!"[PASS] Gaussian full original source declared_validated evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.GaussianSourceContract
