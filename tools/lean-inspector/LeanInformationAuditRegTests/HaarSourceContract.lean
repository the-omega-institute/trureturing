import Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity

open Lean Meta LeanInformationAudit
open Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity

namespace LeanInformationAuditRegTests.HaarSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] Haar rejects {rule}"

private def weakenPremise : Nat → Expr → Expr
  | 0, .forallE n _ b bi => .forallE n (mkConst ``True) b bi
  | i + 1, .forallE n d b bi => .forallE n d (weakenPremise i b) bi
  | _, e => e

private partial def dropConclusion : Expr → Expr
  | .forallE n d b bi => .forallE n d (dropConclusion b) bi
  | .letE n d v b nd => .letE n d v (dropConclusion b) nd
  | _ => mkConst ``True

run_meta do
  let target := ``D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.result
  let owner := `Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity
  let source ← IO.FS.readBinFile ((← Repository.root) /
    "D5/S3/Fourier/Asymptotics/TorusSubgroupHaarContinuity.lean")
  unless Sha256.hex source == "70e70e2d2bea2cbec9c2d3a7b1a13f8a6c91fc12fc70a6d86deae1e725b34b04" do
    throwError "Haar original source changed"
  let env ← getEnv
  let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == target)
    | throwError "Haar expected one original occurrence"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "Haar original claim missing"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated cert := record.result
    | throwError "Haar registration failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do throwError "Haar four slots incomplete"
  let some selection := claim.escapeInput.sourceSelection | throwError "Haar selection missing"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  unless scope.telescope.size == 5 && scope.levels.length == 1 &&
      scope.coordinates.size == 1 && selection.coordinates == #[0] &&
      scope.readouts.size == 1 && selection.readouts[0]!.stateBinder == 3 do
    throwError "Haar original universe/dictionary/parameters/premise changed"
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct info.type (weakenPremise 4 info.type)).run 524288
  mustReject "source.statement_reconstruction" do
    discard <| (SourceScope.reconstruct info.type (dropConclusion info.type)).run 524288
  for coordinates in #[#[0, 1], #[0, 4]] do
    mustReject "source.dictionary_or_proof_coordinate" do
      discard <| (SourceScope.resolve info { selection with coordinates }).run 524288
  mustReject "source.coordinate_dependency" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[] }).run 524288
  -- Selecting ambientHaar H itself would improperly require the fixed Fintype dictionary.
  let measureSelection := { selection with readouts := selection.readouts.map fun r =>
    { r with path := r.path.pop } }
  mustReject "source.coordinate_dependency" do
    discard <| (SourceScope.resolve info measureSelection).run 524288
  let levels := event.levelParams.map Level.param
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope (mkConst ``signature levels)
      (mkConst ``rejected levels)).run 524288
  for name in #[target, ``registration, ``rejected_law, ``Reg.D5.S3.Fourier.Asymptotics.TorusSubgroupHaarContinuity.top_ne_bot] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard Haar axioms: {name}: {axioms}"
    logInfo m!"HAAR_AXIOMS {name}: {axioms}"
  let wire := (Json.arr (← TemplateBinding.reportJson #[(owner, #[event.key])])).compress
  IO.FS.writeFile ((← Repository.root) / ".lake/build/haar-source-evidence.json") (wire ++ "\n")
  logInfo m!"[PASS] Haar original declared_validated evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.HaarSourceContract
