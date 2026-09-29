import Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions

open Lean Meta LeanInformationAudit
open Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions

namespace LeanInformationAuditRegTests.TetrahelixSourceContract

private def mustReject (rule : String) (action : MetaM Unit) : MetaM Unit := do
  let result ← try action; pure "accepted" catch e => e.toMessageData.toString
  unless result.contains rule do throwError "expected {rule}, got {result}"
  logInfo m!"[PASS] Tetrahelix rejects {rule}"

private def replaceAt : List String → Expr → MetaM Expr
  | [], _ => pure (mkConst ``True)
  | "fn" :: steps, .app f a => return .app (← replaceAt steps f) a
  | "arg" :: steps, .app f a => return .app f (← replaceAt steps a)
  | "body" :: steps, .forallE n d b bi => return .forallE n d (← replaceAt steps b) bi
  | _, _ => throwError "Tetrahelix regression clause path is absent"

run_meta do
  let target := ``D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions.result
  let owner := `Reg.D5.S1.Recurrence.BoerdijkCoxeterGeneratingFunctions
  let source ← IO.FS.readBinFile ((← Repository.root) /
    "D5/S1/Recurrence/BoerdijkCoxeterGeneratingFunctions.lean")
  unless Sha256.hex source == "b0b9950cbe5055e4067a07d5f6598995daa854b0157a8d8778d36470842d6740" do
    throwError "Tetrahelix original source changed"
  let env ← getEnv
  let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == target)
    | throwError "Tetrahelix expected one original occurrence"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "Tetrahelix original claim missing"
  let record ← TemplateBinding.assess event (some claim)
  let .declaredValidated cert := record.result
    | throwError "Tetrahelix registration failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do
    throwError "Tetrahelix four slots incomplete"
  let some selection := claim.escapeInput.sourceSelection | throwError "selection missing"
  let info ← getConstInfo target
  let (scope, _) ← (SourceScope.resolve info selection).run 524288
  let #[readout] := scope.readouts | throwError "Tetrahelix expected one readout"
  unless scope.telescope.isEmpty && scope.levels.isEmpty && scope.coordinates.isEmpty &&
      scope.readouts.size == 1 && readout.context.size == 1 &&
      selection.readouts[0]!.stateBinder == 0 do
    throwError "Tetrahelix original lexical scope changed"
  -- Each of the nine all-n clauses is individually essential to reconstruction.
  for i in [:9] do
    let suffix := List.replicate i "arg" ++ (if i == 8 then [] else ["fn", "arg"])
    let weakened ← replaceAt (["fn", "arg", "body"] ++ suffix) info.type
    mustReject "source.statement_reconstruction" do
      discard <| (SourceScope.reconstruct info.type weakened).run 524288
    logInfo m!"[PASS] Tetrahelix geometric clause {i + 1} cannot be omitted"
  -- Nor can any of the three infinite PowerSeries identities be omitted.
  for i in [:3] do
    let suffix := List.replicate (i + 1) "arg" ++ (if i == 2 then [] else ["fn", "arg"])
    let weakened ← replaceAt suffix info.type
    mustReject "source.statement_reconstruction" do
      discard <| (SourceScope.reconstruct info.type weakened).run 524288
    logInfo m!"[PASS] Tetrahelix infinite series {i + 1} cannot be omitted"
  mustReject "source.actual_observation" do
    discard <| (SourceScope.validateFields scope (mkConst ``signature)
      (mkConst ``rejected)).run 524288
  mustReject "source.state_binder" do
    discard <| (SourceScope.resolve info { selection with coordinates := #[0] }).run 524288
  for name in #[target, ``registration, ``rejected_law] do
    let axioms ← collectAxioms name
    unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
      throwError "nonstandard Tetrahelix axioms: {name}: {axioms}"
    logInfo m!"TETRAHELIX_AXIOMS {name}: {axioms}"
  let wire := (Json.arr (← TemplateBinding.reportJson #[(owner, #[event.key])])).compress
  IO.FS.writeFile ((← Repository.root) / ".lake/build/tetrahelix-source-evidence.json") (wire ++ "\n")
  logInfo m!"[PASS] Tetrahelix original declared_validated evidence_ref={cert.evidenceRef}"

end LeanInformationAuditRegTests.TetrahelixSourceContract
