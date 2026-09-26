import Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction
import LeanInformationAuditRegTests.CompiledQuantumWire
import LeanInformationAuditRegTests.CompiledQuantumHistoricalWire

open Lean Meta LeanInformationAudit
namespace LeanInformationAuditRegTests.QuantumSourceContract

set_option trace.InformationRegistration.check true

-- The same regression runs in the current environment and in the isolated,
-- exact historical source environment. The historical name is never aliased.
run_meta do
  let sourceOwner := `D5.S3.Quantum.Information.ActualQubitChordObstruction
  let owner := `Reg.D5.S3.Quantum.Information.ActualQubitChordObstruction
  let current := sourceOwner ++ `actual_two_probe_chord_and_qfi
  let historical := sourceOwner ++ `actual_two_probe_chord_obstruction
  let isCurrent := (← getEnv).contains current
  let name := if isCurrent then current else historical
  let absent := if isCurrent then historical else current
  let hash := if isCurrent then
      "4f45e964a8a60de2e526fa8ecc9d7290e89b061a1a687359917d065453126fb0"
    else "e38587117aa2fd85bf40596abc5c556725faafbfabcaddb21ae96b9f9211f61b"
  let expectedSize := if isCurrent then 36217 else 22806
  let source ← IO.FS.readBinFile ((← Repository.root) /
    "D5/S3/Quantum/Information/ActualQubitChordObstruction.lean")
  unless Sha256.hex source == hash && source.size == expectedSize do
    throwError "quantum original source bytes changed"
  let info ← getConstInfo name
  unless info.isTheorem &&
      RegistrationReifier.declaringModuleOf (← getEnv) name == some sourceOwner &&
      !(← getEnv).contains absent do
    throwError "quantum original name/owner or historical isolation differs"
  let axioms ← collectAxioms name
  unless axioms.all (#[`propext, `Classical.choice, `Quot.sound].contains ·) do
    throwError "quantum original axiom closure"
  let mut pending := [(info.type, 0)]
  let mut unique : Std.HashSet ExprStructEq := {}
  let mut visits := 0
  let mut depth := 0
  while let (e, d) :: rest := pending do
    pending := rest
    visits := visits + 1
    depth := max depth d
    unique := unique.insert ⟨e⟩
    match e with
    | .app f a => pending := (f, d+1) :: (a, d+1) :: pending
    | .lam _ t b _ | .forallE _ t b _ => pending := (t, d+1) :: (b, d+1) :: pending
    | .letE _ t v b _ => pending := (t, d+1) :: (v, d+1) :: (b, d+1) :: pending
    | .mdata _ b | .proj _ _ b => pending := (b, d+1) :: pending
    | _ => pure ()
  let .ok (rawBytes, rawWork) := TemplateAudit.compactRawEncoding info.levelParams info.type
    | throwError "quantum raw identity exceeded the unchanged budget"
  let env ← getEnv
  let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == name)
    | throwError "quantum original must have exactly one registration"
  unless event.key.registrationModule == owner do throwError "quantum Reg owner differs"
  let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
    | throwError "quantum original claim missing"
  unless isNoncomputable env event.realizationName && isNoncomputable env event.unitName do
    throwError "retained quantum unit lost the record's noncomputability"
  let before := (TemplateBinding.observedAssessments env).size
  let start ← IO.monoMsNow
  let heartbeats ← IO.getNumHeartbeats
  let record ← TemplateBinding.assess event (some claim)
  let heartbeats := (← IO.getNumHeartbeats) - heartbeats
  let elapsed := (← IO.monoMsNow) - start
  unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
    throwError "quantum assessment used a cached result"
  let .declaredValidated cert := record.result
    | throwError "quantum assessment failed: {(← TemplateBinding.recordJson record).compress}"
  unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
      record.escape.bridgeKind == "source-equivalence" &&
      record.escape.continuation.any (·.kind == "open") do
    throwError "quantum four slots incomplete"
  let binding := cert.sourceBinding.get!
  unless (binding.getObjValAs? Nat "telescope_size").toOption == some 7 &&
      (binding.getObjValAs? Nat "level_count").toOption == some 0 &&
      (binding.getObjValAs? (Array Nat) "coordinates").toOption == some #[] &&
      (binding.getObjValAs? String "source_type_identity").toOption == some (Sha256.hex rawBytes) do
    throwError "quantum complete source identity/telescope differs"
  let snapshot ← TemplateBinding.exportSnapshot
  let records := snapshot.originals.filter (·.occurrence.key.registrationModule == owner)
  unless records.size == 1 && records.all (·.occurrence.key.theoremName == name) do
    throwError "quantum registration inventory differs from the exact original"
  let wire := (Json.arr (← TemplateBinding.reportJson
    #[(owner, records.map (·.occurrence.key))])).compress
  let row := Json.mkObj [
    ("source_name", toJson name), ("source_owner", toJson sourceOwner),
    ("registration_owner", toJson owner), ("source_sha256", toJson hash),
    ("source_bytes", toJson source.size), ("state", toJson "declared_validated"),
    ("evidence_ref", toJson cert.evidenceRef), ("internal_heartbeats", toJson heartbeats),
    ("milliseconds", toJson elapsed), ("raw_visits", toJson visits),
    ("structural_unique", toJson unique.size), ("raw_depth", toJson depth),
    ("raw_identity_work", toJson rawWork), ("raw_identity_bytes", toJson rawBytes.size),
    ("source_binding", binding), ("axioms", toJson axioms),
    ("registration_source_identity", toJson event.registrationSourceIdentity)]
  let artifactPrefix := if isCurrent then "quantum-current" else "quantum-historical"
  IO.FS.writeFile ((← Repository.root) / s!".lake/build/{artifactPrefix}-evidence.json") (wire ++ "\n")
  IO.FS.writeFile ((← Repository.root) / s!".lake/build/{artifactPrefix}-measurements.json") (row.pretty ++ "\n")
  logInfo m!"SOURCE_ASSESSMENT {row.compress}"
  let fixture := if isCurrent then CompiledQuantumWire.canonical else CompiledQuantumHistoricalWire.canonical
  unless wire == fixture do throwError "quantum compiled fixture differs from actual export"
  let readouts ← IO.ofExcept (binding.getObjValAs? (Array Json) "readouts")
  let path ← IO.ofExcept (readouts[0]!.getObjValAs? (Array String) "path")
  let ((context, term), _) ← (SourceScope.atPath info.type path).run 524288
  unless context.size == 10 &&
      term.isAppOfArity ``D5.S3.Quantum.Information.ActualQubitChordObstruction.jointObservation 1 &&
      term.appArg! == mkBVar 6 do
    throwError "quantum selector no longer selects the actual channel observation"
  for bad in #[mkConst name, info.type,
      mkApp (.lam `P (mkSort .zero) (.bvar 0) .default) info.type,
      mkApp (.lam `P (mkSort .zero) (mkConst ``Unit.unit) .default) info.type,
      mkApp (mkConst ``Decidable) info.type] do
    let reason ← try
      discard <| SourceOperands.check name #[bad] 524288
      pure "accepted"
    catch ex => ex.toMessageData.toString
    unless reason.startsWith "forbidden_dependency:" do
      throwError "target/proof/decision/dead-argument rejection failed: {reason}"
  logInfo "[PASS] quantum_exact_original_owner_complete_four_slots_uncached"
  logInfo "[PASS] noncomputable_unit_actual_data_selection_target_alias_and_dead_argument_rejection"

end LeanInformationAuditRegTests.QuantumSourceContract
