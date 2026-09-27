import Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCore
import Reg.D5.S1.Words.Patterns.CyclicStackPreimages
import Reg.D5.S1.Words.Patterns.CyclicStackPreimagesCandidates
import Reg.D5.S1.Words.Patterns.CyclicStackPreimagesFinalLow
import Reg.D5.S1.Words.Patterns.CyclicStackPreimagesInvariants
import LeanInformationAuditRegTests.CyclicSourceInventory
import LeanInformationAuditRegTests.CompiledCyclicWire

open Lean Meta LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.ConceptDynamics.InformationEscape.CyclicStackFamily

namespace LeanInformationAuditRegTests.CyclicSourceContract

set_option trace.InformationRegistration.check true

run_meta do
  let inventory ← IO.ofExcept (Json.parse CyclicSourceInventory.canonical)
  let sources ← IO.ofExcept (inventory.getObjValAs? (Array Json) "sources")
  let retired ← IO.ofExcept (inventory.getObjValAs? (Array String) "retired_names")
  let mut originals : Array (Name × Name) := #[]
  let mut modules : Array Name := #[]
  let mut measurements := #[]
  for source in sources do
    let path ← IO.ofExcept (source.getObjValAs? String "path")
    let hash ← IO.ofExcept (source.getObjValAs? String "sha256")
    let bytes ← IO.FS.readBinFile ((← Repository.root) / path)
    unless Sha256.hex bytes == hash do throwError "original source bytes changed: {path}"
    let owner := (← IO.ofExcept (source.getObjValAs? String "expected_reg_owner")).toName
    let sourceOwner := (path.dropEnd 5 |>.toString.replace "/" ".").toName
    modules := modules.push owner
    let names ← IO.ofExcept (source.getObjValAs? (Array String) "expected_original_declarations")
    for name in names do
      let name := name.toName
      originals := originals.push (name, owner)
      unless (← getConstInfo name).isTheorem &&
          RegistrationReifier.declaringModuleOf (← getEnv) name == some sourceOwner do
        throwError "original theorem owner differs: {name}"
      let env ← getEnv
      let #[event] := (TemplateBinding.inventory env).filter (·.key.theoremName == name)
        | throwError "original must have exactly one source registration: {name}"
      unless event.key.registrationModule == owner do throwError "wrong Reg owner: {name}"
      let some (_, claim) := (TemplateBinding.ownedClaims env).find? (·.2.key == event.key)
        | throwError "original source claim missing: {name}"
      let before := (TemplateBinding.observedAssessments env).size
      logInfo m!"SOURCE_ASSESSMENT_START {name}"
      let start ← IO.monoMsNow
      let heartbeats ← IO.getNumHeartbeats
      let record ← TemplateBinding.assess event (some claim)
      let heartbeats := (← IO.getNumHeartbeats) - heartbeats
      let elapsed := (← IO.monoMsNow) - start
      unless (TemplateBinding.observedAssessments (← getEnv)).size == before + 1 do
        throwError "source assessment used cached result: {name}"
      let .declaredValidated cert := record.result
        | throwError "original source failed: {(← TemplateBinding.recordJson record).compress}"
      unless cert.sourceBinding.isSome && record.escape.fromObject.isSome &&
          record.escape.bridgeKind == "source-equivalence" &&
          record.escape.continuation.any (·.kind == "open") do
        throwError "incomplete source four slots: {name}"
      let row := Json.mkObj [
        ("source_name", toJson name), ("source_owner", toJson sourceOwner),
        ("registration_owner", toJson owner), ("source_sha256", toJson hash),
        ("state", toJson "declared_validated"), ("evidence_ref", toJson cert.evidenceRef),
        ("internal_heartbeats", toJson heartbeats), ("milliseconds", toJson elapsed),
        ("source_binding", cert.sourceBinding.get!),
        ("registration_source_identity", toJson event.registrationSourceIdentity)]
      measurements := measurements.push row
      logInfo m!"SOURCE_ASSESSMENT {row.compress}"
  unless originals.size == 26 do throwError "incorrect live original inventory"
  let snapshot ← TemplateBinding.exportSnapshot
  let records := snapshot.originals.filter (fun r => modules.contains r.occurrence.key.registrationModule)
  unless records.size == originals.size && records.all (fun r =>
      originals.contains (r.occurrence.key.theoremName, r.occurrence.key.registrationModule)) do
    throwError "live source registrations differ from exact name/owner inventory"
  for name in retired do
    unless !(← getEnv).contains name.toName &&
        !(TemplateBinding.inventory (← getEnv)).any (·.key.theoremName == name.toName) do
      throwError "retired wrapper restored: {name}"
  let selection := modules.map fun owner =>
    (owner, records.filter (·.occurrence.key.registrationModule == owner) |>.map (·.occurrence.key))
  let wire := (Json.arr (← TemplateBinding.reportJson selection)).compress
  IO.FS.writeFile ((← Repository.root) / ".lake/build/cyclic-family-evidence.json") (wire ++ "\n")
  IO.FS.writeFile ((← Repository.root) / ".lake/build/cyclic-family-measurements.json")
    ((Json.arr measurements).pretty ++ "\n")
  unless wire == CompiledCyclicWire.canonical do
    throwError "compiled Cyclic fixture differs from actual source export"
  logInfo "[PASS] all_26_exact_original_names_owners_four_slots_uncached_retired_absent"

example : ¬ ObservationalDependence signature rejected := by
  intro h
  obtain ⟨p, x, y, hxy⟩ := h ()
  exact hxy rfl

unsafe def unsafeIdentity (x : Nat) : Nat := x
@[implemented_by unsafeIdentity] def redirected (x : Nat) : Nat := x

structure HiddenDecision where
  whole : Decidable (∀ input stack,
    _root_.D5.S1.Words.Patterns.CyclicStackPreimages.process input stack =
      (_root_.D5.S1.Words.Patterns.CyclicStackPreimages.run input stack).1 ++
        (_root_.D5.S1.Words.Patterns.CyclicStackPreimages.run input stack).2)

run_meta do
  for name in #[``unsafeIdentity, ``redirected] do
    let rejected ← try
      discard <| SourceOperands.check
        ``D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run #[mkConst name] 524288
      pure false
    catch _ => pure true
    unless rejected do throwError "unsafe/external identity accepted"
  let discarded := mkApp (.lam `carrier (mkSort (.succ .zero))
    (mkConst ``Unit.unit) .default) (mkConst ``HiddenDecision)
  let rejected ← try
    discard <| SourceOperands.check
      ``D5.S1.Words.Patterns.CyclicStackPreimages.process_eq_run #[discarded] 524288
    pure false
  catch _ => pure true
  unless rejected do throwError "target decision hidden in discarded carrier accepted"
  logInfo "[PASS] target_decision_in_discarded_inductive_field"
  let expected ← mkAppM ``Sensitivity #[mkConst ``runArena, mkConst ``actual]
  unless !(← RegistrationGates.checked .anonymous expected) &&
      !(← RegistrationGates.checked ``True.intro expected) do
    throwError "absent or unrelated sensitivity accepted"
  logInfo "[PASS] dead_constant_readout_absent_unrelated_sensitivity_unsafe_external"

end LeanInformationAuditRegTests.CyclicSourceContract
