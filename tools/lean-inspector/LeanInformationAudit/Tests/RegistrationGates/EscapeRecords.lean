import LeanInformationAudit.Tests.RegistrationGates.Positive
import D5.S3.ConceptDynamics.InformationEscape.RegistrationTemplates
import D5.S3.ConceptDynamics.InformationEscape.EscapeRecord

namespace LeanInformationAudit.Tests.EscapeRecords
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape EscapeRecord RegistrationTemplates
open D5.S3.ConceptDynamics.CIRPT
open RegistrationPositive

local instance : DecidableEq arena.State := instDecidableEqBool
local instance : DecidableEq (Arena.ofFintype (Fin 2)).State := inferInstanceAs (DecidableEq (Fin 2))

def emptyChain : LayerChain arena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun x : Bool => x)
  refines := fun r => Fin.elim0 r

def residualChain : LayerChain arena.toArena where
  length := 0
  kernel := fun _ => cutKernel (fun _ : Bool => false)
  refines := fun r => Fin.elim0 r

def otherChain : LayerChain (Arena.ofFintype (Fin 2)) where
  length := 0
  kernel := fun _ => cutKernel (fun _ : Fin 2 => false)
  refines := fun r => Fin.elim0 r

theorem emptyProof : EscapeResidualEmpty emptyChain := by
  change emptyChain.unresolvedCount = 0
  decide +kernel
def otherResidual : EscapeResidualWitness otherChain := ⟨(0 : Fin 2), (1 : Fin 2), by decide +kernel⟩
def residual : EscapeResidualWitness residualChain := ⟨false, true, by decide +kernel⟩

def reads : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun x : Bool => x)

theorem statement : ∀ x : Bool, x = x := fun _ => rfl
theorem legacy : LegacyPrimitiveRealization arena (∀ x : Bool, x = x) reads :=
  ⟨⟨fun _ => rfl, fun _ => statement⟩⟩
theorem forward : EscapePrimitiveRealization arena (∀ x : Bool, x = x) reads := ⟨fun _ => rfl⟩

register_information_template cutRealization

/-- Runtime parsing keeps missing grammar and deliberately broken gates as named
test failures, with a separately compiled oracle. Every case rolls back. -/
elab "observe_escape_records" : command => do
  let commandStart := "register_information_theorem statement in arena " ++
    "readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)) " ++
    "primitives reads.toPrimitiveBundle realization "
  let cases : Array (String × String × Option String) := #[
    ("escape_legacy_empty_validated", commandStart ++ "legacy variation lawVariation sensitivity slotSensitivity " ++
      "escape from (Bool) escape continues (emptyProof)", none),
    ("escape_forward_witness_validated", commandStart ++ "forward variation lawVariation sensitivity slotSensitivity " ++
      "escape from (Bool) escape continues (residual)", none),
    ("escape_forward_requires_sensitivity", commandStart ++ "forward variation lawVariation " ++
      "escape from (Bool) escape continues (residual)", some "dtr.forward_bridge_requires_sensitivity"),
    ("escape_from_absent_rejected", commandStart ++ "legacy variation lawVariation sensitivity slotSensitivity " ++
      "escape from (Nat) escape continues (emptyProof)", some "dtr.escape_from_absent"),
    ("escape_wrong_chain_rejected", commandStart ++ "legacy variation lawVariation sensitivity slotSensitivity " ++
      "escape from (Bool) escape continues (otherResidual)", some "dtr.escape_continues_arena"),
    ("escape_open_validated", commandStart ++ "legacy variation lawVariation sensitivity slotSensitivity " ++
      "escape from (Bool) escape continues (open)", none)]
  for (label, source, expected) in cases do
    let saved ← get
    modify fun s => { s with messages := {} }
    let mut failure := ""
    match Parser.runParserCategory (← getEnv) `command source with
    | .error message => failure := "parse: " ++ message
    | .ok command =>
      try elabCommand command catch error => failure := ← error.toMessageData.toString
    let records := TemplateBinding.records (← getEnv)
    let row := records.find? (·.occurrence.key.theoremName == ``statement)
    let validated := row.any fun row => match row.result with
      | .declaredValidated _ => true | _ => false
    if let some row := row then
      if let .declaredUnresolved diagnostic := row.result then failure := failure ++ diagnostic
    for message in (← get).messages.toList do
      if message.severity == .error then failure := failure ++ (← message.data.toString)
    let metadataOk ← match row with
      | none => pure false
      | some row =>
        let wire ← liftTermElabM <| TemplateBinding.recordJson row
        let kind := if label == "escape_forward_witness_validated" then "forward" else "legacy"
        let residualKind := if label == "escape_open_validated" then "open"
          else if label == "escape_forward_witness_validated" then "witness" else "empty"
        let originOk := row.escape.fromObject.any fun origin => origin.name == ``Bool &&
          origin.typeIdentity.length == 64 && origin.objectIdentity.length == 64
        let residualOk := row.escape.continuation.any fun residual => residual.kind == residualKind &&
          (residualKind == "open" || (residual.declarationName.isSome &&
            residual.statementIdentity.any (·.length == 64) && residual.chainName.isSome))
        let hashesOk := match row.result with
          | .declaredValidated certificate => Id.run do
            let changedFrom := { row.escape with fromObject := none }
            let changedResidual := { row.escape with continuation := none }
            let changedBridge := { row.escape with
              bridgeKind := if kind == "legacy" then "forward" else "legacy" }
            return #[changedFrom, changedResidual, changedBridge].all fun escape =>
              match TemplateAudit.bindingIdentity row.occurrence.statementIdentity
                  { certificate with escape } 524288 with
              | .ok (identity, _) => identity != certificate.evidenceRef
              | _ => false
          | _ => false
        pure <| originOk && residualOk && hashesOk &&
          wire.getObjValAs? String "bridge_kind" == .ok kind
    let ok := match expected with
      | none => validated && failure.isEmpty && metadataOk
      | some diagnostic => !validated && (failure.splitOn diagnostic).length > 1
    set saved
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label} actual={failure}"

observe_escape_records


def nativeArena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x

local instance : DecidableEq nativeArena.State := instDecidableEqBool

elab "observe_escape_record_routes" : command => do
  let descriptor := "readout via (@cutRealization Bool Bool instDecidableEqBool (fun x : Bool => x)) "
  let slots := "escape from (Bool) escape continues (emptyProof)"
  let cases := #[
    ("escape_native_route", #["information_theorem native in nativeArena " ++ descriptor ++
      "primitives reads " ++ slots ++ " : ∀ x : Bool, x = x := fun _ => rfl"]),
    ("escape_occurrence_route", #["register_information_theorem statement in arena " ++
      "object_arena objectArena catalog complete " ++ descriptor ++
      "primitives reads.toPrimitiveBundle realization forward " ++
      "variation lawVariation sensitivity slotSensitivity " ++ slots]),
    ("escape_sidecar_route", #["register_information_theorem statement in arena " ++
      "primitives reads.toPrimitiveBundle realization legacy " ++
      "variation lawVariation sensitivity slotSensitivity",
      "declare_information_template_binding statement in arena " ++ descriptor ++ slots])]
  for (label, commands) in cases do
    let saved ← get
    modify fun state => { state with messages := {} }
    let mut ok := true
    for source in commands do
      match Parser.runParserCategory (← getEnv) `command source with
      | .error message => ok := false; logInfo message
      | .ok command =>
        try elabCommand command catch error => ok := false; logInfo error.toMessageData
    let rows ← liftTermElabM TemplateBinding.assessJoined
    let moduleName := (← getEnv).header.mainModule
    ok := ok && !(← get).messages.hasErrors && rows.any fun row =>
      row.occurrence.key.registrationModule == moduleName &&
      row.escape.fromObject.isSome && row.escape.continuation.isSome &&
      (match row.result with | .declaredValidated _ => true | _ => false)
    let messages ← (← get).messages.toList.mapM (fun message => message.data.toString)
    let diagnostics := rows.map fun row => match row.result with
      | .declaredUnresolved message => message | _ => ""
    set saved
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
    unless ok do logInfo m!"messages={messages} bindings={diagnostics}"

observe_escape_record_routes

end LeanInformationAudit.Tests.EscapeRecords
