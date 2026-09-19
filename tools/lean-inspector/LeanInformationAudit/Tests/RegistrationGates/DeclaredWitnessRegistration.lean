import D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord
import LeanInformationAudit.Tests.RegistrationGates.EscapeRecords
import LeanInformationAudit.Tests.SourceIsolation

namespace LeanInformationAudit.Tests.DeclaredWitnessRegistration
open Lean Meta Elab Command
open D5.S3.ConceptDynamics.InformationEscape CounterexampleRecord

def claim : Prop := ∀ n : Nat, n ≠ 0 ∧ ∀ b : Bool, b = b
theorem result : ¬ claim := fun h => (h 0).1 rfl
theorem literalResult : ¬ ∀ n : Nat, n ≠ 0 ∧ ∀ b : Bool, b = b := result
def predicate (n : Nat) : Prop := n ≠ 0 ∧ ∀ b : Bool, b = b
def embedding : Fin 1 → Nat := fun _ => 0
def decision : ∀ w : Fin 1, Decidable (predicate (embedding w)) :=
  fun _ => .isFalse (fun h => h.1 rfl)
def arena := WitnessArena.ofCarrier (Fin 1) Nat
  predicate embedding decision
def reads := counterexampleRealization (fun _ : Fin 1 => false)
theorem law : arena.Law reads := ⟨(0 : Fin 1), rfl⟩
theorem bridge : WitnessPrimitiveRealization arena (¬ claim) reads := ⟨arena.law_refutes⟩
def definitionBridge : WitnessPrimitiveRealization arena (¬ claim) reads := bridge
theorem unnamedClaimBridge : WitnessPrimitiveRealization arena
    (¬ ∀ n : Nat, n ≠ 0 ∧ ∀ b : Bool, b = b) reads := ⟨arena.law_refutes⟩
theorem variation : arena.Law reads ∧ ¬ arena.Law arena.constantTrue := arena.variation law
theorem sensitivity : FiniteSlotSensitivity arena.toPrimitiveLawArena := arena.sensitivity law

-- Same universal and an actual false readout, but the embedded predicate is true.
def wrongCheckArena := WitnessArena.ofCarrier (Fin 1) Nat
  (fun n => n ≠ 0 ∧ ∀ b : Bool, b = b) (fun _ => 1)
  (fun _ => .isTrue ⟨by decide, fun _ => rfl⟩)
theorem wrongCheckBridge : WitnessPrimitiveRealization wrongCheckArena (¬ claim) reads :=
  ⟨fun _ => result⟩
theorem wrongCheckLaw : wrongCheckArena.Law reads := ⟨(0 : Fin 1), rfl⟩
theorem wrongCheckVariation : wrongCheckArena.Law reads ∧
    ¬ wrongCheckArena.Law wrongCheckArena.constantTrue := wrongCheckArena.variation wrongCheckLaw
theorem wrongCheckSensitivity : FiniteSlotSensitivity wrongCheckArena.toPrimitiveLawArena :=
  wrongCheckArena.sensitivity wrongCheckLaw

def mismatchedArena := WitnessArena.ofCarrier (Fin 1) Nat (fun _ => False)
  (fun _ => 0) (fun _ => .isFalse id)
theorem mismatchedBridge : WitnessPrimitiveRealization mismatchedArena (¬ claim) reads :=
  ⟨fun _ => result⟩
theorem missingPositive : True ∧ ¬ arena.Law arena.constantTrue := ⟨trivial, variation.2⟩
theorem missingNegative : arena.Law reads ∧ True := ⟨law, trivial⟩
-- The empty anchor function can differ while Law ignores it. Checking only the
-- whole pair's proposition would silently accept this unselected realization.
def unselectedReads : PrimitiveRealization arena.signature :=
  { readout := reads.readout, anchor := fun _ => (0 : Fin 1) }
theorem unselectedPositive : arena.Law unselectedReads ∧ ¬ arena.Law arena.constantTrue :=
  ⟨law, variation.2⟩
theorem vacuousBridge : WitnessPrimitiveRealization arena (¬ claim) arena.constantTrue :=
  ⟨fun _ => result⟩

-- Two aliases require two unfoldings: occurrence must stop after the first.
def hiddenClaim : Prop := claim
theorem hiddenResult : ¬ hiddenClaim := result
theorem hiddenBridge : WitnessPrimitiveRealization arena (¬ hiddenClaim) reads := ⟨arena.law_refutes⟩
def fakeClaim : Prop := ¬ True
theorem fakeResult : ¬ fakeClaim := fun h => h trivial
def fakeArena := WitnessArena.ofCarrier (Fin 1) Nat (fun _ => ¬ True)
  (fun _ => 0) (fun _ => .isFalse fakeResult)
theorem fakeBridge : WitnessPrimitiveRealization fakeArena (¬ fakeClaim) reads := ⟨fun _ => fakeResult⟩
-- This universal wrapper is structurally valid. Published-assertion fidelity
-- remains the existing SL-031 pre-registration review obligation.
def wrappedClaim : Prop := ∀ _ : Nat, ¬ True
theorem wrappedResult : ¬ wrappedClaim := fun h => h 0 trivial
theorem wrappedBridge : WitnessPrimitiveRealization fakeArena (¬ wrappedClaim) reads :=
  ⟨fakeArena.law_refutes⟩
theorem fakeLaw : fakeArena.Law reads := ⟨(0 : Fin 1), rfl⟩
theorem fakeVariation : fakeArena.Law reads ∧ ¬ fakeArena.Law fakeArena.constantTrue :=
  fakeArena.variation fakeLaw
theorem fakeSensitivity : FiniteSlotSensitivity fakeArena.toPrimitiveLawArena := fakeArena.sensitivity fakeLaw

elab "observe_declared_witness" : command => do
  let start (theoremName arenaName bridgeName : String) :=
    s!"register_information_theorem {theoremName} in {arenaName} " ++
    "readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false)) " ++
    s!"primitives reads.toPrimitiveBundle realization {bridgeName} "
  let tail := " escape from (Nat) escape continues (open)"
  let evidence := "variation variation sensitivity sensitivity"
  let normal := start "result" "arena" "bridge"
  let cases : Array (String × String × Option String) := #[
    ("named", normal ++ evidence ++ tail, none),
    ("literal", start "literalResult" "arena" "bridge" ++ evidence ++ tail, none),
    ("wrong_bridge", start "result" "arena" "result" ++ evidence ++ tail,
      some "IE-C006"),
    ("bridge_not_theorem", start "result" "arena" "definitionBridge" ++ evidence ++ tail,
      some "IE-C006"),
    ("bridge_arena", start "result" "wrongCheckArena" "bridge" ++ evidence ++ tail,
      some "IE-C006"),
    ("named_claim_required", start "result" "arena" "unnamedClaimBridge" ++ evidence ++ tail,
      some "dtr.witness_statement_identity"),
    ("missing_bridge", "register_information_theorem result in arena " ++
      "readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false)) " ++
      "primitives reads.toPrimitiveBundle" ++ tail, some "parse"),
    ("wrong_origin", normal ++ evidence ++ " escape from (Bool) escape continues (open)",
      some "dtr.escape_from_state"),
    ("absent_origin", normal ++ evidence ++ " escape from (Int) escape continues (open)",
      some "dtr.escape_from_absent"),
    ("one_step_only", start "hiddenResult" "arena" "hiddenBridge" ++ evidence ++ tail,
      some "dtr.escape_from_absent"),
    ("statement_identity", start "result" "mismatchedArena" "mismatchedBridge" ++ evidence ++ tail,
      some "dtr.witness_statement_identity"),
    ("readout_tie", start "result" "wrongCheckArena" "wrongCheckBridge" ++
      "variation wrongCheckVariation sensitivity wrongCheckSensitivity" ++ tail,
      some "dtr.witness_readout_tie"),
    ("missing_variation", normal ++ "sensitivity sensitivity" ++ tail,
      some "dtr.witness_bridge_requires_positive_variation"),
    ("positive_variation", normal ++ "variation missingPositive sensitivity sensitivity" ++ tail,
      some "dtr.witness_bridge_requires_positive_variation"),
    ("selected_positive", normal ++ "variation unselectedPositive sensitivity sensitivity" ++ tail,
      some "dtr.witness_bridge_requires_positive_variation"),
    ("negative_variation", normal ++ "variation missingNegative sensitivity sensitivity" ++ tail,
      some "dtr.witness_bridge_requires_negative_variation"),
    ("missing_sensitivity", normal ++ "variation variation" ++ tail,
      some "dtr.witness_bridge_requires_sensitivity"),
    ("wrong_sensitivity", normal ++ "variation variation sensitivity RegistrationPositive.slotSensitivity" ++ tail,
      some "dtr.witness_bridge_requires_sensitivity"),
    ("fake_negation", start "fakeResult" "fakeArena" "fakeBridge" ++
      "variation fakeVariation sensitivity fakeSensitivity" ++ tail,
      some "dtr.witness_statement_identity"),
    ("wrapped_review_boundary", start "wrappedResult" "fakeArena" "wrappedBridge" ++
      "variation fakeVariation sensitivity fakeSensitivity" ++ tail, none)]
  for (label, source, expected) in cases do
    let saved ← get
    modify fun s => { s with messages := {} }
    let mut failure := ""
    match Parser.runParserCategory (← getEnv) `command source with
    | .error message => failure := "parse: " ++ message
    | .ok command =>
      try elabCommand command catch error => failure := ← error.toMessageData.toString
    let env ← getEnv
    let row := (TemplateBinding.records env).find? fun row =>
      row.occurrence.key.registrationModule == env.header.mainModule
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
        let inputsOk := match row.result with
          | .declaredValidated certificate =>
            certificate.extractionInputs.any (·.name == ``claim) ||
              label == "wrapped_review_boundary"
          | _ => false
        let raw := (env.find? row.occurrence.key.theoremName).get!.type
        pure <| wire.getObjValAs? String "bridge_kind" == .ok "witness" &&
          row.escape.fromObject.any (·.name == ``Nat) && inputsOk && row.occurrence.statement.equal raw
    let ok := match expected with
      | none => validated && failure.isEmpty && metadataOk
      | some diagnostic => !validated && (failure.splitOn diagnostic).length > 1
    set saved
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] witness_{label} validated={validated} actual={failure}"

observe_declared_witness

namespace AuthorExample
-- Requires CounterexampleRecord and the existing closed claim/result in scope.
private def witnessArena := WitnessArena.ofCarrier (Fin 1) Nat
  (fun n => n ≠ 0 ∧ ∀ b : Bool, b = b) (fun _ => 0) (fun _ => .isFalse (fun h => h.1 rfl))
private def witnessReads := counterexampleRealization (fun _ : Fin 1 => false)
private theorem witnessLaw : witnessArena.Law witnessReads := ⟨(0 : Fin 1), rfl⟩
private theorem witnessBridge : WitnessPrimitiveRealization witnessArena (¬ claim) witnessReads := ⟨witnessArena.law_refutes⟩
private theorem witnessVariation : witnessArena.Law witnessReads ∧ ¬ witnessArena.Law witnessArena.constantTrue := witnessArena.variation witnessLaw
private theorem witnessSensitivity : FiniteSlotSensitivity witnessArena.toPrimitiveLawArena := witnessArena.sensitivity witnessLaw
register_information_theorem result in witnessArena
  readout via (@counterexampleRealization (Fin 1) (fun _ : Fin 1 => false))
  primitives witnessReads.toPrimitiveBundle realization witnessBridge
  variation witnessVariation sensitivity witnessSensitivity
  escape from (Nat) escape continues (open)
end AuthorExample

run_meta LeanInformationAudit.Tests.withPrivateSources do
  let records ← TemplateBinding.assessJoined
  let some record := records.find? (·.occurrence.key.theoremName == ``result)
    | throwError "missing author example"
  let .declaredValidated certificate := record.result | throwError "author example was not validated"
  unless certificate.extractionInputs.any (·.name == ``claim) do throwError "claim omitted from evidence"
  let primed ← getEnv
  let assessments (env : Environment) := ((TemplateBinding.observedAssessments env).filter
    (·.theoremName == ``result)).size
  let before := assessments primed
  discard <| TemplateBinding.assessJoined
  unless assessments (← getEnv) == before do throwError "cache not reused"
  logInfo "[PASS] witness_author_example_and_cache_reuse"
  let path := TemplateAudit.sourcePath primed.header.mainModule
  let original ← IO.FS.readFile path
  for (label, oldText, newText) in #[("claim", "def claim : Prop", "def claim  : Prop"),
      ("predicate", "(fun n => n ≠ 0", "(fun n =>  n ≠ 0"),
      ("embedding", "(fun _ => 0)", "(fun _ =>  0)"),
      ("decision", ".isFalse (fun h =>", ".isFalse (fun h  =>")] do
    setEnv primed
    let changed := original.replace oldText newText
    unless changed != original do throwError "source mutation did not change {label}"
    try
      IO.FS.writeFile path changed
      let rejected ← try
        let rows ← TemplateBinding.assessJoined
        pure <| rows.any fun row => row.occurrence.key.theoremName == ``result &&
          (row.result matches .declaredUnresolved _)
      catch _ => pure true
      unless rejected do throwError "stale {label} accepted"
      logInfo m!"[PASS] witness_stale_{label}_bytes_rejected"
    finally IO.FS.writeFile path original
  setEnv primed

end LeanInformationAudit.Tests.DeclaredWitnessRegistration
