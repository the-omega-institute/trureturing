import LeanInformationAudit.CensusSchema
import LeanInformationAudit.Sha256
import LeanInformationAudit.Census.Codec
import Std.Internal.Parsec.ByteArray

namespace LeanInformationAudit

open Lean

namespace DispositionCensus

/-- Cache each display name once instead of rebuilding it in every comparison.
The ordering is exactly StatementKey.lt, including its wire-id tie breaker. -/
private def sortKeys (keys : Array StatementKey) : Array StatementKey :=
  ((keys.map fun key => (key.theoremName.toString, key)).qsort fun a b =>
    a.1 < b.1 || (a.1 == b.1 && a.2.statementId < b.2.statementId)).map (·.2)

def checkFrozenUniqueness (head : String) (keys : Array StatementKey) : Except String Unit := do
  let mut ids : Std.HashSet String := {}
  for key in keys do
    if ids.contains key.statementId then
      throw <| censusError head "frozen_keys" "unique" (toJson key).compress
    ids := ids.insert key.statementId

def checkStatementIds (keys : Array StatementKey) : Except String Unit := do
  for key in keys do discard <| decodeStatementId key.theoremName key.statementId

def checkFrozenKeys (head : String) (keys : Array StatementKey) : Except String Unit := do
  checkFrozenUniqueness head keys
  checkStatementIds keys

def checkInventoryDuplicates (rows : Array StatementKey) : Except String Unit := do
  let mut records : Std.HashMap String (Array Nat) := {}
  for i in [:rows.size] do
    let id := rows[i]!.statementId
    records := records.insert id ((records.getD id #[]).push i)
  for key in rows do
    let duplicates := records.getD key.statementId #[]
    if duplicates.size > 1 then
      throw s!"IE-C035 DuplicateAnalysisDisposition theorem={key.theoremName} statement_id={key.statementId} records={(toJson duplicates).compress}"

/-- All callers share IE-C044 > IE-C035 > IE-C036. Report parsing must
defer the codec until inventory duplicates have had their turn. -/
def checkIdentityInputs (head : String) (frozen rows : Array StatementKey) : Except String Unit := do
  checkFrozenUniqueness head frozen
  checkInventoryDuplicates rows
  checkStatementIds frozen
  checkStatementIds rows

/-- Identity binding only; absence is checked after the manifest's Nat binding. -/
def checkKeyIdentity (head : String) (frozen : Array StatementKey)
    (inventoryHead : String) (rows : Array StatementKey) : Except String Unit := do
  let expected := sortKeys frozen
  for key in expected do
    unless inventoryHead == head do
      throw <| identityError key.theoremName "head" head inventoryHead
  unless inventoryHead == head do
    throw <| identityError .anonymous "head" head inventoryHead
  let names : Std.HashMap Name String :=
    expected.foldl (init := {}) fun result key =>
      if result.contains key.theoremName then result else result.insert key.theoremName key.statementId
  let idNames : Std.HashMap String Name :=
    expected.foldl (init := {}) fun result key => result.insert key.statementId key.theoremName
  for key in sortKeys rows do
    match names[key.theoremName]? with
    | some firstId =>
      unless idNames[key.statementId]? == some key.theoremName do
        throw <| identityError key.theoremName "statement_id" firstId key.statementId
    | none =>
      let expectedName := idNames[key.statementId]?.map Name.toString |>.getD "absent"
      throw <| identityError key.theoremName "theorem_name" expectedName key.theoremName.toString

def checkMissingKeys (head : String) (frozen rows : Array StatementKey) : Except String Unit := do
  let records := rows.foldl (init := ({} : Std.HashSet String)) fun ids row => ids.insert row.statementId
  for key in sortKeys frozen do
    unless records.contains key.statementId do
      throw s!"IE-C034 MissingAnalysisDisposition theorem={key.theoremName} statement_id={key.statementId} head={head}"

/-- IE-C034 is last, after every identity obligation supplied by this API. -/
def checkKeyCoverage (head : String) (frozen : Array StatementKey)
    (inventoryHead : String) (rows : Array StatementKey) : Except String Unit := do
  checkIdentityInputs head frozen rows
  checkKeyIdentity head frozen inventoryHead rows
  checkMissingKeys head frozen rows

def checkCoverage (head : String) (frozen : Array StatementKey)
    (inventory : DispositionInventory) : Except String Unit :=
  checkKeyCoverage head frozen inventory.headSha (inventory.entries.map (·.1))

/-- An immutable report already restricted to frozen elaborated theorem declarations.
The producer owns frozen membership; source provenance checks do not discover members. -/
structure FrozenReport where
  headSha : String
  reportSha256 : String
  theorems : Array StatementKey

/-- The supported wire identity, also used by synthetic producer fixtures. -/
def truthExportIdentity : Json := Json.mkObj [
  ("schema", toJson "stratalint.truth-export"), ("schema_version", toJson (2 : Nat)),
  ("dialect", toJson "stratalint.truth-export.v2"), ("producer", toJson "TruthExportCommand")]

/-- Consume the truth export dialect currently emitted by TruthExportCommand.
source_commit binds HEAD; declaration_name_key preserves Lean Name structure;
statement_id is read verbatim. Only frozen nodes' theorem declarations are included.
The caller pins the report bytes independently with expectedSha256. -/
private def parseReportCore (json : Json) (actualSha256 : String) : Except String FrozenReport := do
  let expectedHead := (json.getObjValAs? String "source_commit").toOption.getD "unknown"
  for field in ["schema", "dialect", "producer"] do
    let expected ← truthExportIdentity.getObjValAs? String field
    unless (← stringField json field) == expected do
      throw <| censusError expectedHead field expected (← stringField json field)
  let version ← truthExportIdentity.getObjValAs? Nat "schema_version"
  unless (← json.getObjValAs? Nat "schema_version") == version do
    throw <| censusError expectedHead "schema_version" (toString version)
      (toString (← json.getObjValAs? Nat "schema_version"))
  let head ← stringField json "source_commit"
  let modules ← json.getObjValAs? (Array Json) "nodes"
  let mut keys : Array StatementKey := #[]
  for moduleRow in modules do
    let freezeStatus ← match moduleRow.getObjValAs? String "freeze_status" with
      | .ok status => pure status
      | .error _ =>
        throw <| censusError head "freeze_status"
          "frozen|proven-not-yet-frozen" "missing-or-invalid"
    unless freezeStatus == "frozen" || freezeStatus == "proven-not-yet-frozen" do
      throw <| censusError head "freeze_status" "frozen|proven-not-yet-frozen" freezeStatus
    if freezeStatus != "frozen" then continue
    let declarations ← moduleRow.getObjValAs? (Array Json) "declarations"
    for declaration in declarations do
      if (← stringField declaration "kind") == "theorem" then
        keys := keys.push ⟨← parseNameKey (← stringField declaration "declaration_name_key"),
          ← stringField declaration "statement_id"⟩
  let sorted := sortKeys keys
  checkFrozenUniqueness head sorted
  return { headSha := head, reportSha256 := actualSha256, theorems := sorted }

def parseReportJson (json : Json) (sha256 : String) : Except String FrozenReport := do
  let report ← parseReportCore json sha256
  checkFrozenKeys report.headSha report.theorems
  return report

private def parseReportHashed (bytes sha256 : String) : Except String FrozenReport :=
  ((Json.parse bytes) >>= fun json => parseReportCore json sha256).mapError fun error =>
    if error.startsWith "IE-" then error else censusError "unknown" "report" "well-formed" error

def parseReportData (bytes : String) : Except String FrozenReport :=
  parseReportHashed bytes ("sha256:" ++ Sha256.hex bytes.toUTF8)

/-- Hash the exact bytes passed to the Lean parser, through the host SHA-256
implementation. Piping those bytes avoids a second path read and its race.
Only hashing crosses this boundary: frozen membership and keys are parsed here. -/
def parseReportDataIO (bytes : String) : IO FrozenReport := do
  let result ← IO.Process.output { cmd := "/usr/bin/shasum", args := #["-a", "256"] } (some bytes)
  unless result.exitCode == 0 do throw <| IO.userError "census report: SHA-256 failed"
  let hash := (result.stdout.take 64).toString
  unless hash.length == 64 && hash.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) do
    throw <| IO.userError "census report: invalid SHA-256 output"
  IO.ofExcept <| parseReportHashed bytes ("sha256:" ++ hash)

def checkReportBinding (expectedHead expectedSha256 : String) (report : FrozenReport) :
    Except String Unit := do
  unless report.headSha == expectedHead do
    throw <| identityError .anonymous "head" expectedHead report.headSha
  unless report.reportSha256 == expectedSha256 do
    throw <| identityError .anonymous "report_sha256" expectedSha256 report.reportSha256

def parseReport (expectedHead expectedSha256 bytes : String) : Except String FrozenReport := do
  let report ← parseReportData bytes
  checkFrozenKeys report.headSha report.theorems
  checkReportBinding expectedHead expectedSha256 report
  return report

/-- The source bytes consumed by the syntax authority check. -/
structure ProvenanceSource where
  moduleName : Name
  path : String
  sha256 : String
  deriving Inhabited, BEq

instance : ToJson ProvenanceSource := ⟨fun source => Json.mkObj [
  ("module", toJson source.moduleName), ("path", toJson source.path),
  ("sha256", toJson source.sha256)]⟩

end DispositionCensus

end LeanInformationAudit
