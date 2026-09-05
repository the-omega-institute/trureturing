import LeanInformationAudit.AnalysisDisposition
import LeanInformationAudit.Sha256

namespace LeanInformationAudit

open Lean

namespace DispositionCensus

/-- Duplicate statement IDs are checked before identity and missing-row diagnostics. -/
def checkCoverage (head : String) (frozen : Array StatementKey)
    (inventory : DispositionInventory) : Except String Unit := do
  let expected := frozen.qsort StatementKey.lt
  for key in expected do
    unless inventory.headSha == head do
      throw <| identityError key.theoremName "head" head inventory.headSha
  unless inventory.headSha == head do
    throw <| identityError .anonymous "head" head inventory.headSha
  for i in [:inventory.entries.size] do
    let key := inventory.entries[i]!.1
    let duplicates := (List.range inventory.entries.size).filter fun j =>
      inventory.entries[j]!.1.statementId == key.statementId
    if duplicates.length > 1 then
      throw s!"IE-C035 DuplicateAnalysisDisposition theorem={key.theoremName} statement_id={key.statementId} records={(toJson duplicates).compress}"
  for entry in inventory.sortedEntries do
    match expected.find? (·.theoremName == entry.1.theoremName) with
    | some key =>
      unless key.statementId == entry.1.statementId do
        throw <| identityError key.theoremName "statement_id" key.statementId entry.1.statementId
    | none =>
      let expectedName := (expected.find? (·.statementId == entry.1.statementId)).map
        (·.theoremName.toString) |>.getD "absent"
      throw <| identityError entry.1.theoremName "theorem_name" expectedName entry.1.theoremName.toString
  for key in expected do
    unless inventory.entries.any (·.1 == key) do
      throw s!"IE-C034 MissingAnalysisDisposition theorem={key.theoremName} statement_id={key.statementId} head={head}"
  unless inventory.ExactlyCovers head frozen.toList.toFinset do
    throw <| censusError head "keys" (toJson expected).compress
      (toJson inventory.keys).compress

structure Counts where
  finiteOccurrence : Nat := 0
  structuralOccurrence : Nat := 0
  boundedFiniteTruncation : Nat := 0
  unreachable : Nat := 0
  noCanonicalObjectCarrier : Nat := 0
  noFinitePrimitiveBundle : Nat := 0
  noFaithfulPrimitiveRealization : Nat := 0
  deriving DecidableEq, Repr

def count (inventory : DispositionInventory) : Counts :=
  inventory.entries.foldl (init := {}) fun counts entry =>
    match entry.2 with
    | .finiteOccurrence _ => { counts with finiteOccurrence := counts.finiteOccurrence + 1 }
    | .structuralOccurrence _ => { counts with structuralOccurrence := counts.structuralOccurrence + 1 }
    | .boundedFiniteTruncation _ =>
      { counts with boundedFiniteTruncation := counts.boundedFiniteTruncation + 1 }
    | .unreachable value =>
      let counts := { counts with unreachable := counts.unreachable + 1 }
      match value.reason with
      | .noCanonicalObjectCarrier =>
        { counts with noCanonicalObjectCarrier := counts.noCanonicalObjectCarrier + 1 }
      | .noFinitePrimitiveBundle =>
        { counts with noFinitePrimitiveBundle := counts.noFinitePrimitiveBundle + 1 }
      | .noFaithfulPrimitiveRealization =>
        { counts with noFaithfulPrimitiveRealization := counts.noFaithfulPrimitiveRealization + 1 }

def Counts.fields (counts : Counts) : List (String × Nat) := [
  ("finite_occurrence", counts.finiteOccurrence),
  ("structural_occurrence", counts.structuralOccurrence),
  ("bounded_finite_truncation", counts.boundedFiniteTruncation),
  ("unreachable", counts.unreachable),
  ("no_canonical_object_carrier", counts.noCanonicalObjectCarrier),
  ("no_finite_primitive_bundle", counts.noFinitePrimitiveBundle),
  ("no_faithful_primitive_realization", counts.noFaithfulPrimitiveRealization)]

instance : ToJson Counts := ⟨fun counts => Json.mkObj <|
  counts.fields.map fun (name, value) => (name, toJson value)⟩

def checkCounts (inventory : DispositionInventory) (counts : Counts) : Except String Unit := do
  for ((name, expected), (_, actual)) in (count inventory).fields.zip counts.fields do
    unless expected == actual do
      throw <| censusError inventory.headSha name (toString expected) (toString actual)

private def stringField (json : Json) (field : String) : Except String String := do
  let value ← json.getObjValAs? String field
  if value.isEmpty then throw field
  return value

private def nameField (json : Json) (field : String) : Except String Name := do
  let value ← stringField json field
  let name := value.toName
  if name.isAnonymous || name.toString != value then throw field
  return name

private def exactFields (json : Json) (fields : List String) : Except String Unit := do
  let object ← json.getObj?
  unless object.size == fields.length && fields.all object.contains do
    throw "payload_fields"

/-- Strict decoding makes the dependent constructor, not a separate label, own the payload. -/
def parseRow (row : Json) : Except String
    (Sigma fun key : StatementKey => AnalysisDisposition key) := do
  let key : StatementKey := ⟨← nameField row "theorem_name", ← stringField row "statement_id"⟩
  let className ← stringField row "class"
  let parsed : Except String (AnalysisDisposition key) := do
    exactFields row ["theorem_name", "statement_id", "class", "payload"]
    let payload ← row.getObjVal? "payload"
    match className with
    | "finite_occurrence" =>
      exactFields payload ["canonical_arena", "registration", "realization",
        "nondegeneracy_certificate", "state_enumeration_certificate"]
      return .finiteOccurrence ⟨← nameField payload "canonical_arena",
        ← nameField payload "registration", ← nameField payload "realization",
        ← nameField payload "nondegeneracy_certificate",
        ← nameField payload "state_enumeration_certificate"⟩
    | "structural_occurrence" =>
      exactFields payload ["canonical_arena", "registration", "realization",
        "strictness_certificate", "witness_certificate"]
      return .structuralOccurrence ⟨← nameField payload "canonical_arena",
        ← nameField payload "registration", ← nameField payload "realization",
        ← nameField payload "strictness_certificate", ← nameField payload "witness_certificate"⟩
    | "bounded_finite_truncation" =>
      exactFields payload ["truncation_family", "bound", "comparison_statement", "certification"]
      let certification ← payload.getObjVal? "certification"
      let certification ← match ← stringField certification "kind" with
        | "report_only" => do
          exactFields certification ["kind"]
          pure TruncationCertification.reportOnly
        | "transferred" => do
          exactFields certification ["kind", "transfer_theorem"]
          pure <| TruncationCertification.transferred (← nameField certification "transfer_theorem")
        | _ => throw "certification"
      return .boundedFiniteTruncation ⟨← nameField payload "truncation_family",
        ← payload.getObjValAs? Nat "bound", ← nameField payload "comparison_statement", certification⟩
    | "unreachable" =>
      exactFields payload ["reason", "evidence"]
      let reason ← match ← stringField payload "reason" with
        | "no_canonical_object_carrier" => pure UnreachableReason.noCanonicalObjectCarrier
        | "no_finite_primitive_bundle" => pure UnreachableReason.noFinitePrimitiveBundle
        | "no_faithful_primitive_realization" => pure UnreachableReason.noFaithfulPrimitiveRealization
        | _ => throw "reason"
      return .unreachable ⟨reason, ← nameField payload "evidence"⟩
    | _ => throw "class"
  match parsed with
  | .ok disposition => return ⟨key, disposition⟩
  | .error invalid => throw <| classError key.theoremName className invalid

def parseInventory (json : Json) : Except String DispositionInventory := do
  exactFields json ["head_sha", "entries"]
  return { headSha := ← stringField json "head_sha"
           entries := ← (← json.getObjValAs? (Array Json) "entries").mapM parseRow }

/-- An immutable report already restricted to frozen elaborated theorem declarations.
The producer owns frozen membership; this consumer never scans Lean source files. -/
structure FrozenReport where
  headSha : String
  reportSha256 : String
  theorems : Array StatementKey

/-- The input envelope has schema, head_sha, and modules. Modules retain the native
inspector declarations (kind/name/statement_id); non-theorems do not enter the census.
The expected report digest and HEAD are caller inputs, not claims trusted from the file. -/
def parseReport (expectedHead expectedSha256 bytes : String) : Except String FrozenReport := do
  let actualSha256 := "sha256:" ++ Sha256.hex bytes.toUTF8
  unless actualSha256 == expectedSha256 do
    throw <| identityError .anonymous "report_sha256" expectedSha256 actualSha256
  let json ← Json.parse bytes
  unless (← stringField json "schema") == "lean-information-frozen-elaborated-report-v1" do
    throw <| censusError expectedHead "schema" "lean-information-frozen-elaborated-report-v1"
      (← stringField json "schema")
  let head ← stringField json "head_sha"
  unless head == expectedHead do
    throw <| identityError .anonymous "head" expectedHead head
  let modules ← json.getObjValAs? (Array Json) "modules"
  let mut keys : Array StatementKey := #[]
  for moduleRow in modules do
    let declarations ← moduleRow.getObjValAs? (Array Json) "declarations"
    for declaration in declarations do
      if (← stringField declaration "kind") == "theorem" then
        keys := keys.push ⟨← nameField declaration "name", ← stringField declaration "statement_id"⟩
  let sorted := keys.qsort StatementKey.lt
  for i in [:sorted.size] do
    for j in [:i] do
      if sorted[i]!.theoremName == sorted[j]!.theoremName ||
          sorted[i]!.statementId == sorted[j]!.statementId then
        throw <| censusError head "frozen_keys" "unique" (toJson sorted[i]!).compress
  return { headSha := head, reportSha256 := actualSha256, theorems := sorted }

def artifact (report : FrozenReport) (inventory : DispositionInventory) : Except String Json := do
  checkCoverage report.headSha report.theorems inventory
  let counts := count inventory
  checkCounts inventory counts
  return Json.mkObj [
    ("schema", toJson "lean-information-disposition-census-v1"),
    ("head_sha", toJson report.headSha), ("report_sha256", toJson report.reportSha256),
    ("theorem_count", toJson report.theorems.size), ("counts", toJson counts),
    ("rows", Json.arr <| inventory.sortedEntries.map dispositionRowJson)]

end DispositionCensus

end LeanInformationAudit
