import LeanInformationAudit.Census.Codec

namespace LeanInformationAudit.DispositionCensus

open Lean

def censusArtifactFields : Array String := #["schema", "head_sha", "report_sha256",
  "source_inputs", "theorem_count", "counts", "certified_complete", "rows"]

structure Counts where
  accounted : Nat := 0
  certified : Nat := 0
  observed : Nat := 0
  observedQueryCompleted : Nat := 0
  observedQueryIncomplete : Nat := 0
  finiteOccurrence : Nat := 0
  structuralOccurrence : Nat := 0
  boundedFiniteTruncation : Nat := 0
  unreachable : Nat := 0
  noCanonicalObjectCarrier : Nat := 0
  noFinitePrimitiveBundle : Nat := 0
  noFaithfulPrimitiveRealization : Nat := 0
  deriving DecidableEq, Repr

def Counts.addEntry (counts : Counts)
    (entry : Sigma fun key : StatementKey => CensusAssessment key) : Counts :=
  let counts := { counts with accounted := counts.accounted + 1 }
  match entry.2 with
  | .observed value =>
    if value.queryCompleted then
      let counts := { counts with observed := counts.observed + 1 }
      { counts with observedQueryCompleted := counts.observedQueryCompleted + 1 }
    else
      { counts with observedQueryIncomplete := counts.observedQueryIncomplete + 1 }
  | .certified disposition =>
    let counts := { counts with certified := counts.certified + 1 }
    match disposition with
    | .finiteOccurrence _ => { counts with finiteOccurrence := counts.finiteOccurrence + 1 }
    | .structuralOccurrence _ =>
      { counts with structuralOccurrence := counts.structuralOccurrence + 1 }
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

def count (inventory : DispositionInventory) : Counts :=
  inventory.entries.foldl (init := {}) Counts.addEntry

def Counts.fields (counts : Counts) : List (String × Nat) := [
  ("accounted", counts.accounted),
  ("certified", counts.certified),
  ("observed", counts.observed),
  ("observed_query_completed", counts.observedQueryCompleted),
  ("observed_query_incomplete", counts.observedQueryIncomplete),
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
  for entry in inventory.entries do
    if let .observed value := entry.2 then
      checkObservationStatus inventory.headSha value
  for ((name, expected), (_, actual)) in (count inventory).fields.zip counts.fields do
    unless expected == actual do
      throw <| censusError inventory.headSha name (toString expected) (toString actual)

def stringField (json : Json) (field : String) : Except String String := do
  let value ← json.getObjValAs? String field
  if value.isEmpty then throw field
  return value

private def nameField (json : Json) (field : String) : Except String Name := do
  parseNameJson (← json.getObjVal? field)

private def nameArrayField (json : Json) (field : String) : Except String (Array Name) := do
  (← json.getObjValAs? (Array Json) field).mapM parseNameJson

private def exactFields (json : Json) (fields : List String) : Except String Unit := do
  let object ← json.getObj?
  unless object.size == fields.length && fields.all object.contains do
    throw "payload_fields"

/-- Strict decoding makes the dependent constructor, not a separate label, own the payload. -/
def parseRow (row : Json) (queryScope : Option ImportClosureScope := none) : Except String
    (Sigma fun key : StatementKey => CensusAssessment key) := do
  let key : StatementKey := ⟨← nameField row "theorem_name", ← stringField row "statement_id"⟩
  discard <| decodeStatementId key.theoremName key.statementId
  let className ← stringField row "class"
  let parsed : Except String (CensusAssessment key) := do
    exactFields row ["theorem_name", "statement_id", "class", "payload"]
    let payload ← row.getObjVal? "payload"
    match className with
    | "finite_occurrence" =>
      exactFields payload ["canonical_arena", "registration", "realization",
        "nondegeneracy_certificate", "state_enumeration_certificate"]
      return .certified <| .finiteOccurrence ⟨← nameField payload "canonical_arena",
        ← nameField payload "registration", ← nameField payload "realization",
        ← nameField payload "nondegeneracy_certificate",
        ← nameField payload "state_enumeration_certificate"⟩
    | "structural_occurrence" =>
      exactFields payload ["canonical_arena", "registration", "realization",
        "strictness_certificate", "witness_certificate"]
      return .certified <| .structuralOccurrence ⟨← nameField payload "canonical_arena",
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
      return .certified <| .boundedFiniteTruncation ⟨← nameField payload "truncation_family",
        ← payload.getObjValAs? Nat "bound", ← nameField payload "comparison_statement", certification⟩
    | "unreachable" =>
      exactFields payload ["reason", "evidence"]
      let reason ← match ← stringField payload "reason" with
        | "no_canonical_object_carrier" => pure UnreachableReason.noCanonicalObjectCarrier
        | "no_finite_primitive_bundle" => pure UnreachableReason.noFinitePrimitiveBundle
        | "no_faithful_primitive_realization" => pure UnreachableReason.noFaithfulPrimitiveRealization
        | _ => throw "reason"
      return .certified <| .unreachable ⟨reason, ← nameField payload "evidence"⟩
    | "observed" =>
      exactFields payload ["owning_module", "root", "import_scope", "query_completed",
        "candidates", "note"]
      let encodedScope ← payload.getObjVal? "import_scope"
      let scope ← match encodedScope, queryScope with
        | .null, some scope => pure scope
        | _, _ => do
          exactFields encodedScope ["modules", "completed"]
          pure { modules := ← nameArrayField encodedScope "modules"
                 completed := ← encodedScope.getObjValAs? Bool "completed" }
      return .observed {
        owningModule := ← nameField payload "owning_module"
        root := ← nameField payload "root"
        importScope := scope
        queryCompleted := ← payload.getObjValAs? Bool "query_completed"
        candidates := ← nameArrayField payload "candidates"
        note := ← payload.getObjValAs? String "note" }
    | _ => throw "class"
  match parsed with
  | .ok disposition => return ⟨key, disposition⟩
  | .error invalid => throw <| classError key.theoremName className invalid

def parseInventory (json : Json) : Except String DispositionInventory := do
  exactFields json ["head_sha", "entries"]
  return { headSha := ← stringField json "head_sha"
           entries := ← (← json.getObjValAs? (Array Json) "entries").mapM parseRow }

end LeanInformationAudit.DispositionCensus
