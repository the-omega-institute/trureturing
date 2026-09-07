import LeanInformationAudit.AnalysisDisposition
import LeanInformationAudit.Sha256
import LeanInformationAudit.DispositionEvidence
import Std.Internal.Parsec.ByteArray

namespace LeanInformationAudit

open Lean

namespace DispositionCensus

private def checkFrozenKeys (head : String) (keys : Array StatementKey) : Except String Unit := do
  let mut names : Std.HashSet Name := {}
  let mut ids : Std.HashSet String := {}
  for key in keys do
    if names.contains key.theoremName || ids.contains key.statementId then
      throw <| censusError head "frozen_keys" "unique" (toJson key).compress
    names := names.insert key.theoremName
    ids := ids.insert key.statementId

/-- Duplicate statement IDs are checked before identity and missing-row diagnostics. -/
def checkCoverage (head : String) (frozen : Array StatementKey)
    (inventory : DispositionInventory) : Except String Unit := do
  let expected := frozen.qsort StatementKey.lt
  checkFrozenKeys head expected
  for key in expected do
    unless inventory.headSha == head do
      throw <| identityError key.theoremName "head" head inventory.headSha
  unless inventory.headSha == head do
    throw <| identityError .anonymous "head" head inventory.headSha
  let mut records : Std.HashMap String (Array Nat) := {}
  for i in [:inventory.entries.size] do
    let id := inventory.entries[i]!.1.statementId
    records := records.insert id ((records.getD id #[]).push i)
  for entry in inventory.entries do
    let key := entry.1
    let duplicates := records.getD key.statementId #[]
    if duplicates.size > 1 then
      throw s!"IE-C035 DuplicateAnalysisDisposition theorem={key.theoremName} statement_id={key.statementId} records={(toJson duplicates).compress}"
  let names : Std.HashMap Name StatementKey :=
    expected.foldl (init := {}) fun result key => result.insert key.theoremName key
  for entry in inventory.sortedEntries do
    match names[entry.1.theoremName]? with
    | some key =>
      unless key.statementId == entry.1.statementId do
        throw <| identityError key.theoremName "statement_id" key.statementId entry.1.statementId
    | none =>
      let expectedName := (expected.find? (·.statementId == entry.1.statementId)).map
        (·.theoremName.toString) |>.getD "absent"
      throw <| identityError entry.1.theoremName "theorem_name" expectedName entry.1.theoremName.toString
  for key in expected do
    unless records.contains key.statementId do
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
  parseNameJson (← json.getObjVal? field)

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
The producer owns frozen membership; source provenance checks do not discover members. -/
structure FrozenReport where
  headSha : String
  reportSha256 : String
  theorems : Array StatementKey

open Std.Internal.Parsec Std.Internal.Parsec.ByteArray in
private partial def nameKeyParser : Std.Internal.Parsec.ByteArray.Parser Name := do
    skipByteChar 'n'
    match ← any with
    | 48 => return .anonymous
    | 115 =>
      skipByteChar '('
      let parent ← nameKeyParser
      skipByteChar ','
      let size ← digits
      skipByteChar ':'
      let bytes ← take size
      let some text := String.fromUTF8? bytes.toByteArray | fail "invalid UTF-8 name component"
      skipByteChar ')'
      return .str parent text
    | 110 =>
      skipByteChar '('
      let parent ← nameKeyParser
      skipByteChar ','
      let index ← digits
      skipByteChar ')'
      return .num parent index
    | _ => fail "invalid Lean name key"

/-- Decode the inspector's structured, byte-length-prefixed Name encoding. -/
def parseNameKey (text : String) : Except String Name :=
  (nameKeyParser <* Std.Internal.Parsec.eof).run text.toUTF8

/-- Consume the existing strict frozen truth export, produced from an elaborated
report by TruthExportCommand. source_commit binds HEAD; declaration_name_key
preserves Lean Name structure; statement_id is read verbatim. Non-theorems are ignored.
The caller pins the report bytes independently with expectedSha256. -/
def parseReport (expectedHead expectedSha256 bytes : String) : Except String FrozenReport := do
  let actualSha256 := "sha256:" ++ Sha256.hex bytes.toUTF8
  unless actualSha256 == expectedSha256 do
    throw <| identityError .anonymous "report_sha256" expectedSha256 actualSha256
  let json ← Json.parse bytes
  for (field, expected) in [("schema", "stratalint.truth-export"),
      ("dialect", "stratalint.truth-export.v1"), ("producer", "TruthExportCommand")] do
    unless (← stringField json field) == expected do
      throw <| censusError expectedHead field expected (← stringField json field)
  unless (← json.getObjValAs? Nat "schema_version") == 1 do
    throw <| censusError expectedHead "schema_version" "1"
      (toString (← json.getObjValAs? Nat "schema_version"))
  let head ← stringField json "source_commit"
  unless head == expectedHead do
    throw <| identityError .anonymous "head" expectedHead head
  let modules ← json.getObjValAs? (Array Json) "nodes"
  let mut keys : Array StatementKey := #[]
  for moduleRow in modules do
    let declarations ← moduleRow.getObjValAs? (Array Json) "declarations"
    for declaration in declarations do
      if (← stringField declaration "kind") == "theorem" then
        keys := keys.push ⟨← parseNameKey (← stringField declaration "declaration_name_key"),
          ← stringField declaration "statement_id"⟩
  let sorted := keys.qsort StatementKey.lt
  checkFrozenKeys head sorted
  return { headSha := head, reportSha256 := actualSha256, theorems := sorted }

def artifact (report : FrozenReport) (inventory : DispositionInventory)
    (sources : Array ProvenanceSource := #[]) : Except String Json := do
  checkCoverage report.headSha report.theorems inventory
  let counts := count inventory
  checkCounts inventory counts
  return Json.mkObj [
    ("schema", toJson "lean-information-disposition-census"),
    ("head_sha", toJson report.headSha), ("report_sha256", toJson report.reportSha256),
    ("source_inputs", toJson sources),
    ("theorem_count", toJson report.theorems.size), ("counts", toJson counts),
    ("rows", Json.arr <| inventory.sortedEntries.map dispositionRowJson)]

/-- Independently checks an output projection against its input inventory. -/
def checkArtifact (report : FrozenReport) (inventory : DispositionInventory)
    (candidate : Json) (sources : Array ProvenanceSource := #[]) : Except String Unit := do
  let expected ← artifact report inventory sources
  for field in ["schema", "head_sha", "report_sha256", "source_inputs", "theorem_count", "counts", "rows"] do
    let expectedValue ← expected.getObjVal? field
    let actual ← match candidate.getObjVal? field with
      | .ok value => pure value
      | .error _ => throw <| censusError report.headSha field expectedValue.compress "missing"
    unless expectedValue.compress == actual.compress do
      throw <| censusError report.headSha field expectedValue.compress actual.compress

open Meta Elab Command

private def keyExpr (key : StatementKey) : Expr :=
  mkApp2 (mkConst ``StatementKey.mk) (toExpr key.theoremName) (toExpr key.statementId)

private def rowExpr (entry : Sigma fun key : StatementKey => AnalysisDisposition key) : MetaM Expr := do
  let key := keyExpr entry.1
  let (constructor, payload) ← match entry.2 with
    | .finiteOccurrence value => do
      let payload ← mkAppOptM ``FiniteOccurrenceDisposition.mk #[some key,
        some (toExpr value.canonicalArena), some (toExpr value.registration),
        some (toExpr value.realization), some (toExpr value.nondegeneracyCertificate),
        some (toExpr value.stateEnumerationCertificate)]
      pure (``AnalysisDisposition.finiteOccurrence, payload)
    | .structuralOccurrence value => do
      let payload ← mkAppOptM ``StructuralOccurrenceDisposition.mk #[some key,
        some (toExpr value.canonicalArena), some (toExpr value.registration),
        some (toExpr value.realization), some (toExpr value.strictnessCertificate),
        some (toExpr value.witnessCertificate)]
      pure (``AnalysisDisposition.structuralOccurrence, payload)
    | .boundedFiniteTruncation value => do
      let certification := match value.certification with
        | .reportOnly => mkConst ``TruncationCertification.reportOnly
        | .transferred name => mkApp (mkConst ``TruncationCertification.transferred) (toExpr name)
      let payload ← mkAppOptM ``BoundedFiniteTruncationDisposition.mk #[some key,
        some (toExpr value.truncationFamily), some (toExpr value.bound),
        some (toExpr value.comparisonStatement), some certification]
      pure (``AnalysisDisposition.boundedFiniteTruncation, payload)
    | .unreachable value => do
      let reason := mkConst <| match value.reason with
        | .noCanonicalObjectCarrier => ``UnreachableReason.noCanonicalObjectCarrier
        | .noFinitePrimitiveBundle => ``UnreachableReason.noFinitePrimitiveBundle
        | .noFaithfulPrimitiveRealization => ``UnreachableReason.noFaithfulPrimitiveRealization
      let payload ← mkAppOptM ``UnreachableDisposition.mk #[some key,
        some reason, some (toExpr value.evidence)]
      pure (``AnalysisDisposition.unreachable, payload)
  let disposition ← mkAppOptM constructor #[some key, some payload]
  let motive := mkLambda `key .default (mkConst ``StatementKey)
    (mkApp (mkConst ``AnalysisDisposition) (.bvar 0))
  mkAppOptM ``Sigma.mk #[some (mkConst ``StatementKey), some motive, some key, some disposition]

/-- Reifies the actual inventory and asks Lean's kernel to verify ExactlyCovers.
No native evaluation result is used as a proof. -/
def coverageProof (report : FrozenReport) (inventory : DispositionInventory) : MetaM Expr := do
  let motive := mkLambda `key .default (mkConst ``StatementKey)
    (mkApp (mkConst ``AnalysisDisposition) (.bvar 0))
  let rowType := mkApp2 (mkConst ``Sigma [.zero, .zero]) (mkConst ``StatementKey) motive
  let entries ← mkArrayLit rowType (← inventory.entries.toList.mapM rowExpr)
  let inventoryExpr := mkApp2 (mkConst ``DispositionInventory.mk) (toExpr inventory.headSha) entries
  let keys ← mkListLit (mkConst ``StatementKey) (report.theorems.toList.map keyExpr)
  let frozen ← mkAppM ``List.toFinset #[keys]
  let proposition ← mkAppM ``DispositionInventory.ExactlyCovers
    #[inventoryExpr, toExpr report.headSha, frozen]
  let proof ← mkDecideProof proposition
  checkWithKernel proof
  return proof

private def readUtf8 (path : String) : IO String := do
  let bytes ← IO.FS.readBinFile path
  match String.fromUTF8? bytes with
  | some text => return text
  | none => throw <| IO.userError s!"invalid UTF-8: {path}"

/-- Report-only command. File inputs are stratalint.truth-export.v1 and the source
modules of structural rows, resolved by findLean/getSrcSearchPath and hashed in
source_inputs. Provenance means generated by structural_theorem in source;
source rewriting during a build and modified source search paths are out of scope.
The inventory is a typed declaration in the elaborated environment. It stages
ExactlyCovers only after checking the full inventory and its semantic evidence.
The resulting JSON is output, never seal input. -/
elab "#disposition_census" &"root" root:ident &"report" reportPath:str
    &"head" head:str &"report_sha256" reportSha:str &"inventory" inventoryName:ident
    &"certificate" certificate:ident " output " outputPath:str : command => do
  -- realPath resolves relative components and symlinks before any declaration is staged.
  let inputResolved ← IO.FS.realPath reportPath.getString
  let destination : System.FilePath := outputPath.getString
  if ← destination.pathExists then
    if inputResolved == (← IO.FS.realPath destination) then
      throwError (censusError head.getString "output_path" "distinct-from-report" "report-alias")
    -- Lean metadata exposes link counts but not inode identity. POSIX test -ef
    -- compares the existing files without involving shell parsing.
    if (← destination.metadata).numLinks > 1 then
      let comparison ← IO.Process.output {
        cmd := "/bin/test", args := #[reportPath.getString, "-ef", outputPath.getString] }
      if comparison.exitCode == 0 then
        throwError (censusError head.getString "output_path" "distinct-from-report" "report-alias")
      unless comparison.exitCode == 1 do
        throwError "cannot compare census input/output file identities"
  let reportBytes ← readUtf8 reportPath.getString
  let report ← ofExcept <| parseReport head.getString reportSha.getString reportBytes
  let inventory ← liftTermElabM do
    let name ← realizeGlobalConstNoOverloadWithInfo inventoryName
    let value ← mkConstWithFreshMVarLevels name
    unless ← isDefEq (← inferType value) (mkConst ``DispositionInventory) do
      throwError "expected a DispositionInventory declaration: {name}"
    checkWithKernel value
    unsafe evalExpr DispositionInventory (mkConst ``DispositionInventory) value
  ofExcept <| checkCoverage report.headSha report.theorems inventory
  let certificateName := (← getCurrNamespace) ++ certificate.getId.eraseMacroScopes
  if (← getEnv).contains certificateName then
    throwError "disposition census certificate already exists: {certificateName}"
  let (proof, sources) ← liftTermElabM do
    let sources ← validateEvidenceSources root.getId.eraseMacroScopes inventory
    return (← coverageProof report inventory, sources)
  let proofType ← liftTermElabM <| inferType proof
  let projection ← ofExcept <| artifact report inventory sources
  ofExcept <| checkArtifact report inventory projection sources
  let declaration := Declaration.thmDecl {
    name := certificateName
    levelParams := []
    type := proofType
    value := proof
  }
  let options ← getOptions
  let stagedEnv ← match (← getEnv).addDeclCore (Core.getMaxHeartbeats options).toUSize
      (maxRecDepth.get options).toUSize declaration none true with
    | .ok env => pure env
    | .error error => throwError "{error.toMessageData options}"
  IO.FS.writeFile outputPath.getString (projection.pretty ++ "\n")
  setEnv stagedEnv

end DispositionCensus

end LeanInformationAudit
