-- Statement encodings are spooled here; the producer compactor computes the
-- byte-identical .NET statement addresses before publishing the report.

import Lean.Environment
import Lean.CoreM
import Lean.PrivateName
import Lean.Elab.Term
import LeanInformationAudit.RawArtifacts
import LeanInformationAudit.CompiledAxioms
import LeanInformationAudit.ArtifactAssessment
import LeanInformationAudit.Contract.FibApplications

namespace LeanInformationAudit.InspectorProducer

open Lean CompiledAxioms

def atom (value : String) : String := s!"{value.utf8ByteSize}:{value}"

partial def encodeName : Name → String
  | .anonymous => "n0"
  | .str parent value => s!"ns({encodeName parent},{atom value})"
  | .num parent value => s!"nn({encodeName parent},{value})"

partial def encodeLevel : Level → String
  | .zero => "l0"
  | .succ level => s!"ls({encodeLevel level})"
  | .max left right => s!"lm({encodeLevel left},{encodeLevel right})"
  | .imax left right => s!"li({encodeLevel left},{encodeLevel right})"
  | .param name => s!"lp({encodeName name})"
  | .mvar id => s!"lv({encodeName id.name})"

def encodeBinderInfo : BinderInfo → String
  | .default => "bd"
  | .implicit => "bi"
  | .strictImplicit => "bs"
  | .instImplicit => "bc"

def encodeLiteral : Literal → String
  | .natVal value => s!"ln({value})"
  | .strVal value => s!"lt({atom value})"

partial def encodeExpr : Expr → String
  | .bvar index => s!"eb({index})"
  | .fvar id => s!"ef({encodeName id.name})"
  | .mvar id => s!"em({encodeName id.name})"
  | .sort level => s!"es({encodeLevel level})"
  | .const name levels =>
      s!"ec({encodeName name},[{String.intercalate "," (levels.map encodeLevel)}])"
  | .app function argument => s!"ea({encodeExpr function},{encodeExpr argument})"
  | .lam _ type body binderInfo =>
      s!"el({encodeBinderInfo binderInfo},{encodeExpr type},{encodeExpr body})"
  | .forallE _ type body binderInfo =>
      s!"ep({encodeBinderInfo binderInfo},{encodeExpr type},{encodeExpr body})"
  | .letE _ type value body nondependent =>
      s!"ee({if nondependent then "1" else "0"},{encodeExpr type},{encodeExpr value},{encodeExpr body})"
  | .lit literal => s!"ei({encodeLiteral literal})"
  | .mdata _ body => s!"ed({encodeExpr body})"
  | .proj name index body => s!"ej({encodeName name},{index},{encodeExpr body})"

def encodeStatement (info : ConstantInfo) : String :=
  let parameters := info.levelParams.map encodeName
  let header :=
    s!"statement-v1(uparams=[{String.intercalate "," parameters}],type={encodeExpr info.type}"
  match info with
  | .defnInfo _ | .opaqueInfo _ =>
      match info.value? (allowOpaque := true) with
      | some value => header ++ s!",value={encodeExpr value})"
      | none => header ++ ",value=missing)"
  | _ => header ++ ")"

/-- Statement-v1 wire output. The bounded buffer amortizes small syntactic
fragments; no complete encoded expression or statement is retained. -/
structure StatementOutput where
  stream : IO.FS.Stream
  buffer : IO.Ref ByteArray

def StatementOutput.flush (out : StatementOutput) : IO Unit := do
  let bytes ← out.buffer.get
  out.buffer.set ByteArray.empty
  unless bytes.isEmpty do out.stream.write bytes

def StatementOutput.put (out : StatementOutput) (text : String) : IO Unit := do
  let bytes := text.toUTF8
  let used := (← out.buffer.get).size
  if used + bytes.size < 65536 then
    out.buffer.modify fun buffer => bytes.copySlice 0 buffer used bytes.size false
  else
    let mut offset := 0
    while offset < bytes.size do
      let used := (← out.buffer.get).size
      let count := min (65536 - used) (bytes.size - offset)
      out.buffer.modify fun buffer => bytes.copySlice offset buffer used count false
      offset := offset + count
      if used + count == 65536 then out.flush

partial def writeLevel (out : StatementOutput) : Level → IO Unit
  | .zero => out.put "l0"
  | .succ level => do out.put "ls("; writeLevel out level; out.put ")"
  | .max left right => do
      out.put "lm("; writeLevel out left; out.put ","; writeLevel out right; out.put ")"
  | .imax left right => do
      out.put "li("; writeLevel out left; out.put ","; writeLevel out right; out.put ")"
  | .param name => out.put s!"lp({encodeName name})"
  | .mvar id => out.put s!"lv({encodeName id.name})"

partial def writeExpr (out : StatementOutput) : Expr → IO Unit
  | .bvar index => out.put s!"eb({index})"
  | .fvar id => out.put s!"ef({encodeName id.name})"
  | .mvar id => out.put s!"em({encodeName id.name})"
  | .sort level => do out.put "es("; writeLevel out level; out.put ")"
  | .const name levels => do
      out.put s!"ec({encodeName name},["
      let mut first := true
      for level in levels do
        unless first do out.put ","
        first := false
        writeLevel out level
      out.put "])"
  | .app function argument => do
      out.put "ea("; writeExpr out function; out.put ","; writeExpr out argument; out.put ")"
  | .lam _ type body binderInfo => do
      out.put s!"el({encodeBinderInfo binderInfo},"
      writeExpr out type; out.put ","; writeExpr out body; out.put ")"
  | .forallE _ type body binderInfo => do
      out.put s!"ep({encodeBinderInfo binderInfo},"
      writeExpr out type; out.put ","; writeExpr out body; out.put ")"
  | .letE _ type value body nondependent => do
      out.put s!"ee({if nondependent then "1" else "0"},"
      writeExpr out type; out.put ","; writeExpr out value
      out.put ","; writeExpr out body; out.put ")"
  | .lit (.strVal value) => do
      out.put s!"ei(lt({value.utf8ByteSize}:"; out.put value; out.put "))"
  | .lit literal => out.put s!"ei({encodeLiteral literal})"
  | .mdata _ body => do out.put "ed("; writeExpr out body; out.put ")"
  | .proj name index body => do
      out.put s!"ej({encodeName name},{index},"; writeExpr out body; out.put ")"

def writeStatement (out : StatementOutput) (info : ConstantInfo) : IO Unit := do
  out.put s!"statement-v1(uparams=[{String.intercalate "," (info.levelParams.map encodeName)}],type="
  writeExpr out info.type
  match info with
  | .defnInfo _ | .opaqueInfo _ =>
    match info.value? (allowOpaque := true) with
    | some value => do out.put ",value="; writeExpr out value
    | none => out.put ",value=missing"
  | _ => pure ()
  out.put ")"
  out.flush

structure ModuleInput where
  moduleName : String
  sourcePath : String
  sourceSha256 : String

structure DeclarationReport where
  axioms : Array String
  includeInStatement : Bool
  kind : String
  materialFile : String
  name : String
  nameKey : String

structure UtilityInput where
  modulePath : String
  claimGid : String
  claimModule : String
  claimSelector : String
  claimSourcePath : String
  claimSourceSha256 : String
  resultGid : String
  resultModule : String
  resultSelector : String
  deriving FromJson

structure RefutationReport where
  claimGid : String
  claimSourcePath : String
  claimSourceSha256 : String
  resultGid : String
  isClosedNegation : Bool

structure ModuleReport where
  declarations : Array DeclarationReport
  imports : Array String
  moduleName : String
  sourcePath : String
  sourceSha256 : String
  refutation : Option RefutationReport := none
  informationRegistrationErrors : Array String := #[]
  informationTemplates : Json := Json.null
  fibApplications : Json := Json.null

def includeInStatement (name : Name) : ConstantInfo → Bool
  | .thmInfo _ => !(privateToUserName name).isInternalDetail
  | _ => true

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .defnInfo _ => "def"
  | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .inductInfo _ => "inductive"

def sortedUnique (values : Array String) : Array String :=
  (values.qsort (· < ·)).foldl (init := #[]) fun result value =>
    if result.back? == some value then result else result.push value

def resolveIncludedDeclaration (moduleData : String → Option ModuleData)
    (find : Name → Option ConstantInfo) (moduleName selector : String) : Option ConstantInfo := do
  let data ← moduleData moduleName
  let selected := data.constNames.filterMap fun name => do
    let info ← find name
    if name.getString! == selector && includeInStatement name info then some info else none
  if selected.size == 1 then selected[0]? else none

def closedExpression (expression : Expr) : Bool :=
  !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars

/-- This checks one declared relationship, not the usefulness or classification of a module. -/
def closedNegation (moduleData : String → Option ModuleData)
    (find : Name → Option ConstantInfo) (input : ModuleInput) (utility : UtilityInput) : IO Bool := do
  if utility.resultModule != input.moduleName || utility.claimGid == utility.resultGid then return false
  let some (.defnInfo claim) := resolveIncludedDeclaration moduleData find utility.claimModule utility.claimSelector
    | return false
  let some (.thmInfo result) := resolveIncludedDeclaration moduleData find utility.resultModule utility.resultSelector
    | return false
  if !claim.levelParams.isEmpty || !result.levelParams.isEmpty
      || !closedExpression claim.type || !closedExpression claim.value
      || !closedExpression result.type || !closedExpression result.value then return false
  -- The kernel checked the proof; SL-031 requires these exact raw types.
  return claim.type.equal (mkSort .zero) &&
    result.type.equal (mkApp (mkConst ``Not) (mkConst claim.name))

elab "informationMaterialWriterProgram" : term => do
  let path := (System.FilePath.mk (← getFileName)).parent.getD "." / "materials.py"
  return mkStrLit path.toString

abbrev MaterialWriter := IO.Process.Child {
  stdin := .piped, stdout := .piped, stderr := .inherit }

def writeMaterial (writer : MaterialWriter) (info : ConstantInfo) : IO Unit := do
  writer.stdin.putStr "chunks\n"
  let stream : IO.FS.Stream := { (default : IO.FS.Stream) with
    write := fun bytes => do
      writer.stdin.putStr s!"{bytes.size}\n"
      writer.stdin.write bytes
      writer.stdin.flush }
  writeStatement ⟨stream, ← IO.mkRef ByteArray.empty⟩ info
  writer.stdin.putStr "0\n"
  writer.stdin.flush
  unless (← writer.stdout.getLine) == "ok\n" do
    throw <| IO.userError "statement spool writer did not acknowledge the material"

def inspectData (moduleData : ModuleData) (find : Name → Option ConstantInfo)
    (refute : UtilityInput → IO Bool) (cache : IO.Ref AxiomClosureState)
    (writer : MaterialWriter) (materialCounter : IO.Ref Nat)
    (utilities : Array UtilityInput)
    (generatedNames : Array Name) (informationTemplates : Json)
    (input : ModuleInput) : IO ModuleReport := do
  let profiling := (← IO.getEnv "STRATALINT_INSPECTOR_PROFILE") == some "1"
  let enumerationStart ← if profiling then IO.monoNanosNow else pure 0
  let allNames := moduleData.constNames ++
    generatedNames.filter (!moduleData.constNames.contains ·)
  let metadata := allNames.filter fun name =>
    match name with
    | .str _ suffix => suffix == "__information_registration_diagnostic"
    | _ => false
  let mut informationRegistrationErrors := #[]
  for name in metadata do
    match find name with
    | some (.defnInfo info) =>
      match info.type, info.value with
      | .const ``String [], .lit (.strVal message) =>
        if !message.isEmpty then informationRegistrationErrors := informationRegistrationErrors.push message
      | _, _ => throw <| IO.userError s!"invalid registration diagnostic: {name}"
    | _ => throw <| IO.userError s!"invalid registration diagnostic: {name}"
  informationRegistrationErrors := sortedUnique informationRegistrationErrors
  let names := (allNames.filter (!metadata.contains ·)).qsort fun left right =>
    encodeName left < encodeName right
  let enumerationEnd ← if profiling then IO.monoNanosNow else pure 0
  let sccNanos ← IO.mkRef 0
  let encodingNanos ← IO.mkRef 0
  let declarations ← names.mapM fun name => do
    let some info := find name
      | throw <| IO.userError s!"declaration missing: {name}"
    let sccStart ← if profiling then IO.monoNanosNow else pure 0
    let axioms ← collectAxiomsShared find cache name
    let encodeStart ← if profiling then IO.monoNanosNow else pure 0
    sccNanos.modify (· + (encodeStart - sccStart))
    let materialIndex ← materialCounter.get
    materialCounter.set (materialIndex + 1)
    let materialFile := s!"{materialIndex}.statement.gz"
    writeMaterial writer info
    if profiling then encodingNanos.modify (· + ((← IO.monoNanosNow) - encodeStart))
    return {
      axioms := sortedUnique (axioms.map Name.toString)
      includeInStatement := includeInStatement name info
      kind := kindOf info
      materialFile
      name := name.toString
      nameKey := encodeName name
    }
  if profiling then
    (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_PROFILE module={input.moduleName} declarations={names.size} enumeration_ns={enumerationEnd - enumerationStart} scc_ns={← sccNanos.get} statement_encoding_ns={← encodingNanos.get} scc_constants={(← cache.get).counter}"
  let obligations := utilities.filter (·.modulePath == input.sourcePath)
  if obligations.size > 1 then
    throw <| IO.userError s!"duplicate utility obligation: {input.sourcePath}"
  let refutation ← match obligations[0]? with
    | none => pure none
    | some utility => do
      let valid ← refute utility
      pure <| some {
        claimGid := utility.claimGid
        claimSourcePath := utility.claimSourcePath
        claimSourceSha256 := utility.claimSourceSha256
        resultGid := utility.resultGid
        isClosedNegation := valid
      }
  return {
    informationTemplates
    informationRegistrationErrors
    declarations
    imports := sortedUnique (moduleData.imports.map (fun item => item.module.toString))
    moduleName := input.moduleName
    sourcePath := input.sourcePath
    sourceSha256 := input.sourceSha256
    refutation
  }

def hexDigit (value : Nat) : Char :=
  Char.ofNat <| if value < 10 then '0'.toNat + value else 'A'.toNat + value - 10

def hex4 (value : Nat) : String :=
  String.ofList [
    hexDigit ((value / 4096) % 16),
    hexDigit ((value / 256) % 16),
    hexDigit ((value / 16) % 16),
    hexDigit (value % 16)
  ]

def jsonCharacter (character : Char) : String :=
  let scalar := character.toNat
  if scalar ≤ 0xffff then
    let encoded := (toJson (String.ofList [character])).compress
    ((encoded.drop 1).dropEnd 1).toString
  else
    let offset := scalar - 0x10000
    let high := 0xd800 + offset / 0x400
    let low := 0xdc00 + offset % 0x400
    "\\u" ++ hex4 high ++ "\\u" ++ hex4 low

def jsonString (value : String) : String :=
  "\"" ++ String.join (value.toList.map jsonCharacter) ++ "\""

def renderStrings (values : Array String) : String :=
  "[" ++ String.intercalate ", " (values.toList.map jsonString) ++ "]"

def renderDeclaration (declaration : DeclarationReport) : String :=
  "{\"axioms\": " ++ renderStrings declaration.axioms
    ++ ", \"include_in_statement\": "
    ++ (if declaration.includeInStatement then "true" else "false")
    ++ ", \"kind\": " ++ jsonString declaration.kind
    ++ ", \"material_file\": " ++ jsonString declaration.materialFile
    ++ ", \"name\": " ++ jsonString declaration.name
    ++ ", \"name_key\": " ++ jsonString declaration.nameKey ++ "}"

def renderModule (report : ModuleReport) : String :=
  "{\"declarations\": ["
    ++ String.intercalate ", " (report.declarations.toList.map renderDeclaration)
    ++ "], \"imports\": " ++ renderStrings report.imports
    ++ ", \"information_registration_errors\": " ++ renderStrings report.informationRegistrationErrors
    ++ (if report.informationTemplates == Json.null then "" else
      ", \"information_templates\": " ++ report.informationTemplates.compress)
    ++ (if report.fibApplications == Json.null then "" else
      ", \"fib_analysis\": " ++ report.fibApplications.compress)
    ++ ", \"module\": " ++ jsonString report.moduleName
    ++ ", \"source_path\": " ++ jsonString report.sourcePath
    ++ ", \"source_sha256\": " ++ jsonString report.sourceSha256
    ++ ", \"utility_refutation\": " ++ (match report.refutation with
      | none => "null"
      | some evidence =>
        "{\"claim_gid\": " ++ jsonString evidence.claimGid
          ++ ", \"claim_source_path\": " ++ jsonString evidence.claimSourcePath
          ++ ", \"claim_source_sha256\": " ++ jsonString evidence.claimSourceSha256
          ++ ", \"is_closed_negation\": " ++ (if evidence.isClosedNegation then "true" else "false")
          ++ ", \"result_gid\": " ++ jsonString evidence.resultGid ++ "}") ++ "}"

def renderReport (reports : Array ModuleReport) : String :=
  "{\"modules\": [" ++ String.intercalate ", " (reports.toList.map renderModule)
    ++ "], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\n"

def parseModuleInputs : List String → Except String (Array ModuleInput)
  | [] => .ok #[]
  | moduleName :: sourcePath :: sourceSha256 :: rest => do
      let tail ← parseModuleInputs rest
      return #[{ moduleName, sourcePath, sourceSha256 }] ++ tail
  | _ => .error "module arguments must be repeated triples: MODULE SOURCE_PATH SOURCE_SHA256"

def parseArguments : List String → Except String
    (System.FilePath × System.FilePath × Option System.FilePath × Array ModuleInput)
  | "--output" :: reportOutput :: "--material-spool" :: materialSpool :: rest => do
      let (utilityInput, rest) := match rest with
        | "--utility-input" :: path :: tail => (some (System.FilePath.mk path), tail)
        | _ => (none, rest)
      let inputs ← parseModuleInputs rest
      if inputs.isEmpty then
        throw "at least one module is required"
      return (reportOutput, materialSpool, utilityInput,
        inputs.qsort (fun left right => left.moduleName < right.moduleName))
  | _ => .error
      "usage: Inspector.lean --output FILE --material-spool DIR [--utility-input FILE] MODULE SOURCE_PATH SOURCE_SHA256 [...]"

private def withReportWriter (reportOutput materialSpool : System.FilePath)
    (statementOnly : Bool) (action : MaterialWriter → IO.FS.Handle → IO Unit) : IO Unit := do
  let localWriter := System.FilePath.mk "tools/lean-inspector/materials.py"
  let writerProgram := if (← localWriter.pathExists) || !statementOnly then
    localWriter.toString else informationMaterialWriterProgram
  let writer ← IO.Process.spawn {
    cmd := "python3", args := #["-I", writerProgram, "stream", materialSpool.toString],
    stdin := .piped, stdout := .piped, stderr := .inherit }
  try
    IO.FS.withFile reportOutput .write fun out => do
      out.putStr "{\"modules\": ["
      action writer out
      writer.stdin.putStr "done\n"
      writer.stdin.flush
      unless (← writer.stdout.getLine) == "done\n" && (← writer.wait) == 0 do
        throw <| IO.userError "statement spool writer did not complete"
      out.putStr "], \"schema\": \"stratalint-lean-inspector-spool-v1\"}\n"
      out.flush
  catch error =>
    try writer.kill catch _ => pure ()
    try discard <| writer.wait catch _ => pure ()
    try IO.FS.removeFile reportOutput catch _ => pure ()
    throw error

-- No target store, assessment, expression cache or report row escapes this frame.
@[noinline] private unsafe def produceTarget (base : RawArtifacts.Store)
    (state : IO.Ref RawArtifacts.Store) (statementOnly profiling : Bool)
    (input : ModuleInput) (utilities : Array UtilityInput)
    (generated : IO.Ref (Std.HashMap Name String))
    (seen : IO.Ref (NameMap Name))
    (writer : MaterialWriter) (out : IO.FS.Handle) (counter : IO.Ref Nat) : IO Unit := do
  state.set base.fork
  let target := input.moduleName.toName
  RawArtifacts.loadModule target state
  for utility in utilities do RawArtifacts.loadModule utility.claimModule.toName state
  if !statementOnly && RawArtifacts.hasTypedInputs (← (← state.get).getModule target) then
    RawArtifacts.loadModule `LeanInformationAudit.TemplateEnrollment state
  let store ← state.get
  RawArtifacts.checkBatchConstants base store seen
  if profiling then
    let slots := store.moduleOrder.foldl (fun count owner =>
      if base.modules.contains owner then count else
        count + ((store.modules.find? owner).map (·.constants.size)).getD 0) 0
    (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_TARGET_LOADED module={target} target_regions={store.regions.size} target_bytes={store.regions.foldl (fun n r => n + r.size.toNat) 0} target_constant_slots={slots}"
  let cache ← IO.mkRef ({ closure := store.metadata.axioms } : AxiomClosureState)
  let empty := if statementOnly then Json.null else Json.mkObj [
    ("schema_version", toJson (1 : Nat)), ("inventory", Json.arr #[]),
    ("registered", Json.arr #[]), ("records", Json.arr #[])]
  let data ← store.getModule target
  let (current, generatedNames, binding, enrollmentErrors) ←
    if !statementOnly && RawArtifacts.hasTypedInputs data then do
      let start ← IO.monoNanosNow
      let (assessment, seals) ← try ArtifactAssessment.assess store target catch error =>
        throw <| IO.userError s!"raw.assessment_failed:{target}:{error}"
      for (name, _) in assessment.generated do
        let some info := assessment.store.constants.find? name
          | throw <| IO.userError s!"incomplete_closure:dtr.generated_missing:{name}"
        let identity := Sha256.hex (reprStr (info.levelParams, info.type,
          info.value? (allowOpaque := true), info.isTheorem)).toUTF8
        if let some previous := (← generated.get)[RawArtifacts.ownName name]? then
          unless previous == identity do
            throw <| IO.userError s!"incomplete_closure:dtr.generated_target:{name}"
        else generated.modify (·.insert (RawArtifacts.ownName name) identity)
      if profiling then
        let own := assessment.records.filter (·.occurrence.key.registrationModule == target)
        let validated := own.filter (fun record => record.result matches .declaredValidated _)
        let unresolved := own.filter (fun record => record.result matches .declaredUnresolved _)
        let ownSeals := seals.filter (·.catalog.rootId == target)
        (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_PROFILE compiled_assess_ns={(← IO.monoNanosNow) - start} module={target} registrations={own.size} validated={validated.size} unresolved={unresolved.size} undeclared={own.size - validated.size - unresolved.size} seal_catalogs={ownSeals.size} seal_theorems={ownSeals.foldl (fun count sealRecord => count + sealRecord.catalog.units.size) 0}"
      pure (assessment.store, assessment.generated.filter (·.2 == target) |>.map Prod.fst,
        ← ArtifactRegistration.targetJson target assessment, assessment.enrollmentErrors)
    else pure (store, #[], empty, #[])
  let row ← inspectData data (current.constants.find?)
    (closedNegation (fun name => current.modules.find? name.toName)
      (current.constants.find?) input)
    cache writer counter utilities generatedNames binding input
  let fib ← if statementOnly then pure Json.null else
    FibApplications.extract target data.constants (current.constants.find?) (current.owners.find?)
  let row := { row with
    fibApplications := fib
    informationRegistrationErrors := sortedUnique (row.informationRegistrationErrors ++ enrollmentErrors) }
  out.putStr (renderModule row)
  out.flush

private unsafe def produceCompiled (reportOutput materialSpool : System.FilePath)
    (statementOnly : Bool) (inputs : Array ModuleInput) (utilities : Array UtilityInput) : IO Unit := do
  let start ← IO.monoNanosNow
  let targets := inputs.map fun input => (input.moduleName.toName,
    utilities.filter (·.modulePath == input.sourcePath) |>.map (·.claimModule.toName))
  let shared ← RawArtifacts.sharedModules targets statementOnly
  let state ← IO.mkRef ({} : RawArtifacts.Store)
  for name in sortedUnique (inputs.map (·.moduleName) ++ utilities.map (·.claimModule)) do
    if shared.contains name.toName then RawArtifacts.loadModule name.toName state
  for name in shared.toArray.qsort Name.quickLt do RawArtifacts.loadModule name state
  let base ← state.get
  let profiling := (← IO.getEnv "STRATALINT_INSPECTOR_PROFILE") == some "1"
  if profiling then
    (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_PROFILE raw_read_ns={(← IO.monoNanosNow) - start} raw_modules={base.modules.toList.length} raw_constants={RawArtifacts.mapSize base.constants} shared_regions={base.regions.size} shared_bytes={base.regions.foldl (fun n r => n + r.size.toNat) 0}"
  let counter ← IO.mkRef 0
  let generated ← IO.mkRef ({} : Std.HashMap Name String)
  let seen ← IO.mkRef ({} : NameMap Name)
  let targetState ← IO.mkRef ({} : RawArtifacts.Store)
  withReportWriter reportOutput materialSpool statementOnly fun writer out => do
    for h : index in [:inputs.size] do
      let input := inputs[index]
      let selected := utilities.filter (·.modulePath == input.sourcePath)
      if index > 0 then out.putStr ", "
      try
        produceTarget base targetState statementOnly profiling input selected generated seen writer out counter
      finally
        RawArtifacts.release targetState
      if profiling then
        let released ← targetState.get
        let resident ← IO.Process.output {
          cmd := "ps", args := #["-o", "rss=", "-p", toString (← IO.Process.getPID)] }
        unless resident.exitCode == 0 do
          throw <| IO.userError "raw.profile_rss_failed"
        (← IO.getStderr).putStrLn s!"LEAN_INSPECTOR_TARGET_RELEASE completed={index + 1} module={input.moduleName} target_constants={RawArtifacts.mapSize released.constants} target_modules={released.modules.toList.length} target_regions={released.regions.size} target_metadata={released.metadata.axioms.toList.length} rss_kib={resident.stdout.trimAscii.toString}"

unsafe def main (args : List String) : IO Unit := do
  let args ← match args with
    | ["--request-file", path] =>
        IO.ofExcept (Json.parse (← IO.FS.readFile path) >>= fromJson? (α := List String))
    | _ => pure args
  -- Statement-only output deliberately has no binding fields and cannot meet
  -- the declared-template admission consumer. It serves standalone encoders.
  let statementOnly := args.head? == some "--statements-only"
  let args := if statementOnly then args.drop 1 else args
  let (reportOutput, materialSpool, utilityInput, inputs) ← match parseArguments args with
    | .ok parsed => pure parsed
    | .error message => throw <| IO.userError message
  IO.FS.createDirAll materialSpool
  initSearchPath (← findSysroot)
  let utilities : Array UtilityInput ← match utilityInput with
    | none => pure #[]
    | some path => do
      let encoded ← IO.FS.readFile path
      match Json.parse encoded >>= fromJson? with
      | .ok values => pure values
      | .error message => throw <| IO.userError s!"invalid utility input: {message}"
  let selectedUtilities := utilities.filter fun utility =>
    inputs.any (·.sourcePath == utility.modulePath)
  produceCompiled reportOutput materialSpool statementOnly inputs selectedUtilities

end LeanInformationAudit.InspectorProducer

unsafe def main (args : List String) : IO UInt32 := do
  try
    LeanInformationAudit.InspectorProducer.main args
    return 0
  catch error =>
    (← IO.getStderr).putStrLn s!"lean-inspector: {error}"
    return 1
