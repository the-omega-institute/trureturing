-- Statement encodings are spooled here; the producer compactor computes the
-- byte-identical .NET statement addresses before publishing the report.

import Lean.Environment
import Lean.CoreM
import Lean.PrivateName
import Lean.Util.CollectAxioms
import Lean.Meta

open Lean

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

/-- Single owner of dependency semantics for both axiom closure and structural
extraction. Keep the type/constructor and optional value halves separate. -/
def declarationDependencyParts (info : ConstantInfo) : Array Name × Option (Array Name) :=
  let types := match info with
    | .quotInfo _ => #[]
    | .inductInfo value => value.type.getUsedConstants ++ value.ctors.toArray
    | value => value.type.getUsedConstants
  (types, (info.value? (allowOpaque := true)).map Expr.getUsedConstants)

/-- The union consumed by the report's transitive axiom traversal. -/
def declarationDependencies (info : ConstantInfo) : Array Name :=
  let (types, values) := declarationDependencyParts info
  types ++ values.getD #[]

/-- Report-shared state for axiom-closure collection. `closure` memoizes the final
sorted axiom set of every constant once its strongly connected component has been
resolved; the remaining fields are the working state of the Tarjan traversal. -/
structure AxiomClosureState where
  counter : Nat := 0
  index : NameMap Nat := {}
  low : NameMap Nat := {}
  onStack : NameSet := {}
  stack : Array Name := #[]
  closure : NameMap (Array Name) := {}

/-- Tarjan strong-connect that finalizes, into `state.closure`, the transitive axiom
closure of every constant reachable from `constant`. Constants that are mutually
dependent (an inductive and its constructors, mutually recursive definitions, …)
form one strongly connected component and share a single closure: the union of the
component members' own axioms with every external successor's already-finalized
closure. That is exactly the complete transitive axiom set that stock
`Lean.collectAxioms` returns for any member queried at top level — a naive
memoized DFS instead caches the cycle-truncated partial set of whichever member it
reaches first, so this SCC treatment is required for byte-identical reports. The
shared `state` walks each constant's subgraph at most once for the whole run, where
the stock routine (a fresh cache per call) re-walked the imported closure for every
referencing declaration. -/
partial def strongConnect (environment : Environment)
    (state : IO.Ref AxiomClosureState) (constant : Name) : IO Unit := do
  state.modify fun s => { s with
    index := s.index.insert constant s.counter
    low := s.low.insert constant s.counter
    counter := s.counter + 1
    onStack := s.onStack.insert constant
    stack := s.stack.push constant }
  let dependencies := ((environment.find? constant).map declarationDependencies).getD #[]
  for dependency in dependencies do
    let s ← state.get
    if !(s.index.contains dependency) then
      strongConnect environment state dependency
      let s ← state.get
      let lowDependency := (s.low.find? dependency).getD 0
      if lowDependency < (s.low.find? constant).getD 0 then
        state.modify fun s => { s with low := s.low.insert constant lowDependency }
    else if s.onStack.contains dependency then
      let indexDependency := (s.index.find? dependency).getD 0
      if indexDependency < (s.low.find? constant).getD 0 then
        state.modify fun s => { s with low := s.low.insert constant indexDependency }
  let s ← state.get
  if (s.low.find? constant).getD 0 == (s.index.find? constant).getD 0 then
    let mut members : Array Name := #[]
    let mut remaining := s.stack
    let mut popped := Name.anonymous
    repeat
      popped := remaining.back!
      remaining := remaining.pop
      members := members.push popped
    until popped == constant
    let memberSet : NameSet := members.foldl (init := {}) (fun set name => set.insert name)
    let mut axioms : NameSet := {}
    for member in members do
      if (environment.find? member) matches some (.axiomInfo _) then
        axioms := axioms.insert member
      for dependency in (((environment.find? member).map declarationDependencies).getD #[]) do
        if !(memberSet.contains dependency) then
          for entry in ((s.closure.find? dependency).getD #[]) do
            axioms := axioms.insert entry
    let result := axioms.toArray
    state.modify fun s => { s with
      closure := members.foldl (init := s.closure) (fun map name => map.insert name result)
      onStack := members.foldl (init := s.onStack) (fun set name => set.erase name)
      stack := remaining }

/-- Transitive axiom closure of `constant`, memoized across every declaration in the
run through `state` (see `strongConnect`). -/
def collectAxiomsShared (environment : Environment)
    (state : IO.Ref AxiomClosureState) (constant : Name) : IO (Array Name) := do
  if let some cached := (← state.get).closure.find? constant then
    return cached
  strongConnect environment state constant
  return ((← state.get).closure.find? constant).getD #[]

def resolveIncludedDeclaration (env : Environment) (moduleName selector : String) : Option ConstantInfo := do
  let moduleIdx ← env.getModuleIdx? moduleName.toName
  let selected := env.header.moduleData[moduleIdx]!.constNames.filterMap fun name => do
    let info ← env.find? name
    if name.getString! == selector && includeInStatement name info then some info else none
  if selected.size == 1 then selected[0]? else none

def closedExpression (expression : Expr) : Bool :=
  !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars

/-- This checks one declared relationship, not the usefulness or classification of a module. -/
def closedNegation (env : Environment) (input : ModuleInput) (utility : UtilityInput) : IO Bool := do
  if utility.resultModule != input.moduleName || utility.claimGid == utility.resultGid then return false
  let some (.defnInfo claim) := resolveIncludedDeclaration env utility.claimModule utility.claimSelector
    | return false
  let some (.thmInfo result) := resolveIncludedDeclaration env utility.resultModule utility.resultSelector
    | return false
  if !claim.levelParams.isEmpty || !result.levelParams.isEmpty
      || !closedExpression claim.type || !closedExpression claim.value
      || !closedExpression result.type || !closedExpression result.value then return false
  let check : MetaM Bool := Meta.withTransparency .all do
    if !(← Meta.isDefEq claim.type (mkSort .zero)) then return false
    let expected := mkApp (mkConst ``Not) (mkConst claim.name)
    if !(← Meta.isDefEq result.type expected) then return false
    return ← Meta.isDefEq (← Meta.inferType result.value) expected
  return (← check.run' |>.toIO { fileName := "<utility-refutation>", fileMap := default } { env }).1

def inspectModule (env : Environment) (cache : IO.Ref AxiomClosureState)
    (materialSpool : System.FilePath) (materialCounter : IO.Ref Nat)
    (utilities : Array UtilityInput)
    (input : ModuleInput) : IO ModuleReport := do
  let moduleName := input.moduleName.toName
  let some moduleIdx := env.getModuleIdx? moduleName
    | throw <| IO.userError s!"module not loaded: {input.moduleName}"
  let moduleData := env.header.moduleData[moduleIdx]!
  let environment := env.setExporting false
  let names := moduleData.constNames.qsort fun left right => encodeName left < encodeName right
  let declarations ← names.mapM fun name => do
    let some info := environment.find? name
      | throw <| IO.userError s!"declaration missing: {name}"
    let axioms ← collectAxiomsShared environment cache name
    let statement := encodeStatement info
    let materialIndex ← materialCounter.get
    materialCounter.set (materialIndex + 1)
    let materialFile := s!"{materialIndex}.statement"
    IO.FS.writeFile (materialSpool / materialFile) statement
    return {
      axioms := sortedUnique (axioms.map Name.toString)
      includeInStatement := includeInStatement name info
      kind := kindOf info
      materialFile
      name := name.toString
      nameKey := encodeName name
    }
  let obligations := utilities.filter (·.modulePath == input.sourcePath)
  if obligations.size > 1 then
    throw <| IO.userError s!"duplicate utility obligation: {input.sourcePath}"
  let refutation ← match obligations[0]? with
    | none => pure none
    | some utility => do
      let valid ← closedNegation environment input utility
      pure <| some {
        claimGid := utility.claimGid
        claimSourcePath := utility.claimSourcePath
        claimSourceSha256 := utility.claimSourceSha256
        resultGid := utility.resultGid
        isClosedNegation := valid
      }
  return {
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
  | "--output" :: output :: "--material-spool" :: materialSpool :: rest => do
      let (utilityInput, rest) := match rest with
        | "--utility-input" :: path :: tail => (some (System.FilePath.mk path), tail)
        | _ => (none, rest)
      let inputs ← parseModuleInputs rest
      if inputs.isEmpty then
        throw "at least one module is required"
      return (output, materialSpool, utilityInput,
        inputs.qsort (fun left right => left.moduleName < right.moduleName))
  | _ => .error
      "usage: Inspector.lean --output FILE --material-spool DIR [--utility-input FILE] MODULE SOURCE_PATH SOURCE_SHA256 [...]"

/-- Read statement material only for requested Names in collision modules. No
project module is imported: ModuleData parts are read and released one at a time. -/
@[noinline] private unsafe def emitStatementIdentities (moduleName : String)
    (paths : Array String) (keys : Std.HashSet String) (out : IO.FS.Stream) :
    IO (Array CompactedRegion) := do
  let parts ← readModuleDataParts (paths.map System.FilePath.mk)
  let mut regions := #[]
  for h : i in [:parts.size] do
    let (data, region) := parts[i]
    for info in data.constants do
      let nameKey := encodeName info.name
      unless keys.contains nameKey do continue
      out.putStrLn (Json.mkObj [("module", toJson moduleName),
        ("part", toJson (#["base", "server", "private"][i]!)),
        ("name_key", toJson nameKey),
        ("kind", toJson (if info.isTheorem then "theorem" else "other")),
        ("statement_material", toJson (encodeStatement info))]).compress
    regions := regions.push region
  return regions

private unsafe def statementIdentities (manifest request : String) : IO Unit := do
  let modules ← IO.ofExcept <| (Json.parse (← IO.FS.readFile manifest) >>= fromJson?
    (α := Array (String × Array String)))
  let input ← IO.ofExcept <| Json.parse (← IO.FS.readFile request)
  let rows ← IO.ofExcept <| input.getObjValAs? (Array (Array String)) "keys"
  let keys := Std.HashSet.ofArray (rows.map (·[1]!))
  let out ← IO.getStdout
  for (moduleName, paths) in modules do
    unless paths.size ≥ 1 && paths.size ≤ 3 do
      throw <| IO.userError "expected a prefix of olean parts"
    let regions ← emitStatementIdentities moduleName paths keys out
    for region in regions.reverse do region.free
    out.flush

/-- Detach one module's used constants before freeing its compacted regions.
Names use Inspector's existing constructor-preserving encoding. -/
@[noinline] private unsafe def emitDependencies (moduleName : String) (paths : Array String)
    (bodies : Bool) (out : IO.FS.Stream) : IO (Array CompactedRegion) := do
  let parts ← readModuleDataParts (paths.map System.FilePath.mk)
  let mut regions := #[]
  for h : i in [:parts.size] do
    let (data, region) := parts[i]
    out.putStrLn (Json.mkObj [("module", toJson moduleName),
      ("part", toJson (#["base", "server", "private"][i]!)),
      ("imports", toJson (data.imports.map (·.module.toString)))]).compress
    if bodies then
      for info in data.constants do
        let (types, values) := declarationDependencyParts info
        out.putStrLn (Json.mkObj [("name", toJson (encodeName info.name)),
          ("kind", toJson (kindOf info)),
          ("value", toJson (values.map (·.map encodeName))),
          ("type", toJson (types.map encodeName))]).compress
    else
      for name in data.constNames do
        out.putStrLn (Json.mkObj [("name", toJson (encodeName name))]).compress
    regions := regions.push region
  return regions

private unsafe def dependencies (manifest destination mode : String) : IO Unit := do
  unless mode == "bodies" || mode == "names" do
    throw <| IO.userError "expected bodies or names"
  let modules ← IO.ofExcept <| (Json.parse (← IO.FS.readFile manifest) >>= fromJson?
    (α := Array (String × Array String)))
  let out ← if destination == "-" then IO.getStdout else
    IO.FS.Stream.ofHandle <$> IO.FS.Handle.mk destination .write
  for (moduleName, paths) in modules do
    unless paths.size ≥ 1 && paths.size ≤ 3 do
      throw <| IO.userError "missing_olean_part"
    let regions ← emitDependencies moduleName paths (mode == "bodies") out
    for region in regions.reverse do region.free
    out.flush

unsafe def main (args : List String) : IO Unit := do
  if let ["--dependencies", manifest, destination, mode] := args then
    dependencies manifest destination mode
    return
  if let ["--statement-identities", manifest, request] := args then
    statementIdentities manifest request
    return
  let (output, materialSpool, utilityInput, inputs) ← match parseArguments args with
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
  let moduleNames := sortedUnique (inputs.map (·.moduleName) ++ selectedUtilities.map (·.claimModule))
  let imports := moduleNames.map fun moduleName => { module := moduleName.toName }
  let env ← importModules imports {} (trustLevel := 0)
  let cache ← IO.mkRef ({} : AxiomClosureState)
  let materialCounter ← IO.mkRef 0
  let reports ← inputs.mapM (inspectModule env cache materialSpool materialCounter utilities)
  IO.FS.writeFile output (renderReport reports)
