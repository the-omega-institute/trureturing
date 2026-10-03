import Lean
import Lean.Elab.Import

namespace LeanInformationAudit.RegMigration
open Lean Elab Command

private def spanJson (source : String) (stx : Syntax) : Except String Json := do
  let some range := stx.getRange? | throw "RM-SYNTAX-MISSING-SPAN"
  let start := range.start.byteIdx
  let stop := range.stop.byteIdx
  let some text := String.fromUTF8? (source.toUTF8.extract start stop)
    | throw "RM-SYNTAX-UTF8-SPAN"
  return Json.mkObj [("start", toJson start), ("end", toJson stop), ("text", Json.str text)]

/-- Only grammar-inserted optional/list groups are flattened. Terms remain opaque. -/
private partial def grammarItems (stx : Syntax) : Array Syntax :=
  if stx.getKind == nullKind then stx.getArgs.flatMap grammarItems
  else #[stx]

private def token (stx : Syntax) : String :=
  if stx.isAtom then stx.getAtomVal.trimAscii.toString else ""

private def isRegistration (stx : Syntax) : Bool :=
  let name := stx.getKind.toString
  name.startsWith "LeanInformationAudit.registerInformation" ||
    name.startsWith "LeanInformationAudit.informationTheorem"

private def isTemplate (stx : Syntax) : Bool :=
  #[`LeanInformationAudit.command__, `LeanInformationAudit.«command__Constructors_[_,,]»].contains
    stx.getKind

private def variant (stx : Syntax) : String :=
  let kind := stx.getKind.toString
  if kind.contains "FiniteSource" then "finite-source"
  else if kind.contains "Source" then "source"
  else if kind.startsWith "LeanInformationAudit.informationTheorem" then "native"
  else if kind.contains "Occurrence" then "occurrence"
  else if kind.contains "Via" then "forward"
  else "legacy"

private def registrationSlots (source : String) (stx : Syntax) : Except String Json := do
  let args := stx.getArgs.flatMap grammarItems
  let mut slots : List (String × Json) := []
  let add (name : String) (item : Syntax) : Except String (String × Json) :=
    return (name, ← spanJson source item)
  if args.size < 2 then throw "RM-SYNTAX-REGISTRATION-SHAPE"
  slots := slots.concat (← add "theorem" args[1]!)
  for index in [:args.size] do
    let word := token args[index]!
    let some next := args[index + 1]? | continue
    let addSlot (name : String) : Except String (List (String × Json)) :=
      return slots.concat (← add name next)
    match word with
    | "in" => slots ← addSlot "arena"
    | "object_arena" => slots ← addSlot "object_arena"
    | "catalog" => slots ← addSlot "catalog"
    | "primitives" => slots ← addSlot "primitive"
    | "variation" => slots ← addSlot "variation"
    | "sensitivity" => slots ← addSlot "sensitivity"
    | "output_evidence" => slots ← addSlot "output_evidence"
    | "realizes" => slots ← addSlot "source_record"
    | "realization" =>
        if next.getKind == `LeanInformationAudit.inlineInformationRealization then
          slots := slots.concat (← add "inline_actual" next[1])
          slots := slots.concat (← add "inline_proof" next[3])
        else if next.getKind == `LeanInformationAudit.namedInformationRealization then
          slots := slots.concat (← add "realization" next[0])
        else throw "RM-SYNTAX-REALIZATION-SHAPE"
    | "via" =>
        let previous := (args[index - 1]?).map token |>.getD ""
        if previous == "readout" then
          let some value := args[index + 2]? | throw "RM-SYNTAX-READOUT-SHAPE"
          slots := slots.concat (← add "readout" value)
        else if previous == "finite" then slots ← addSlot "finite_bridge"
        else slots ← addSlot "via_descriptor"
    | "from" =>
        let isSource := token next == "source"
        let some value := args[index + (if isSource then 3 else 2)]?
          | throw "RM-SYNTAX-ESCAPE-SHAPE"
        slots := slots.concat (← add (if isSource then "escape_from_source" else "escape_from") value)
    | "continues" =>
        let some value := args[index + 2]? | throw "RM-SYNTAX-CONTINUATION-SHAPE"
        let value := if value.getKind == `LeanInformationAudit.escapeCertifiedContinuation then
            value[0] else value
        slots := slots.concat (← add "continuation" value)
    | ":" => slots ← addSlot "target_type"
    | ":=" => slots ← addSlot "native_proof"
    | _ => pure ()
  return Json.mkObj slots

private partial def identifiers (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId] else stx.getArgs.flatMap identifiers

private def templateSlots (source : String) (stx : Syntax) : Except String (Json × Json) := do
  let args := stx.getArgs.flatMap grammarItems
  let mut slots := [("name", ← spanJson source args[1]!)]
  let mut constructors : Array Name := #[]
  for index in [:args.size] do
    if token args[index]! == "constructors" then
      let some value := args[index + 1]? | throw "RM-SYNTAX-TEMPLATE-VERSION"
      slots := slots.concat ("version", ← spanJson source value)
    if token args[index]! == "[" then
      let mut close := index + 1
      while close < args.size && token args[close]! != "]" do
        if args[close]!.isIdent then
          slots := slots.concat (s!"constructor_{constructors.size}", ← spanJson source args[close]!)
        constructors := constructors ++ identifiers args[close]!
        close := close + 1
      if close == args.size then throw "RM-SYNTAX-TEMPLATE-CONSTRUCTORS"
      let info := SourceInfo.synthetic (args[index]!.getPos?.getD 0)
        (args[close]!.getTailPos?.getD 0) true
      slots := slots.concat ("constructors", ← spanJson source (Syntax.node info nullKind #[]))
  return (Json.mkObj slots, Json.arr (constructors.map fun name => Json.str name.toString))

private partial def termHead (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Term.paren then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.explicit then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.explicitUniv then termHead stx[0]
  else stx

private partial def catalogArguments (stx : Syntax) : Array Syntax := Id.run do
  if stx.isOfKind ``Parser.Term.app then
    let args := stx.getArgs.flatMap grammarItems
    if args.size >= 2 then
      let head := termHead args[0]!
      if head.isIdent && #[`RootCatalogs.declare, `LeanInformationAudit.RootCatalogs.declare,
          `_root_.LeanInformationAudit.RootCatalogs.declare].contains head.getId then
        return #[args[1]!]
  return stx.getArgs.flatMap catalogArguments

private partial def rootFields (source : String) (stx : Syntax) : Except String (List (String × Json)) := do
  let mut result := []
  if stx.isOfKind ``Parser.Term.structInstField then
    let some field := stx[0].find? (·.isIdent) | return []
    let some definition := stx.find? (·.isOfKind ``Parser.Term.structInstFieldDef) | return []
    let value := definition.getArgs.back!
    let key := match field.getId.toString with
      | "rootId" => "root_id"
      | "expected" => "expected"
      | "source" => "source"
      | "baseline" => "baseline"
      | "companionPrefix" => "companion_prefix"
      | _ => ""
    if key != "" then result := [(key, ← spanJson source value)]
    return result
  for child in stx.getArgs do result := result ++ (← rootFields source child)
  return result

private partial def openNamespaces (stx : Syntax) : Array (Name × Bool) :=
  if stx.isOfKind ``Parser.Command.openSimple then
    stx[0].getArgs.map (fun id => (id.getId, true))
  else if stx.isOfKind ``Parser.Command.openScoped then
    stx[1].getArgs.map (fun id => (id.getId, false))
  else stx.getArgs.flatMap openNamespaces

private def declarationNames (ns : Name) (stx : Syntax) : Array Name := Id.run do
  unless stx.isOfKind ``Parser.Command.declaration do return #[]
  let some id := stx[1].find? (·.isOfKind ``Parser.Command.declId) | return #[]
  unless id[0].isIdent do return #[]
  let name := id[0].getId
  return #[if (`_root_).isPrefixOf name then name.replacePrefix `_root_ .anonymous else ns ++ name]

private partial def companionPrefix (name : Name) : Option Name :=
  match name with
  | .anonymous => none
  | .num parent _ => companionPrefix parent
  | .str parent word =>
    if word == "__information_unit" || word == "__primitive_realization" then some name
    else companionPrefix parent

private def nameComponents : Name → Array Json
  | .anonymous => #[]
  | .str parent word => nameComponents parent |>.push (Json.str word)
  | .num parent value => nameComponents parent |>.push (toJson value)

private partial def companionIdentifiers (source : String) (stx : Syntax) : Except String (Array Json) := do
  if stx.isOfKind ``Parser.Term.quot then return #[]
  if stx.isIdent then
    let some name := companionPrefix stx.getId | return #[]
    let span ← spanJson source stx
    return #[Json.mkObj [("name", Json.str name.toString),
      ("name_components", Json.arr (nameComponents name)),
      ("identifier", Json.str stx.getId.toString),
      ("start", ← span.getObjVal? "start"), ("end", ← span.getObjVal? "end"),
      ("text", ← span.getObjVal? "text")]]
  stx.getArgs.foldlM (fun found child => return found ++ (← companionIdentifiers source child)) #[]

private def openDeclJson : OpenDecl → Json
  | .simple name exceptions => Json.mkObj [("kind", Json.str "simple"),
      ("namespace", Json.str name.toString),
      ("namespace_components", Json.arr (nameComponents name)),
      ("exceptions", Json.arr (exceptions.toArray.map fun name => Json.str name.toString))]
  | .explicit name declaration => Json.mkObj [("kind", Json.str "explicit"),
      ("name", Json.str name.toString), ("declaration", Json.str declaration.toString),
      ("name_components", Json.arr (nameComponents name)),
      ("declaration_components", Json.arr (nameComponents declaration))]

private partial def commandJson (source : String) (ns : Name) (opens : List OpenDecl)
    (stx : Syntax) : Except String (Array Json) := do
  if stx.isOfKind ``Parser.Command.in then
    return ← ((stx.getArgs.flatMap grammarItems).filter
      (fun child => !child.isAtom && child.getRange?.isSome)).flatMapM (commandJson source ns opens)
  if stx.isOfKind ``Parser.Command.set_option then
    let nested := (stx.getArgs.flatMap grammarItems).filter (fun child => isRegistration child || isTemplate child ||
      child.isOfKind ``Parser.Command.set_option ||
      child.getKind == `LeanInformationAudit.sealInformationTheoryCmd)
    if !nested.isEmpty then
      return ← nested.flatMapM (commandJson source ns opens)
  let span ← spanJson source stx
  let start ← span.getObjValAs? Nat "start"
  let stop ← span.getObjValAs? Nat "end"
  let mut category := "context"
  let mut form := ""
  let mut slots := Json.mkObj []
  let mut constructors := Json.arr #[]
  if isRegistration stx then
    category := "registration"
    form := variant stx
    slots ← registrationSlots source stx
  else if isTemplate stx then
    category := "template"
    let data ← templateSlots source stx
    slots := data.1
    constructors := data.2
  else if stx.getKind == `LeanInformationAudit.sealInformationTheoryCmd then
    category := "seal"
  else
    let roots := catalogArguments stx
    if roots.size > 1 then throw "RM-SYNTAX-DUPLICATE-ROOT-CALL"
    if let some contract := roots[0]? then
      category := "root"
      form := if (termHead contract).isIdent then "root-reference" else "root-literal"
      slots := Json.mkObj <| [("root_contract", ← spanJson source contract)] ++
        (← rootFields source contract)
    else if stx.getKind.toString.contains "notation" then category := "notation"
  return #[Json.mkObj [
    ("kind", Json.str category), ("syntax_kind", Json.str stx.getKind.toString),
    ("variant", Json.str form), ("start", toJson start), ("end", toJson stop),
    ("namespace", Json.str (if ns.isAnonymous then "" else ns.toString)), ("slots", slots), ("constructors", constructors),
    ("namespace_components", Json.arr (nameComponents ns)),
    ("open_decls", Json.arr (opens.toArray.map openDeclJson)),
    ("companion_identifiers", Json.arr (← companionIdentifiers source stx)),
    ("declared_names", Json.arr ((declarationNames ns stx).map fun name => Json.str name.toString))]]

/-- Each environment comes only from the source header's imports. No source command is elaborated. -/
private def parseFile (repo : System.FilePath) (path : String) : IO Json := do
  let source ← IO.FS.readFile (repo / path)
  let input := Parser.mkInputContext source path
  let (header, initial, messages) ← Parser.parseHeader input
  if messages.hasErrors then throw <| IO.userError s!"RM-SYNTAX-HEADER: {path}"
  let imports := Elab.headerToImports header
  unsafe enableInitializersExecution
  let mut env ← importModules imports {} (loadExts := true)
  let mut state := initial
  let mut ns := Name.anonymous
  let mut opens : List OpenDecl := []
  let mut scopes : List (Name × Environment × List OpenDecl) := []
  let mut commands := #[]
  repeat
    let (stx, next, messages) := Parser.parseCommand input
      { env, options := {}, currNamespace := ns, openDecls := opens } state {}
    if messages.hasErrors then
      let errors ← messages.toList.mapM fun message => message.data.toString
      throw <| IO.userError s!"RM-SYNTAX-PARSE: {path}: {errors}"
    if Parser.isTerminalCommand stx then break
    if next.pos == state.pos then throw <| IO.userError s!"RM-SYNTAX-PROGRESS: {path}"
    match commandJson source ns opens stx with
    | .error error => throw <| IO.userError s!"{error}: {path}"
    | .ok entries => commands := commands ++ entries
    if stx.isOfKind ``Parser.Command.namespace then
      scopes := (ns, env, opens) :: scopes
      let name := stx[1].getId
      ns := if (`_root_).isPrefixOf name then name.replacePrefix `_root_ .anonymous else ns ++ name
      env := Parser.parserExtension.activateScoped env ns
    else if stx.isOfKind ``Parser.Command.section then
      scopes := (ns, env, opens) :: scopes
    else if stx.isOfKind ``Parser.Command.end then
      let previous :: rest := scopes | throw <| IO.userError s!"RM-SYNTAX-SCOPE: {path}"
      ns := previous.1
      env := previous.2.1
      opens := previous.2.2
      scopes := rest
    if stx.isOfKind ``Parser.Command.open then
      for (name, simple) in openNamespaces stx do
        for resolved in ResolveName.resolveNamespace env ns opens name do
          env := Parser.parserExtension.activateScoped env resolved
          if simple then opens := .simple resolved [] :: opens
    state := next
  return Json.mkObj [("path", Json.str path), ("source_text", Json.str source),
    ("commands", Json.arr commands),
    ("imports", Json.arr (imports.map fun item => Json.str item.module.toString))]

/-- Each source uses a separate process and exactly its header's imports. -/
def parseManifest (executable : String) (manifest : String) (output : String) : IO Unit := do
  let input ← IO.FS.readFile manifest
  let snapshot ← match Json.parse input with
    | .ok snapshot => pure snapshot
    | .error error => throw <| IO.userError s!"RM-SYNTAX-MANIFEST: {error}"
  let files ← match snapshot.getObjValAs? (Array Json) "files" with
    | .ok files => pure files
    | .error error => throw <| IO.userError s!"RM-SYNTAX-MANIFEST-FILES: {error}"
  let repo := (snapshot.getObjValAs? String "repo").toOption.getD "."
  let jobs := (snapshot.getObjValAs? Nat "jobs").toOption.getD 4
  unless jobs > 0 && jobs <= 8 do throw <| IO.userError "RM-SYNTAX-JOBS: expected 1..8"
  let files := files.qsort fun left right =>
    (left.getObjValAs? String "path").toOption.getD "" <
      (right.getObjValAs? String "path").toOption.getD ""
  let mut result := #[]
  let parseOne (file : Json) : IO Json := do
    let path ← match file.getObjValAs? String "path" with
      | .ok path => pure path
      | .error error => throw <| IO.userError s!"RM-SYNTAX-MANIFEST-PATH: {error}"
    let child ← IO.Process.output { cmd := executable, args := #["--one", repo, path] }
    unless child.exitCode == 0 do
      throw <| IO.userError s!"RM-SYNTAX-CHILD: {path}: {child.exitCode}: {child.stderr}"
    let file ← match Json.parse child.stdout with
      | .ok file => pure file
      | .error error => throw <| IO.userError s!"RM-SYNTAX-CHILD-JSON: {path}: {error}"
    return file
  let mut offset := 0
  while offset < files.size do
    let batch := files.extract offset (offset + jobs)
    let tasks ← batch.mapM fun file => IO.asTask (parseOne file)
    let outcomes := tasks.map (·.get)
    for outcome in outcomes do
      match outcome with
      | .ok file => result := result.push file
      | .error error => throw error
    offset := offset + jobs
  IO.FS.writeFile output <|
    (Json.mkObj [("schema", Json.str "reg-migration-syntax-v1"), ("files", Json.arr result)]).compress ++ "\n"

def parserMain (args : List String) : IO UInt32 := do
  try
    match args with
    | ["--one", repo, path] =>
      initSearchPath (← findSysroot)
      IO.println (← parseFile repo path).compress
      return 0
    | ["--manifest", manifest, output] =>
      parseManifest (← IO.appPath).toString manifest output
      return 0
    | _ =>
      IO.eprintln "RM-SYNTAX-USAGE: --manifest MANIFEST OUTPUT | --one REPO PATH"
      return 2
  catch error =>
    IO.eprintln error.toString
    return 1

syntax (name := regMigrationParse) "#reg_migration_parse " str str : command

elab_rules : command
  | `( #reg_migration_parse $manifest:str $output:str ) => do
    let input ← liftIO <| IO.FS.readFile manifest.getString
    let snapshot ← ofExcept <| Json.parse input
    let executable ← ofExcept <| snapshot.getObjValAs? String "parser_executable"
    liftIO <| parseManifest executable manifest.getString output.getString

end LeanInformationAudit.RegMigration

def main (args : List String) : IO UInt32 :=
  LeanInformationAudit.RegMigration.parserMain args
