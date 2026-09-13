import Lean

/- Current-compiler source queries. No declaration, proof, macro expansion, or initializer
   body from the requested sources is elaborated. Imports are current compiler inputs. -/
open Lean Lean.Parser Lean.Elab Lean.Elab.Frontend

namespace SourceContext

def equality (env : Environment) : Bool := (getTokenTable env).find? "='" |>.isSome

def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
def stringField (j : Json) (key : String) : Except String String :=
  field j key >>= Json.getStr?

def errorJson (messages : MessageLog) : IO Json := do
  for message in messages.toList do
    if message.severity == .error then
      return Json.mkObj [("line", toJson message.pos.line),
        ("column", toJson message.pos.column), ("message", toJson (← message.data.toString))]
  return Json.null

partial def syntaxNames (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId] else stx.getArgs.flatMap syntaxNames

partial def declarationNamespaces (stx : Syntax) : Array Name :=
  if stx.isOfKind ``Parser.Command.declId then
    #[stx[0].getId.getPrefix]
  else if stx.getKind.toString.startsWith "Lean.Parser.Term." ||
      stx.getKind.toString.startsWith "Lean.Parser.Tactic." then #[]
  else stx.getArgs.flatMap declarationNamespaces

/- `Elab.Term.toParserDescr.processSepBy/1` uses separator text as a symbol
   only without an explicit separator parser. `sepBy/1Info.collectTokens`
   combines the element and actual separator parser, excluding that metadata. -/
partial def declarationTokens (stx : Syntax) : Array String :=
  if stx.isOfKind ``Parser.Syntax.sepBy || stx.isOfKind ``Parser.Syntax.sepBy1 then
    declarationTokens stx[1] ++ declarationTokens (if stx[4].isNone then stx[3] else stx[4][1])
  else
    match stx.isStrLit? with
    | some s => #[s.trimAscii.toString]
    | none => stx.getArgs.flatMap declarationTokens

/- Export nested scope facts by running the actual parser scope operation. Its callback
   observes the inner context; the outer context is never substituted for that reading. -/
partial def syntaxFacts (stx : Syntax) (c : ParserContext) : Json := Id.run do
  let start := stx.getPos?.getD 0
  let stop := stx.getTailPos?.getD start
  let mut children : Array Json := #[]
  if stx.isOfKind ``Parser.Command.in && stx[0].isOfKind ``Parser.Command.open then
    children := #[insideOpen stx[0][1] stx[2] c]
  else if stx.isOfKind ``Parser.Command.in && stx[0].isOfKind ``Parser.Command.set_option then
    children := #[insideOption stx[0] stx[2] c]
  else if stx.isOfKind ``Parser.Command.in then
    -- Command.in parses both commands before elaborating either one. Only its
    -- parser-owned open/set_option callbacks above change the second parse context.
    children := #[syntaxFacts stx[0] c, syntaxFacts stx[2] c]
  else if stx.isOfKind ``Parser.Term.open || stx.isOfKind ``Parser.Tactic.open then
    children := #[insideOpen stx[1] stx[3] c]
  else if stx.isOfKind ``Parser.Command.mutual then
    children := stx[1].getArgs.map (syntaxFacts · c)
  else
    for child in stx.getArgs do
      children := children ++ nestedFacts child c
  return Json.mkObj [("start", toJson start.byteIdx), ("end", toJson stop.byteIdx),
    ("kind", toJson stx.getKind.toString), ("namespace", toJson (if c.currNamespace.isAnonymous then "" else c.currNamespace.toString)),
    ("equality", toJson (equality c.env)), ("children", toJson children)]
where
  insideOption (option child : Syntax) (c : ParserContext) : Json :=
    let capture : ParserFn := fun inner s =>
      s.pushSyntax (Syntax.mkStrLit (syntaxFacts child inner).compress)
    let state := withSetOptionFn capture c ((mkParserState c.inputString).pushSyntax option)
    if state.hasError || !state.recoveredErrors.isEmpty || state.stxStack.isEmpty then
      Json.mkObj [("scopeError", toJson (child.getPos?.getD 0).byteIdx)]
    else (Json.parse (state.stxStack.back.isStrLit?.getD "null")).toOption.getD Json.null
  insideOpen (decl child : Syntax) (c : ParserContext) : Json :=
    let capture : ParserFn := fun inner s =>
      s.pushSyntax (Syntax.mkStrLit (syntaxFacts child inner).compress)
    let state := withOpenDeclFnCore decl capture c (mkParserState c.inputString)
    if state.hasError || !state.recoveredErrors.isEmpty || state.stxStack.isEmpty then
      Json.mkObj [("scopeError", toJson (child.getPos?.getD 0).byteIdx)]
    else (Json.parse (state.stxStack.back.isStrLit?.getD "null")).toOption.getD Json.null
  nestedFacts (stx : Syntax) (c : ParserContext) : Array Json :=
    if stx.isOfKind ``Parser.Term.open || stx.isOfKind ``Parser.Tactic.open then
      #[syntaxFacts stx c]
    else stx.getArgs.flatMap (nestedFacts · c)

def commandFacts (input : InputContext) (pmctx : ParserModuleContext) (cmd : Syntax) : Json :=
  let capture : ParserFn := fun c s => s.pushSyntax (Syntax.mkStrLit (syntaxFacts cmd c).compress)
  let state := capture.run input pmctx (getTokenTable pmctx.env) (mkParserState input.inputString)
  (Json.parse (state.stxStack.back.isStrLit?.getD "null")).toOption.getD Json.null

partial def factsHaveError (facts : Json) : Bool :=
  facts == Json.null || (facts.getObjVal? "scopeError").isOk ||
    ((facts.getObjVal? "children" >>= Json.getArr?).toOption.getD #[]).any factsHaveError

def applyBuiltin (cmd : Syntax) : FrontendM Unit := do
  if cmd.isOfKind ``Parser.Command.namespace then
    runCommandElabM <| Command.elabNamespace cmd
  else if cmd.isOfKind ``Parser.Command.section then
    runCommandElabM <| Command.elabSection cmd
  else if cmd.isOfKind ``Parser.Command.end then
    runCommandElabM <| Command.elabEnd cmd
  else if cmd.isOfKind ``Parser.Command.open then
    runCommandElabM <| Command.elabOpen cmd
  else if cmd.isOfKind ``Parser.Command.set_option then
    runCommandElabM <| Command.elabSetOption cmd
  else
    runCommandElabM do
      let ns ← getCurrNamespace
      for name in declarationNamespaces cmd do
        unless name.isAnonymous do modifyEnv (·.registerNamespace (ns ++ name))

inductive AttributeTokenEffect where
  | unchanged
  | unknown

/- Core `simp` and `instance` update simplifier/simproc and instance extensions,
   respectively, without registering parser tokens, for add, erase, or any scope.
   Check their identities in the current imported registry. Do not run elabAttr (which
   expands attribute macros) or apply the handler to unelaborated source targets.
   Other handlers remain unknown; their application time is not an effect guarantee. -/
def attributeTokenEffect (env : Environment) (stx : Syntax) : IO AttributeTokenEffect := do
  let name? := if stx.isOfKind ``Parser.Command.eraseAttr then
      some stx[1].getId.eraseMacroScopes
    else if stx.isOfKind ``Parser.Term.attrInstance then
      if stx[1].isOfKind ``Parser.Attr.simp then some `simp
      else if stx[1].isOfKind ``Parser.Attr.instance then some `instance
      else if stx[1].isOfKind ``Parser.Attr.simple then some stx[1][0].getId.eraseMacroScopes
      else none
    else none
  let some name := name? | return .unknown
  let .ok impl := getAttributeImpl env name | return .unknown
  if name == `simp && impl.ref == ``Meta.simpExtension then return .unchanged
  -- Init-only sources inherit this builtin handler without importing its defining
  -- module. Compare the compiler registry identity, not a generated private name.
  if name == `instance && impl.ref == (← getBuiltinAttributeImpl `instance).ref then
    return .unchanged
  return .unknown

/- Bounded declarative token registration. Only the token is projected; the old
   expansion target is neither inspected as executable code nor evaluated. -/
partial def projectRegistration (cmd : Syntax) (scope? : Option Name := none) : FrontendM Unit := do
  if cmd.isOfKind ``Parser.Command.in then
    -- BuiltinCommand.expandInCmd: section; cmd1; end_local_scope 1; cmd2; end.
    -- Use the compiler's scope operations so globals survive and only cmd1's
    -- local effects end here. Recursion projects effects without elaborating
    -- source bodies or invoking their attribute handlers.
    runCommandElabM do Command.elabSection (← `(command| section))
    projectRegistration cmd[0] scope?
    runCommandElabM <| setDelimitsLocal 1
    projectRegistration cmd[2] scope?
    runCommandElabM do Command.elabEnd (← `(command| end))
    return
  if cmd.isOfKind `Mathlib.Tactic.scopedNS then
    projectRegistration cmd[6] (some cmd[4].getId)
    return
  -- Scope transitions and token effects have the same owner in scanning/replay.
  applyBuiltin cmd
  unless [``Parser.Command.mixfix, ``Parser.Command.notation, ``Parser.Command.syntax].contains cmd.getKind do
    if cmd.isOfKind ``Parser.Command.initialize || cmd.getKind.toString.endsWith ".run_cmd" then
      runCommandElabM <| logErrorAt cmd "source context cannot model a dynamic initializer registration effect"
    else if [``Parser.Command.macro, ``Parser.Command.elab].contains cmd.getKind &&
      (declarationTokens cmd[7]).contains "='" then
      runCommandElabM <| logErrorAt cmd "source context cannot model this equality-token registration effect"
    else if cmd.isOfKind ``Parser.Command.attribute then
      runCommandElabM do
        for attr in cmd[2].getSepArgs do
          match ← attributeTokenEffect (← getEnv) attr with
          | .unchanged => pure ()
          | .unknown => logErrorAt attr "source context cannot determine this attribute registration effect"
    else if !(cmd.getKind.toString.startsWith "Lean.Parser.Command.") then
      runCommandElabM <| logErrorAt cmd "source context cannot determine this custom command registration effect"
    return
  -- Parser.Syntax gives these commands a declaration-item field at index 7
  -- and attrKind at index 2. Expansion terms, attributes and priority expressions
  -- are separate fields; their strings/atoms are not registration facts.
  unless (declarationTokens cmd[7]).contains "='" do return
  runCommandElabM do
    let ns ← getCurrNamespace
    let kind ← if scope?.isSome then pure AttributeKind.scoped
      else liftMacroM <| toAttributeKind cmd[2]
    modifyEnv fun env => parserExtension.addCore env (.token "='") kind (scope?.getD ns)

partial def scan (project : Bool) (rows : Array Json := #[]) (commands : Array Syntax := #[]) :
    FrontendM (Array Json × Json × Array Syntax) := do
  updateCmdPos
  let state ← getCommandState
  let input ← getInputContext
  let ps ← getParserState
  let scope := state.scopes.head!
  let pmctx : ParserModuleContext := { env := state.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
  let (cmd, next, messages) := parseCommand input pmctx ps state.messages
  setParserState next
  setMessages messages
  if messages.hasErrors then return (rows, ← errorJson messages, commands)
  if isTerminalCommand cmd then return (rows, Json.null, commands)
  let facts := commandFacts input pmctx cmd
  if factsHaveError facts then
    return (rows, Json.mkObj [("line", toJson (input.fileMap.toPosition (cmd.getPos?.getD 0)).line),
      ("message", toJson "source context nested parser scope failed")], commands)
  let rows := rows.push facts
  if project then projectRegistration cmd else applyBuiltin cmd
  let messages := (← getCommandState).messages
  if messages.hasErrors then return (rows, ← errorJson messages, commands)
  scan project rows (commands.push cmd)

def readHeader (source path : String) : IO (HeaderSyntax × ModuleParserState × MessageLog) :=
  parseHeader (mkInputContext source path)

def parseSource (source path : String) (env : Environment) (opts : Options)
    (ps : ModuleParserState) (messages : MessageLog) (project := false) :
    IO ((Array Json × Json × Array Syntax) × Frontend.State) :=
  (scan project #[] #[] { inputCtx := mkInputContext source path }).run {
    commandState := Command.mkState env messages opts, parserState := ps, cmdPos := ps.pos }

def replay (commands : Array Syntax) : FrontendM (Array Json × Json) := do
  let mut rows := #[]
  for cmd in commands do
    let state ← getCommandState
    let scope := state.scopes.head!
    let input ← getInputContext
    let pmctx : ParserModuleContext := { env := state.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
    let facts := commandFacts input pmctx cmd
    if factsHaveError facts then
      return (rows, Json.mkObj [("line", toJson (input.fileMap.toPosition (cmd.getPos?.getD 0)).line),
        ("message", toJson "source context nested parser scope failed")])
    rows := rows.push facts
    projectRegistration cmd
    let messages := (← getCommandState).messages
    if messages.hasErrors then return (rows, ← errorJson messages)
  return (rows, Json.null)

def replaySource (commands : Array Syntax) (source path : String) (env : Environment) (opts : Options) :
    IO ((Array Json × Json) × Frontend.State) :=
  (replay commands { inputCtx := mkInputContext source path }).run {
    commandState := Command.mkState env {} opts, parserState := {}, cmdPos := 0 }

unsafe def importHeader (header : HeaderSyntax) (opts : Options) (arts : NameMap ImportArtifacts := {}) :
    IO Environment := do
  enableInitializersExecution
  importModules header.imports opts (trustLevel := 0) (loadExts := true)
    (level := if header.isModule then .exported else .private) (arts := arts)

def options (rows : Array Json) : IO Options := do
  let mut opts : Options := {}
  for row in rows do
    let name := (← IO.ofExcept <| stringField row "name").toName
    let value ← IO.ofExcept <| field row "value"
    match value with
    | .bool b => opts := opts.setBool name b
    | .str s => opts := opts.set name s
    | .num _ => opts := opts.set name (← IO.ofExcept value.getNat?)
    | _ => throw <| IO.userError s!"unsupported option value: {name}"
  return opts

unsafe def interfaces (catalog managed : Array Json) (directory : System.FilePath) (opts : Options)
    (arts : NameMap ImportArtifacts := {}) (visiting : List Name := []) :
    IO (NameMap ImportArtifacts) := do
  let mut arts := arts
  for entry in managed do
    let name := (← IO.ofExcept <| stringField entry "module").toName
    if (arts.find? name).isSome then continue
    if visiting.contains name then throw <| IO.userError s!"cyclic managed source import: {name}"
    let source ← IO.ofExcept <| stringField entry "source"
    let path ← IO.ofExcept <| stringField entry "path"
    let opts ← match (field entry "options" >>= Json.getArr?).toOption with
      | some rows => options rows
      | none => pure opts
    let (header, ps, messages) ← readHeader source path
    if messages.hasErrors then throw <| IO.userError (← errorJson messages).compress
    let dependencies := catalog.filter fun row =>
      (stringField row "module").toOption.any fun dep => header.imports.any (·.module == dep.toName)
    arts ← interfaces catalog dependencies directory opts arts (name :: visiting)
    let env ← importHeader header opts arts
    let ((_, error, _), state) ← parseSource source path (env.setMainModule name) opts ps messages true
    if error != Json.null then throw <| IO.userError s!"{path}: {error.compress}"
    let file := directory / (name.toString ++ ".olean")
    let env := state.commandState.env
    let data ← mkModuleData env
    unless data.constants.isEmpty do throw <| IO.userError "query interface contains declarations"
    writeModule env file
    let oleanParts := if header.isModule then
      #[file, file.withExtension "olean.server", file.withExtension "olean.private"] else #[file]
    let irParts := if header.isModule then #[file.withExtension "ir.sig", file.withExtension "ir"] else #[]
    arts := arts.insert name (.ofArrays #[oleanParts, irParts])
  return arts

unsafe def sourceInterfaces (catalog managed : Array Json) (directory : System.FilePath) (opts : Options)
    (grammarArts : NameMap ImportArtifacts) (arts : NameMap ImportArtifacts := {})
    (visiting : List Name := []) : IO (NameMap ImportArtifacts) := do
  let mut arts := arts
  for entry in managed do
    let name := (← IO.ofExcept <| stringField entry "module").toName
    if (arts.find? name).isSome then continue
    if visiting.contains name then throw <| IO.userError s!"cyclic source import: {name}"
    let source ← IO.ofExcept <| stringField entry "source"
    let path ← IO.ofExcept <| stringField entry "path"
    let opts ← match (field entry "options" >>= Json.getArr?).toOption with
      | some rows => options rows
      | none => pure opts
    let (header, ps, messages) ← readHeader source path
    if messages.hasErrors then throw <| IO.userError s!"{path}: {(← errorJson messages).compress}"
    let dependencies := catalog.filter fun row =>
      (stringField row "module").toOption.any fun dep => header.imports.any (·.module == dep.toName)
    arts ← sourceInterfaces catalog dependencies directory opts grammarArts arts (name :: visiting)
    -- Grammar is from the current compiler and current packages. Source effects are
    -- replayed separately; no old expansion or declaration is ever elaborated.
    let grammar ← importHeader header opts grammarArts
    let ((_, parseError, commands), _) ← parseSource source path grammar opts ps messages true
    if parseError != Json.null then throw <| IO.userError s!"{path}: {parseError.compress}"
    let env ← importHeader header opts arts
    let ((_, error), state) ← replaySource commands source path (env.setMainModule name) opts
    if error != Json.null then throw <| IO.userError s!"{path}: {error.compress}"
    let file := directory / (name.toString ++ ".olean")
    let data ← mkModuleData state.commandState.env
    unless data.constants.isEmpty do throw <| IO.userError "source interface contains declarations"
    writeModule state.commandState.env file
    let oleanParts := if header.isModule then
      #[file, file.withExtension "olean.server", file.withExtension "olean.private"] else #[file]
    let irParts := if header.isModule then #[file.withExtension "ir.sig", file.withExtension "ir"] else #[]
    arts := arts.insert name (.ofArrays #[oleanParts, irParts])
  return arts

unsafe def query (request : Json) (directory : System.FilePath) : IO Json := do
  let source ← IO.ofExcept <| stringField request "source"
  let path ← IO.ofExcept <| stringField request "path"
  let opts ← options (← IO.ofExcept <| (field request "options" >>= Json.getArr?))
  let (header, ps, messages) ← readHeader source path
  if (stringField request "mode").toOption == some "header" then
    return Json.mkObj [("imports", toJson header.imports), ("isModule", toJson header.isModule),
      ("headerEnd", toJson ps.pos.byteIdx), ("error", ← errorJson messages)]
  let mut error ← errorJson messages
  let mut rows := #[]
  let mut initial := false
  let mut opened := false
  let mut count := 0
  if error == Json.null then
    let mode ← IO.ofExcept <| stringField request "mode"
    let mut arts : NameMap ImportArtifacts := {}
    if mode == "projected" || mode == "source" then
      IO.FS.createDirAll directory
      let managed ← IO.ofExcept <| (field request "managed" >>= Json.getArr?)
      let roots := managed.filter fun row =>
        (stringField row "module").toOption.any fun dep => header.imports.any (·.module == dep.toName)
      arts ← interfaces managed roots directory opts
      count := arts.size
    let env ← importHeader header opts arts
    if mode == "source" then
      let managed ← IO.ofExcept <| (field request "managed" >>= Json.getArr?)
      let external ← IO.ofExcept <| (field request "sourceModules" >>= Json.getArr?)
      let catalog := managed ++ external
      let roots := catalog.filter fun row =>
        (stringField row "module").toOption.any fun dep => header.imports.any (·.module == dep.toName)
      let sourceDirectory := directory / "source"
      IO.FS.createDirAll sourceDirectory
      let sourceArts ← sourceInterfaces catalog roots sourceDirectory opts arts
      let sourceEnv ← importHeader header opts sourceArts
      let ((_, parseError, commands), _) ← parseSource source path env opts ps messages true
      if parseError != Json.null then
        return Json.mkObj [("error", parseError)]
      let ((sourceRows, failure), _) ← replaySource commands source path sourceEnv opts
      return Json.mkObj [("imports", toJson header.imports), ("isModule", toJson header.isModule),
        ("headerEnd", toJson ps.pos.byteIdx), ("initialEquality", toJson (equality sourceEnv)),
        ("openedEquality", toJson (equality (parserExtension.activateScoped sourceEnv `FirstOrder))),
        ("commands", toJson sourceRows), ("error", failure), ("queryModules", toJson sourceArts.size),
        ("projectedDeclarations", toJson (0 : Nat)), ("elaboratedDeclarations", toJson (0 : Nat))]
    initial := equality env
    opened := equality (parserExtension.activateScoped env `FirstOrder)
    let ((commands, failure, _), _) ← parseSource source path env opts ps messages true
    rows := commands
    error := failure
  return Json.mkObj [("imports", toJson header.imports), ("isModule", toJson header.isModule),
    ("headerEnd", toJson ps.pos.byteIdx), ("initialEquality", toJson initial),
    ("openedEquality", toJson opened), ("commands", toJson rows), ("error", error),
    ("queryModules", toJson count), ("projectedDeclarations", toJson (0 : Nat)),
    ("elaboratedDeclarations", toJson (0 : Nat))]

end SourceContext

unsafe def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let request ← IO.ofExcept <| Json.parse (← IO.FS.readFile args.head!)
  let result ← match request with
    | .arr requests => do
      let mut results := #[]
      for request in requests do
        let directory := (System.FilePath.mk args[1]!) / toString results.size
        results := results.push (← SourceContext.query request directory)
      pure (Json.arr results)
    | _ => SourceContext.query request args[1]!
  IO.println result.compress
