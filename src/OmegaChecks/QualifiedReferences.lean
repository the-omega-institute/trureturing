import Lean.Elab.Frontend

/-! Correlate explicitly qualified source references with the compiler's indexed resolutions. -/

open Lean

namespace OmegaChecks.QualifiedReferences

private def standardName? (stx : Syntax) : Option Name := do
  let raw ← match stx with
    | .ident _ _ n _ => some n
    | .atom _ text => some text.toName -- A notation token may shadow an identifier.
    | _ => none
  let name := raw.eraseMacroScopes.replacePrefix `_root_ .anonymous
  guard (name.getRoot == `OmegaMathlib && name != `OmegaMathlib)
  return name

private partial def declarationNames (stx : Syntax) (inSignature := false) (inValue := false)
    (fromValue := false)
    (acc : Array (Syntax × Bool) := #[]) : Array (Syntax × Bool) := Id.run do
  let kind := stx.getKind
  let signature := inSignature || [``Parser.Command.declSig, ``Parser.Command.optDeclSig,
    ``Parser.Command.structFields, ``Parser.Command.ctor, ``Parser.Command.variable].contains kind
  let value := inValue || [``Parser.Command.declValSimple, ``Parser.Command.declValEqns,
    ``Parser.Command.whereStructInst].contains kind
  if (signature || value) && (stx.isIdent || (standardName? stx).isSome) then
    return acc.push (stx, signature || fromValue)
  let inferred := stx.getArgs.any fun child =>
    child.isOfKind ``Parser.Command.optDeclSig && child[1].isNone
  return stx.getArgs.foldl (fun a c => declarationNames c signature value (fromValue || inferred) a) acc

/-- `resolveName'` indexes a qualified constant and any trailing field projections at separate
source ranges. Recover those same prefixes, longest first, without splitting escaped names. -/
private def prefixes (stx : Syntax) : List Syntax :=
  if stx.isIdent then
    (List.range stx.getId.getNumParts).filterMap fun n => (stx.identComponents (some n)).head?
  else [stx]

private structure Port where
  alias : Name
  target : Name
  owner : Name

private structure Ports where
  aliases : NameMap Port := {}
  objects : NameMap Port := {}
  byLeaf : Std.HashMap String (Array Port) := {}

/-- Only alias entries owned by compiled, admitted port modules can confer standard identity. -/
private def admittedPorts (env : Environment) (official : Bool) : IO Ports := do
  let mut ports : Ports := {}
  for mod in env.header.modules do
    unless mod.module.getRoot == `OmegaMathlib do continue
    let some idx := env.getModuleIdx? mod.module | continue
    for (alias, target) in aliasExtension.getModuleEntries env idx do
      unless alias.getRoot == `OmegaMathlib do continue
      let some idx := env.getModuleIdxFor? target | throw <| IO.userError s!"unknown port target {target}"
      let owner := env.header.moduleNames[idx]!
      let expected := alias.replacePrefix `OmegaMathlib (if official then .anonymous else `Omega)
      let expectedOwner := if official then mod.module.replacePrefix `OmegaMathlib `Mathlib else mod.module
      unless owner == expectedOwner && target == expected do
        throw <| IO.userError s!"{alias} in {mod.module} exports {target} from {owner}, expected {expected} from {expectedOwner}"
      let port := { alias, target, owner : Port }
      ports := { ports with aliases := ports.aliases.insert alias port }
      let .str _ leaf := alias | continue
      if (env.find? target).any (!·.isTheorem) then
        ports := { ports with
          objects := ports.objects.insert target port
          byLeaf := ports.byLeaf.alter leaf fun entries => some ((entries.getD #[]).push port) }
  return ports

private def matchingPort? (env catalog : Environment) (ports : Ports) (spelling actual : Name) : Option Name := do
  let .str _ leaf := spelling | none
  let project ← env.find? actual
  (ports.byLeaf.getD leaf #[]).findSome? fun port => do
    let standard ← catalog.find? port.target
    guard (project.levelParams.length == standard.levelParams.length)
    let type := standard.type.instantiateLevelParams standard.levelParams (project.levelParams.map Level.param)
    guard (Kernel.isDefEqGuarded env {} project.type type)
    return port.alias

/-- Follow direct project aliases to their admitted constant, including aliases of aliases. -/
private partial def underlyingPort? (catalog : Environment) (ports : Ports) (project : NameSet)
    (name : Name) : Option Name := do
  if let some port := ports.objects.find? name then return port.alias
  let idx ← catalog.getModuleIdxFor? name
  guard (project.contains catalog.header.moduleNames[idx]!)
  let .defnInfo info ← catalog.find? name | none
  let .const target _ := info.value | none
  underlyingPort? catalog ports project target

private def sensitive? (catalog : Environment) (ports : Ports) (project : NameSet)
    (name : Name) : Option Name := do
  if let some port := underlyingPort? catalog ports project name then return port
  let idx ← catalog.getModuleIdxFor? name
  guard (project.contains catalog.header.moduleNames[idx]!)
  matchingPort? catalog catalog ports name name

/-- Proof definitions are governed by their statements. Inspect the complete value of data and predicates. -/
private def objectValue? (env : Environment) (info : ConstantInfo) : Option Expr := do
  guard (!info.isTheorem && !(Kernel.check env {} info.type).toOption.any (Kernel.isDefEqGuarded env {} (mkSort .zero)))
  info.value? (allowOpaque := true)

private def publicUses (data : ModuleData) (catalog : Environment) (ports : Ports)
    (project : NameSet) : Array Name := Id.run do
  let mut names := #[]
  for name in data.constNames do
    let some info := catalog.find? name | continue
    if isPrivateName info.name || info.name.isInternalOrNum || info.name.hasMacroScopes then continue
    let usesPort := fun (e : Expr) => e.getUsedConstants.any (fun n => (sensitive? catalog ports project n).isSome)
    if usesPort info.type || (objectValue? catalog info).any usesPort then
      names := names.push info.name
  return names

/-- Replace only authenticated identifier tokens with fresh references to the same objects.
A named reference preserves Lean's explicit application, universe and projection syntax. -/
private def checkElaborated (source : System.FilePath) (text : String)
    (commands : Array Syntax) (env : Environment) (opts : Options) (names : Array Name) (isModule : Bool)
    (marks : Array (Lean.Syntax.Range × Name)) (catalog : Environment) (ports : Ports) (project : NameSet) : IO Unit := do
  let prefixName := s!"OmegaCheckedReference{← IO.rand 1 4294967295}".toName
  if text.contains prefixName.toString then throw <| IO.userError "fresh reference marker collision"
  let mut edits : Array (Lean.Syntax.Range × String) := #[]
  let mut markers : NameMap Name := {}
  let mut targets : NameMap Name := {}
  for (span, target) in marks.toList.eraseDups.mergeSort (fun a b => a.1.start.byteIdx ≤ b.1.start.byteIdx) do
    let marker := (targets.find? target).getD (.str prefixName s!"ref{markers.toList.length}")
    unless targets.contains target do
      if env.contains marker || catalog.contains marker then throw <| IO.userError "fresh reference marker collision"
      let some cmd := commands.find? (fun c => c.getRange?.any fun r => r.start ≤ span.start && span.stop ≤ r.stop)
        | throw <| IO.userError s!"unlocated source reference to {target}"
      let some pos := cmd.getPos? | throw <| IO.userError s!"unlocated declaration for {target}"
      let some obj := catalog.find? target | throw <| IO.userError s!"missing compiled object {target}"
      let levels := (List.range obj.numLevelParams).map fun i => s!"omegaLevel{i}"
      let univs := if levels.isEmpty then "" else ".{" ++ String.intercalate "," levels ++ "}"
      let vis := if isModule then "public " else ""
      let decl := s!"\n{vis}noncomputable abbrev _root_.{marker}{univs} := @_root_.{target}{univs}\n"
      edits := edits.push (⟨pos, pos⟩, decl)
      markers := markers.insert marker target
      targets := targets.insert target marker
    edits := edits.push (span, s!"_root_.{marker}")
  let mut marked := text
  for (span, replacement) in edits.toList.mergeSort (fun a b => b.1.start.byteIdx ≤ a.1.start.byteIdx) do
    marked := (0 : String.Pos.Raw).extract marked span.start ++ replacement ++ span.stop.extract marked marked.rawEndPos
  let ictx := Parser.mkInputContext marked source.toString
  let (_, parserState, messages) ← Parser.parseHeader ictx
  let state ← Elab.IO.processCommands ictx parserState (Elab.Command.mkState env messages opts)
  for msg in state.commandState.messages.toList do
    if msg.severity == .error then throw <| IO.userError s!"cannot verify source identity in {source}: {← msg.toString}"
  for name in names do
    let some info := state.commandState.env.find? name | throw <| IO.userError s!"missing source declaration {name}"
    let check (expr original : Expr) := do
      let restored := expr.replace fun e => do
        let .const n levels := e | none
        return .const (← markers.find? n) levels
      unless restored == original do
        throw <| IO.userError s!"{source}: could not recover the compiled expression of {name} after checking its reference positions"
      for n in expr.getUsedConstants do
        if let some standard := sensitive? catalog ports project n then
          throw <| IO.userError s!"{source}: {name} exposes {n} without an explicit source reference to {standard} or its qualified project identity at that occurrence"
    let some original := catalog.find? name | throw <| IO.userError s!"missing compiled declaration {name}"
    check info.type original.type
    if let some value := objectValue? catalog original then
      let some markedValue := info.value? (allowOpaque := true) | throw <| IO.userError s!"missing marked value for {name}"
      check markedValue value

/-- The parsed declaration syntax excludes imports, comments and string contents.
The trace-verified .ilean supplies the resolution at this exact source token on this backend. -/
private def checkFile (moduleName : Name) (source index : System.FilePath)
    (catalog : Environment) (ports : Ports) (project : NameSet) : IO Nat := do
  let text ← IO.FS.readFile source
  let ictx := Parser.mkInputContext text source.toString
  let (header, parserState, messages) ← Parser.parseHeader ictx
  let refs ← Server.Ilean.load index
  unless refs.module == moduleName do throw <| IO.userError s!"{index} is for {refs.module}, expected {moduleName}"
  let relevantRefs := refs.references.toList.any fun (id, info) => Id.run do
    let .const owner name := id | return false
    if info.usages.isEmpty then return false
    if ports.objects.contains name.toName then return true
    unless project.contains owner.toName do return false
    if let .str _ leaf := name.toName then
      if ports.byLeaf.contains leaf then return true
    return info.usages.any fun loc => Id.run do
      let range := ictx.fileMap.lspRangeToUtf8Range loc.range
      let raw := range.start.extract text range.stop
      let .str _ leaf := raw.toName | return false
      return ports.byLeaf.contains leaf
  let (data, _) ← readModuleData (← findOLean moduleName)
  let published := publicUses data catalog ports project
  if published.isEmpty && !relevantRefs && !(parserState.pos.extract text text.rawEndPos).contains "OmegaMathlib" then
    return 0
  let opts := ({} : Options).setBool `relaxedAutoImplicit false
  let (env, messages) ← Elab.processHeader header opts messages ictx (mainModule := moduleName) (leakEnv := true)
  for msg in messages.toList do
    if msg.severity == .error then throw <| IO.userError (← msg.toString)
  let state ← Elab.IO.processCommands ictx parserState (Elab.Command.mkState env messages opts)
  if state.commandState.messages.hasErrors then
    for msg in state.commandState.messages.toList do
      if msg.severity == .error then throw <| IO.userError (← msg.toString)
    throw <| IO.userError s!"failed to recover declaration syntax for {moduleName}"
  let tokens := state.commands.foldl (fun acc c => declarationNames c false false false acc) #[]
  let key := fun (r : Lsp.Range) => (r.start.line, r.start.character, r.end.line, r.end.character)
  let mut locations : Std.HashMap (Nat × Nat × Nat × Nat) (List (Lsp.RefIdent × String)) := {}
  for (id, info) in refs.references.toList do
    for loc in info.usages do
      locations := locations.alter (key loc.range) (fun entries => some ((id, loc.parentDecl) :: entries.getD []))
  let mut count := 0
  let mut marks := #[]
  let sourceEnv := env
  let env := state.commandState.env
  for (token, signature) in tokens do
    -- The compiler indexes dot notation at the field token as well as the receiver.
    let spans := prefixes token ++ (if token.isIdent then token.identComponents.tail else [])
    let parts := spans.filterMap fun stx =>
      stx.getRange?.map fun r => (stx, ictx.fileMap.utf8RangeToLspRange r)
    let some alias := standardName? token | do
      for (part, pos) in parts do
        for (id, parent) in locations.getD (key pos) [] do
          let .const owner name := id | continue
          if isPrivateName parent.toName then continue
          unless signature || (env.find? parent.toName).any (fun info => (objectValue? env info).isSome) do continue
          let actual := name.toName
          if let some port := ports.objects.find? actual then
            if port.owner == owner.toName then
              throw <| IO.userError s!"{source}:{pos.start.line+1}:{pos.start.character+1}: {parent} uses {actual} from {owner}; qualify this identifier as {port.alias}"
          let spelling := part.getId.eraseMacroScopes
          if project.contains owner.toName &&
              (spelling == `_root_ ++ actual || (spelling == actual && !actual.getPrefix.isAnonymous)) &&
              (matchingPort? env catalog ports spelling actual).isSome &&
              (underlyingPort? catalog ports project actual).isNone then
            if let some span := part.getRange? then marks := marks.push (span, actual)
          if project.contains owner.toName && spelling != `_root_ ++ actual &&
              !(spelling == actual && !actual.getPrefix.isAnonymous) then
            if let some candidate := matchingPort? env catalog ports spelling actual then
              throw <| IO.userError s!"{source}:{pos.start.line+1}:{pos.start.character+1}: {parent} uses {actual} from {owner}; qualify the project reference as _root_.{actual} or use the admitted {candidate}"
      continue
    count := count + 1
    let resolved := parts.findSome? fun (stx, pos) => do
      let name ← standardName? stx
      return (← ports.aliases.find? name, pos, stx)
    let some (port, pos, id) := resolved | throw <| IO.userError s!"unknown standard reference {alias} in {moduleName}"
    unless (locations.getD (key pos) []).map Prod.fst == [.const port.owner.toString port.target.toString] do
      throw <| IO.userError s!"{source}:{pos.start.line+1}:{pos.start.character+1}: {alias} requires {port.target} in {port.owner} at this occurrence"
    let inObject := (locations.getD (key pos) []).any fun (_, p) =>
      (env.find? p.toName).any (fun info => !isPrivateName info.name && (objectValue? env info).isSome)
    if (signature || inObject) && ports.objects.contains port.target then
      if let some span := id.getRange? then marks := marks.push (span, port.target)
  unless published.isEmpty do
    checkElaborated source text state.commands sourceEnv opts published data.isModule marks catalog ports project
  return count

end OmegaChecks.QualifiedReferences

open OmegaChecks.QualifiedReferences in
unsafe def main (args : List String) : IO Unit := do
  let backend :: path :: request :: portModules := args | throw <| IO.userError "expected backend, search path and input manifest"
  unless backend == "strict" || backend == "official" do throw <| IO.userError s!"unknown backend {backend}"
  searchPathRef.set (System.SearchPath.parse path)
  let files : Array (Array String) ← IO.ofExcept (Json.parse (← IO.FS.readFile request) >>= fromJson?)
  let mut count := 0
  enableInitializersExecution
  let modules := (portModules ++ files.toList.filterMap (·[0]?)).eraseDups
  let catalog ← importModules (modules.toArray.map fun name => {module := name.toName, importAll := true}) {}
  let ports ← admittedPorts catalog (backend == "official")
  let project := files.foldl (init := ({} : NameSet)) fun names row =>
    if let some name := row[0]? then names.insert name.toName else names
  for row in files do
    let #[name, source, refs] := row | throw <| IO.userError "expected module, source and ilean paths"
    enableInitializersExecution
    count := count + (← checkFile name.toName source refs catalog ports project)
  IO.println s!"Verified {count} qualified standard references on the {backend} backend."
