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

private partial def claims (stx : Syntax) (inside := false)
    (acc : Array (Name × Syntax.Range) := #[]) : Array (Name × Syntax.Range) := Id.run do
  let kind := stx.getKind
  let signature := inside || [``Parser.Command.declSig, ``Parser.Command.optDeclSig,
    ``Parser.Command.structFields, ``Parser.Command.ctor, ``Parser.Command.variable].contains kind
  if signature then
    if let some n := standardName? stx then
      if let some range := stx.getRange? then return acc.push (n, range)
  return stx.getArgs.foldl (fun a c => claims c signature a) acc

/-- The parsed command syntax excludes imports, comments, string contents and theorem proofs.
The trace-verified .ilean supplies the resolution at this exact source token on this backend. -/
private def checkFile (moduleName : Name) (source index : System.FilePath) (official : Bool) : IO Nat := do
  let text ← IO.FS.readFile source
  let ictx := Parser.mkInputContext text source.toString
  let (header, parserState, messages) ← Parser.parseHeader ictx
  if !(parserState.pos.extract text text.rawEndPos).contains "OmegaMathlib" then return 0
  let opts := ({} : Options).setBool `relaxedAutoImplicit false
  let (env, messages) ← Elab.processHeader header opts messages ictx (mainModule := moduleName)
  let state ← Elab.IO.processCommands ictx parserState (Elab.Command.mkState env messages opts)
  if state.commandState.messages.hasErrors then
    for msg in state.commandState.messages.toList do
      if msg.severity == .error then throw <| IO.userError (← msg.toString)
    throw <| IO.userError s!"failed to recover declaration syntax for {moduleName}"
  let uses := state.commands.foldl (fun acc c => claims c false acc) #[]
  if uses.isEmpty then return 0
  let refs ← Server.Ilean.load index
  unless refs.module == moduleName do throw <| IO.userError s!"{index} is for {refs.module}, expected {moduleName}"
  for (alias, range) in uses do
    let expected := alias.replacePrefix `OmegaMathlib (if official then .anonymous else `Omega)
    let env := state.commandState.env
    let some idx := env.getModuleIdxFor? expected | throw <| IO.userError s!"unknown standard reference {alias} in {moduleName}"
    let owner := env.header.moduleNames[idx]!
    unless owner.getRoot == (if official then `Mathlib else `OmegaMathlib) do
      throw <| IO.userError s!"{moduleName}: {alias} resolves outside its admitted port: {expected} in {owner}"
    let lspRange := ictx.fileMap.utf8RangeToLspRange range
    let resolved := refs.references.toList.filterMap fun (id, uses) =>
      if uses.usages.any (·.range == lspRange) then some id else none
    unless resolved == [.const owner.toString expected.toString] do
      throw <| IO.userError s!"{source}:{lspRange.start.line+1}:{lspRange.start.character+1}: {alias} requires {expected} in {owner} at this occurrence"
  return uses.size

unsafe def run (backend path request : String) : IO Unit := do
  unless backend == "strict" || backend == "official" do throw <| IO.userError s!"unknown backend {backend}"
  enableInitializersExecution
  searchPathRef.set (System.SearchPath.parse path)
  let files : Array (Array String) ← IO.ofExcept (Json.parse (← IO.FS.readFile request) >>= fromJson?)
  let mut count := 0
  for row in files do
    let #[name, source, refs] := row | throw <| IO.userError "expected module, source and ilean paths"
    count := count + (← checkFile name.toName source refs (backend == "official"))
  IO.println s!"Verified {count} qualified standard references on the {backend} backend."

end OmegaChecks.QualifiedReferences
