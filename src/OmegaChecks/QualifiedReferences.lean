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

private partial def signatureNames (stx : Syntax) (inside := false)
    (acc : Array (Option Name × Syntax.Range) := #[]) : Array (Option Name × Syntax.Range) := Id.run do
  let kind := stx.getKind
  let signature := inside || [``Parser.Command.declSig, ``Parser.Command.optDeclSig,
    ``Parser.Command.structFields, ``Parser.Command.ctor, ``Parser.Command.variable].contains kind
  if signature then
    let standard := standardName? stx
    if standard.isSome || stx.isIdent then
      if let some range := stx.getRange? then return acc.push (standard, range)
  return stx.getArgs.foldl (fun a c => signatureNames c signature a) acc

/-- The parsed command syntax excludes imports, comments, string contents and theorem proofs.
The trace-verified .ilean supplies the resolution at this exact source token on this backend. -/
def checkFile (moduleName : Name) (source index : System.FilePath) (official : Bool) : IO Nat := do
  let text ← IO.FS.readFile source
  let ictx := Parser.mkInputContext text source.toString
  let (header, parserState, messages) ← Parser.parseHeader ictx
  let refs ← Server.Ilean.load index
  unless refs.module == moduleName do throw <| IO.userError s!"{index} is for {refs.module}, expected {moduleName}"
  let portUses := refs.references.toList.any fun (id, info) =>
    match id with
    | .const owner _ => owner.toName.getRoot == `OmegaMathlib && !info.usages.isEmpty
    | _ => false
  if (official || !portUses) && !(parserState.pos.extract text text.rawEndPos).contains "OmegaMathlib" then
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
  let tokens := state.commands.foldl (fun acc c => signatureNames c false acc) #[]
  let key := fun (r : Lsp.Range) => (r.start.line, r.start.character, r.end.line, r.end.character)
  let mut locations : Std.HashMap (Nat × Nat × Nat × Nat) (List (Lsp.RefIdent × String)) := {}
  for (id, info) in refs.references.toList do
    for loc in info.usages do
      locations := locations.alter (key loc.range) (fun entries => some ((id, loc.parentDecl) :: entries.getD []))
  let mut count := 0
  for (standard, range) in tokens do
    let pos := ictx.fileMap.utf8RangeToLspRange range
    let refsHere := locations.getD (key pos) []
    let some alias := standard | do
      unless official do
        for (id, parent) in refsHere do
          if let .const owner name := id then
            if owner.toName.getRoot == `OmegaMathlib && !isPrivateName parent.toName then
              let canonical := name.toName.replacePrefix `Omega `OmegaMathlib
              throw <| IO.userError s!"{source}:{pos.start.line+1}:{pos.start.character+1}: {parent} uses {name} from {owner}; qualify this identifier as {canonical}"
      continue
    count := count + 1
    let expected := alias.replacePrefix `OmegaMathlib (if official then .anonymous else `Omega)
    let env := state.commandState.env
    let some idx := env.getModuleIdxFor? expected | throw <| IO.userError s!"unknown standard reference {alias} in {moduleName}"
    let owner := env.header.moduleNames[idx]!
    unless owner.getRoot == (if official then `Mathlib else `OmegaMathlib) do
      throw <| IO.userError s!"{moduleName}: {alias} resolves outside its admitted port: {expected} in {owner}"
    unless refsHere.map Prod.fst == [.const owner.toString expected.toString] do
      throw <| IO.userError s!"{source}:{pos.start.line+1}:{pos.start.character+1}: {alias} requires {expected} in {owner} at this occurrence"
  return count

end OmegaChecks.QualifiedReferences

open OmegaChecks.QualifiedReferences in
unsafe def main (args : List String) : IO Unit := do
  let [backend, path, request] := args | throw <| IO.userError "expected backend, search path and input manifest"
  unless backend == "strict" || backend == "official" do throw <| IO.userError s!"unknown backend {backend}"
  searchPathRef.set (System.SearchPath.parse path)
  let files : Array (Array String) ← IO.ofExcept (Json.parse (← IO.FS.readFile request) >>= fromJson?)
  let mut count := 0
  for row in files do
    let #[name, source, refs] := row | throw <| IO.userError "expected module, source and ilean paths"
    enableInitializersExecution
    count := count + (← checkFile name.toName source refs (backend == "official"))
  IO.println s!"Verified {count} qualified standard references on the {backend} backend."
