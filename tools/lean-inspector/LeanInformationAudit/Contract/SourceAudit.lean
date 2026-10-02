import Lean

namespace LeanInformationAudit.Contract.SourceAudit
open Lean

def heads : Array Name := #[
  `LeanInformationAudit.Contract.Registration,
  `LeanInformationAudit.Contract.TemplateEnrollment,
  `LeanInformationAudit.Contract.RootCatalog,
  `LeanInformationAudit.Contract.ExpectedDeclaration,
  `LeanInformationAudit.Contract.Seal]

/-- Inspect dependency syntax to detect aliases and wrappers; never normalize it. -/
def scanContract (env : Environment) (e : Expr) (unrelated : NameSet := {})
    : Bool × NameSet := Id.run do
  let mut pending := e.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if heads.contains name then return (true, unrelated)
    if seen.contains name || unrelated.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ value.getUsedConstants
      if let .inductInfo d := info then pending := pending ++ d.ctors.toArray
  return (false, seen.toArray.foldl (fun cache name => cache.insert name) unrelated)

def containsContract (env : Environment) (e : Expr) : Bool :=
  (scanContract env e).1

partial def termHead (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Term.app then termHead stx[0]
  else if stx.isOfKind ``Parser.Term.explicit then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.explicitUniv then termHead stx[0]
  else stx

def isHeadSpelling (stx : Syntax) (head : Name) : Bool :=
  stx.isIdent && #[head, `Contract ++ head.getString!.toName,
    `_root_ ++ head, `_root_.Contract ++ head.getString!.toName].contains stx.getId

def audit (command : Syntax) (head : Name) : Except String Unit := do
  unless command.isOfKind ``Parser.Command.declaration do
    throw "contract.discovery:source_declaration"
  let mods := command[0]
  let decl := command[1]
  if (mods.find? (fun s => s.isAtom && s.getAtomVal == "unsafe")).isSome then
    throw "contract.discovery:unsafe"
  if decl.isOfKind ``Parser.Command.instance then throw "contract.discovery:instance"
  if decl.isOfKind ``Parser.Command.opaque then throw "contract.discovery:opaque"
  unless decl.isOfKind ``Parser.Command.definition do throw "contract.discovery:not_def"
  let sig := decl[2]
  unless sig[0].getArgs.isEmpty do throw "contract.discovery:term_parameters"
  let type := sig[1][0][1]
  if type.isOfKind ``Parser.Term.forall || type.isOfKind ``Parser.Term.arrow then
    throw "contract.discovery:forall"
  unless isHeadSpelling (termHead type) head do throw "contract.discovery:type_alias_or_wrapper"
  let rhs := decl[3]
  unless rhs.isOfKind ``Parser.Command.declValSimple do
    throw "contract.discovery:structure_literal"
  let body := rhs[1]
  if body.isOfKind ``Parser.Term.fun then throw "contract.discovery:lambda"
  unless body.isOfKind ``Parser.Term.structInst do
    throw "contract.discovery:forwarding_or_computed"
  -- Structure update is forwarding even if its compiled value eta-expands.
  unless body[1].getArgs.isEmpty do throw "contract.discovery:structure_update"

structure Entry where
  command : Syntax
  sourceName : Option Name
  start : String.Pos.Raw
  stop : String.Pos.Raw

/-- Examples emit no named constant; every other author declaration belongs
to the source inventory, independently of its result-type spelling. -/
def hasInventory (command : Syntax) : Bool :=
  command.isOfKind ``Parser.Command.declaration &&
    !command[1].isOfKind ``Parser.Command.example

private def declarationName (ns : Name) (command : Syntax) : Option Name := do
  guard (command.isOfKind ``Parser.Command.declaration)
  let id ← command[1].find? (·.isOfKind ``Parser.Command.declId)
  guard id[0].isIdent
  let name := id[0].getId
  return if (`_root_).isPrefixOf name then name.replacePrefix `_root_ .anonymous else ns ++ name

private partial def declarations (command : Syntax) : Array Syntax :=
  if command.isOfKind ``Parser.Command.declaration then #[command]
  else if command.isOfKind ``Parser.Command.mutual ||
      command.isOfKind ``Parser.Command.set_option ||
      command.isOfKind ``Parser.Command.in then
    command.getArgs.flatMap declarations
  else if command.getKind == `null then command.getArgs.flatMap declarations
  else #[]

private partial def openNamespaces (command : Syntax) : Array (Name × Bool) :=
  if command.isOfKind ``Parser.Command.openSimple then
    command[0].getArgs.map (fun id => (id.getId, true))
  else if command.isOfKind ``Parser.Command.openScoped then
    command[1].getArgs.map (fun id => (id.getId, false))
  else command.getArgs.flatMap openNamespaces

/-- Parse every command, so a compiled head filter cannot erase a source entry. -/
def parse (env : Environment) (source : String) (file : String) : IO (Array Entry) := do
  let input := Parser.mkInputContext source file
  let (_, initial, messages) ← Parser.parseHeader input
  if messages.hasErrors then throw <| IO.userError "contract.discovery:source_header"
  let mut state := initial
  let mut entries := #[]
  let mut ns := Name.anonymous
  let mut parserEnv := env
  let mut opens : List OpenDecl := []
  let mut scopes : List (Name × Environment × List OpenDecl) := []
  repeat
    let (command, next, messages) := Parser.parseCommand input
      { env := parserEnv, options := {}, currNamespace := ns, openDecls := opens } state {}
    if messages.hasErrors then
      let details ← messages.toList.mapM fun m => m.data.toString
      throw <| IO.userError s!"contract.discovery:source_parse:{file}:{details}"
    if Parser.isTerminalCommand command then break
    if next.pos == state.pos then throw <| IO.userError "contract.discovery:source_progress"
    let some start := command.getPos? | throw <| IO.userError "contract.discovery:source_range"
    let some stop := command.getTailPos? | throw <| IO.userError "contract.discovery:source_range"
    let authorDeclarations := declarations command
    if authorDeclarations.isEmpty then
      entries := entries.push ⟨command, none, start, stop⟩
    else
      for declaration in authorDeclarations do
        entries := entries.push ⟨declaration, declarationName ns declaration,
          declaration.getPos?.getD start, declaration.getTailPos?.getD stop⟩
    if command.isOfKind ``Parser.Command.namespace then
      scopes := (ns, parserEnv, opens) :: scopes
      ns := ns ++ command[1].getId
      parserEnv := Parser.parserExtension.activateScoped parserEnv ns
    else if command.isOfKind ``Parser.Command.section then
      scopes := (ns, parserEnv, opens) :: scopes
    else if command.isOfKind ``Parser.Command.end then
      let previous :: rest := scopes
        | throw <| IO.userError "contract.discovery:source_scope"
      ns := previous.1
      parserEnv := previous.2.1
      opens := previous.2.2
      scopes := rest
    if command.isOfKind ``Parser.Command.open then
      for (name, simple) in openNamespaces command do
        for resolved in ResolveName.resolveNamespace parserEnv ns opens name do
          parserEnv := Parser.parserExtension.activateScoped parserEnv resolved
          if simple then opens := .simple resolved [] :: opens
    state := next
  return entries

end LeanInformationAudit.Contract.SourceAudit
