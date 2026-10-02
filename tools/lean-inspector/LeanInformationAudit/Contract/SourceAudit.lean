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
def containsContract (env : Environment) (e : Expr) : Bool := Id.run do
  let mut pending := e.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if heads.contains name then return true
    if seen.contains name then continue
    seen := seen.insert name
    match env.find? name with
    | some (.defnInfo d) =>
      if d.type.getForallBody.isSort then pending := pending ++ d.value.getUsedConstants
    | some (.opaqueInfo d) =>
      if d.type.getForallBody.isSort then pending := pending ++ d.value.getUsedConstants
    | some (.inductInfo d) =>
      for ctor in d.ctors do
        if let some c := env.find? ctor then pending := pending ++ c.type.getUsedConstants
    | _ => pure ()
  return false

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

/-- Parse every command, so a compiled head filter cannot erase a source entry. -/
def parse (env : Environment) (source : String) (file : String) : IO (Array Entry) := do
  let input := Parser.mkInputContext source file
  let (_, initial, messages) ← Parser.parseHeader input
  if messages.hasErrors then throw <| IO.userError "contract.discovery:source_header"
  let mut state := initial
  let mut entries := #[]
  let mut ns := Name.anonymous
  let mut scopes : List Name := []
  repeat
    let (command, next, messages) := Parser.parseCommand input
      { env, options := {}, currNamespace := ns, openDecls := [] } state {}
    if messages.hasErrors then throw <| IO.userError "contract.discovery:source_parse"
    if Parser.isTerminalCommand command then break
    if next.pos == state.pos then throw <| IO.userError "contract.discovery:source_progress"
    let some start := command.getPos? | throw <| IO.userError "contract.discovery:source_range"
    let some stop := command.getTailPos? | throw <| IO.userError "contract.discovery:source_range"
    let sourceName := if command.isOfKind ``Parser.Command.declaration &&
        command[1][1][0].isIdent then
      some (ns ++ command[1][1][0].getId) else none
    entries := entries.push ⟨command, sourceName, start, stop⟩
    if command.isOfKind ``Parser.Command.namespace then
      scopes := ns :: scopes
      ns := ns ++ command[1].getId
    else if command.isOfKind ``Parser.Command.section then
      scopes := ns :: scopes
    else if command.isOfKind ``Parser.Command.end then
      let previous :: rest := scopes
        | throw <| IO.userError "contract.discovery:source_scope"
      ns := previous
      scopes := rest
    state := next
  return entries

end LeanInformationAudit.Contract.SourceAudit
