import Lean

/-!
Reg commands have finite permissions. run_cmd and notation are forbidden;
bare instance/reducible attributes follow the finite attribute grammar.
Contract entries use exact heads and literal metadata. Every other audited
constant is checked for direct interface references in its compiled type/body;
no result-shape, carrier, alias-closure or reduction recognizer is used.
-/

namespace LeanInformationAudit.Contract.SourceAudit
open Lean

def heads : Array Name := #[
  `LeanInformationAudit.Contract.Registration,
  `LeanInformationAudit.Contract.TemplateEnrollment,
  `LeanInformationAudit.Contract.RootCatalog,
  `LeanInformationAudit.Contract.ExpectedDeclaration,
  `LeanInformationAudit.Contract.Seal]

partial def termHead (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Term.paren then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.app then termHead stx[0]
  else if stx.isOfKind ``Parser.Term.explicit then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.explicitUniv then termHead stx[0]
  else stx

/-- Interface ownership, rather than a list of selected type heads, includes
constructors, projections and compiler companions of all Contract interface types.
Implementation helpers live in a different library and grant no interface entry. -/
def interfaceConstant (env : Environment) (name : Name) : Bool :=
  match env.getModuleIdxFor? name with
  | some idx => (`LeanInformationAuditContract).isPrefixOf
      env.header.moduleNames[idx.toNat]!
  | none => false

/-- Direct references only: no transitive dependency scan or normalization.
Lean foldConsts omits the structure name of primitive projection nodes, so those
explicit kernel references are inspected directly in the same type/body trees. -/
def directInterfaceReferences (env : Environment) (info : ConstantInfo) : Array Name := Id.run do
  let mut names := info.getUsedConstantsAsSet.toArray.filter (interfaceConstant env)
  for tree in #[some info.type, info.value? (allowOpaque := true)] do
    if let some tree := tree then
      if let some (.proj name _ _) := tree.find? (fun e => match e with
          | .proj name _ _ => interfaceConstant env name
          | _ => false) then
        unless names.contains name do names := names.push name
  return names

def isHeadSpelling (stx : Syntax) (head : Name) : Bool :=
  !head.isAnonymous && stx.isIdent && #[head, head.getString!.toName, `Contract ++ head.getString!.toName,
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
  unless rhs.getArgs.size == 4 && rhs[2].getArgs.all (·.getArgs.isEmpty) &&
      rhs[3].getArgs.isEmpty && decl[4].getArgs.isEmpty do
    throw "contract.entry:declaration_suffix_not_allowed"
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
  originCommand : Syntax
  authoredNames : Array Name := #[]

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

/-- Nested where/let-rec declarations retain their own source ownership, even
when their compiler names share the enclosing entry prefix. -/
private partial def nestedDeclarationNames (parent : Name) (stx : Syntax) : Array Name :=
  if stx.isOfKind ``Parser.Term.letRecDecl then
    match stx.find? (·.isOfKind ``Parser.Term.letId) >>= (·.find? (·.isIdent)) with
    | some id =>
      let name := parent ++ id.getId
      #[name] ++ stx.getArgs.flatMap (nestedDeclarationNames name)
    | none => stx.getArgs.flatMap (nestedDeclarationNames parent)
  else stx.getArgs.flatMap (nestedDeclarationNames parent)

/-- Authored elaboration has no compiler-equation permission. This includes
named children emitted by term elaboration rather than declaration syntax. -/
def hasAuthoredElaboration (entries : Array Entry) (forbidden : NameSet := {}) : Bool :=
  Id.run do
    let mut seen : Array String.Pos.Raw := #[]
    for entry in entries do
      let pos := entry.originCommand.getPos?.getD entry.start
      if seen.contains pos then continue
      seen := seen.push pos
      if (entry.originCommand.find? fun stx =>
          forbidden.contains stx.getKind ||
          (stx.isAtom && #["by_elab", "run_tac", "run_elab", "run_meta"].contains
            stx.getAtomVal)).isSome then return true
    return false

/-- Retain an entry's enclosing command wrappers while removing sibling
declarations from a mutual command. Only its own tree controls equation permission. -/
private partial def ownCommandTree (declaration : Syntax) (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Command.declaration && stx != declaration then .missing
  else stx.setArgs (stx.getArgs.map (ownCommandTree declaration))

def entryHasAuthoredElaboration (entry : Entry) (forbidden : NameSet := {}) : Bool :=
  hasAuthoredElaboration #[{ entry with
    originCommand := ownCommandTree entry.command entry.originCommand }] forbidden

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

private partial def identifiers (stx : Syntax) : Array Name :=
  if stx.isIdent then #[stx.getId] else stx.getArgs.flatMap identifiers

private partial def patternKeys (stx : Syntax) : Array Name :=
  if stx.isOfKind ``Parser.Term.matchAlt then
    match stx[1].find? (·.isOfKind ``Parser.Term.quot) with
    | some quote => #[quote[1].getKind]
    | none => #[]
  else stx.getArgs.flatMap patternKeys

/-- Source patterns retain local extensions that are absent from an imported
module’s exported attribute table. Reading syntax never runs an expander. -/
def expansionKeys (entries : Array Entry) (coreDelegates : NameSet := {}) : NameSet := Id.run do
  let mut keys : NameSet := {}
  for entry in entries do
    let command := entry.command
    if command.isOfKind ``Parser.Command.macro_rules ||
        command.isOfKind ``Parser.Command.elab_rules then
      for key in patternKeys command do keys := keys.insert key
    if entry.sourceName.any coreDelegates.contains then continue
    -- Attribute registration may name an existing builtin syntax kind.
    if let some attrs := command.find? (·.isOfKind ``Parser.Term.attributes) then
      for attrSyntax in attrs[1].getSepArgs do
        let ids := identifiers attrSyntax
        let kinds := #[`macro, `term_elab, `builtin_macro, `builtin_term_elab,
          `tactic, `builtin_tactic, `command_elab, `builtin_command_elab]
        if ids.any kinds.contains then
          for id in ids do unless kinds.contains id do keys := keys.insert id
  return keys

/-- The complete P0 attribute-name set. Attribute arguments have no permission. -/
private def allowedRegAttributes : Array Name := #[`instance, `reducible]

private def attributeIssue (attr : Syntax) : Option Name := do
  let name := if attr.isOfKind ``Parser.Attr.instance then `instance
    else if attr.isOfKind ``Parser.Attr.simple && attr[0].isIdent then attr[0].getId
    else attr.getKind
  if !allowedRegAttributes.contains name then return name
  if !attr[1].getArgs.isEmpty then return attr.getKind
  none

private partial def attributesIssue (command : Syntax) : Option Name := do
  if command.isOfKind ``Parser.Term.attributes then
    command[1].getSepArgs.findSome? fun attr => attributeIssue attr[1]
  else if command.isOfKind ``Parser.Command.attribute then
    command[2].getSepArgs.findSome? fun attr => attributeIssue attr[1]
  else command.getArgs.findSome? attributesIssue

/-- Complete ordinary command-kind table. Wrappers recurse into their commands;
no term subtree is mistaken for an authorized command. -/
private def ordinaryRegCommands : Array Name := #[
  ``Parser.Command.declaration, ``Parser.Command.end, ``Parser.Command.moduleDoc,
  ``Parser.Command.namespace, ``Parser.Command.open, ``Parser.Command.printAxioms,
  ``Parser.Command.section, ``Parser.Command.universe, ``Parser.Command.variable,
  `LeanInformationAudit.command__,
  `LeanInformationAudit.registerInformationFiniteSourceTheoremCmd,
  `LeanInformationAudit.registerInformationSourceTheoremCmd,
  `LeanInformationAudit.registerInformationTheoremOccurrenceReadoutCmd,
  `LeanInformationAudit.registerInformationTheoremReadoutCmd,
  `LeanInformationAudit.sealInformationTheoryCmd,
  `LeanInformationAudit.«command__Constructors_[_,,]»]

/-- Exact source option names and their literal types. The table applies also
inside terms and tactics; option name prefixes grant no permission. -/
private def booleanRegOptions : Array Name := #[
  `autoImplicit, `relaxedAutoImplicit, `backward.isDefEq.respectTransparency,
  `backward.isDefEq.respectTransparency.types, `trace.InformationRegistration.check]

private def naturalRegOptions : Array Name := #[
  `maxHeartbeats, `maxRecDepth, `maxSynthPendingDepth]

private partial def auditRegInputs (owner : Name) (stx : Syntax) : Except String Unit := do
  if stx.isOfKind ``Parser.Command.declModifiers then
    for modifier in #["unsafe", "partial"] do
      if (stx.find? fun s => s.isAtom && s.getAtomVal == modifier).isSome then
        throw s!"contract.reg:declaration_modifier_not_allowed:{owner}:{modifier}"
  if #[``Parser.Command.set_option, ``Parser.Term.set_option,
      ``Parser.Tactic.set_option].contains stx.getKind then
    let arity := if stx.isOfKind ``Parser.Command.set_option then 4 else 6
    unless stx.getArgs.size == arity && stx[1].isIdent && stx[2].getArgs.isEmpty do
      throw s!"contract.reg:wrapper_not_allowed:{owner}:{stx.getKind}"
    let name := stx[1].getId
    unless booleanRegOptions.contains name || naturalRegOptions.contains name do
      throw s!"contract.reg:option_not_allowed:{owner}:{name}"
    let value := stx[3]
    let valid := if booleanRegOptions.contains name then
        value.isAtom && #["true", "false"].contains value.getAtomVal
      else value.isNatLit?.isSome
    unless valid do throw s!"contract.reg:option_literal_type:{owner}:{name}"
  for child in stx.getArgs do auditRegInputs owner child

private partial def auditRegCommand (owner : Name) (command : Syntax) : Except String Unit := do
  if let some attr := attributesIssue command then
    throw s!"contract.reg:metaprogramming_not_allowed:{owner}:attribute:{attr}"
  if command.getKind == `Lean.runCmd then
    throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{command.getKind}"
  else if command.isOfKind ``Parser.Command.notation then
    throw s!"contract.reg:metaprogramming_not_allowed:{owner}:notation_binding"
  else if command.isOfKind ``Parser.Command.in then
    unless command.getArgs.size == 3 && command[1].isAtom &&
        command[1].getAtomVal.trimAscii.toString == "in" do
      throw s!"contract.reg:wrapper_not_allowed:{owner}:{command.getKind}"
    auditRegCommand owner command[0]
    auditRegCommand owner command[2]
  else if command.isOfKind ``Parser.Command.mutual then
    unless command.getArgs.size == 3 && command[1].getKind == `null do
      throw s!"contract.reg:wrapper_not_allowed:{owner}:{command.getKind}"
    for child in command[1].getArgs do auditRegCommand owner child
  else if command.isOfKind ``Parser.Command.set_option then
    unless command.getArgs.size == 4 do
      throw s!"contract.reg:wrapper_not_allowed:{owner}:{command.getKind}"
  else if command.isOfKind ``Parser.Command.attribute then
    pure ()
  else unless ordinaryRegCommands.contains command.getKind do
    throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{command.getKind}"

/-- Every command must have a finite permission. Metaprogramming commands,
including run_cmd and notation, have none. -/
def auditRegCommands (owner : Name) (entries : Array Entry) : Except String Unit := do
  let mut seen : Array String.Pos.Raw := #[]
  for entry in entries do
    let pos := entry.originCommand.getPos?.getD entry.start
    if seen.contains pos then continue
    seen := seen.push pos
    auditRegInputs owner entry.originCommand
    auditRegCommand owner entry.originCommand

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
      entries := entries.push ⟨command, none, start, stop, command, #[]⟩
    else
      for declaration in authorDeclarations do
        let sourceName := declarationName ns declaration
        let authoredNames := sourceName.map (fun name =>
          #[name] ++ nestedDeclarationNames name declaration) |>.getD #[]
        entries := entries.push ⟨declaration, sourceName,
          declaration.getPos?.getD start, declaration.getTailPos?.getD stop,
          command, authoredNames⟩
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
