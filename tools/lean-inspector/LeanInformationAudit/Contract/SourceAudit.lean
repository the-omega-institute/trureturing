import Lean

namespace LeanInformationAudit.Contract.SourceAudit
open Lean

def heads : Array Name := #[
  `LeanInformationAudit.Contract.Registration,
  `LeanInformationAudit.Contract.TemplateEnrollment,
  `LeanInformationAudit.Contract.RootCatalog,
  `LeanInformationAudit.Contract.ExpectedDeclaration,
  `LeanInformationAudit.Contract.Seal]

/-- Only the endpoint of a declaration telescope determines its output. -/
partial def resultType (e : Expr) : Expr :=
  match e.consumeMData with
  | .forallE _ _ body _ => resultType body
  | e => e

private def allowedTypeCarrierStructures : Array Name := #[
  `D5.S3.ConceptDynamics.InformationEscape.Arena,
  `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena,
  `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature,
  `D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena]

private def projectionStructure (env : Environment) (name : Name) : Option Name :=
  (env.getProjectionFnInfo? name).map (·.ctorName.getPrefix)

private def projectionReturnsSort (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info => (resultType info.type).isType
  | none => false

private def allowedProjection (structureName : Name) : Bool :=
  allowedTypeCarrierStructures.contains structureName

private partial def resultTypeIssueAt (env : Environment) (e : Expr) : Option String :=
  match e.consumeMData with
  | .letE _ type value body _ =>
      if let some issue := resultTypeIssueAt env type then some issue
      else if let some issue := resultTypeIssueAt env value then some issue
      else if let some issue := resultTypeIssueAt env body then some issue
      else some "contract.discovery:result_type_let"
  | .proj structureName index value =>
      let fields := getStructureFields env structureName
      match fields[index]? with
      | some field =>
          let projection := structureName ++ field
          if projectionReturnsSort env projection && !allowedProjection structureName then
            some s!"contract.discovery:result_type_projection:{structureName}:{field}"
          else resultTypeIssueAt env value
      | none => some s!"contract.discovery:result_type_projection:{structureName}:{index}"
  | .app fn arg =>
      if let some fnName := fn.constName? then
        if let some projection := projectionStructure env fnName then
          if projectionReturnsSort env fnName && !allowedProjection projection then
            some s!"contract.discovery:result_type_projection:{projection}:{fnName}"
          else if let some issue := resultTypeIssueAt env fn then some issue
          else resultTypeIssueAt env arg
        else if let some issue := resultTypeIssueAt env fn then some issue
        else if let some issue := resultTypeIssueAt env arg then some issue else none
      else if let some issue := resultTypeIssueAt env fn then some issue
      else resultTypeIssueAt env arg
  | .forallE _ domain body _ =>
      if let some issue := resultTypeIssueAt env domain then some issue
      else resultTypeIssueAt env body
  | .lam _ domain body _ =>
      if let some issue := resultTypeIssueAt env domain then some issue
      else resultTypeIssueAt env body
  | .mdata _ body => resultTypeIssueAt env body
  | _ => none

def resultTypeIssue (env : Environment) (e : Expr) : Option String :=
  resultTypeIssueAt env (resultType e)

private partial def containsAtomValue (stx : Syntax) (value : String) : Bool :=
  (stx.isAtom && stx.getAtomVal == value) || stx.getArgs.any (containsAtomValue · value)

/-- Check the authored result-type syntax before elaboration zeta-reduces it. -/
def sourceResultTypeIssue (command : Syntax) : Option String :=
  if !command.isOfKind ``Parser.Command.declaration then none
  else
    let declaration := command[1]
    if !declaration.isOfKind ``Parser.Command.definition then none
    else
      let signature := declaration[2]
      let type := signature[1][0][1]
      if containsAtomValue type "let" || containsAtomValue type "have" then
        some "contract.discovery:result_type_let"
      else none

/-- Recognize proposition-valued heads from their compiled signatures, without
normalization or examining proofs. Proposition arguments are mathematical data. -/
partial def proposition (env : Environment) (e : Expr) : Bool :=
  match e.consumeMData with
  | .forallE _ _ body _ => proposition env body
  | .sort .zero => true
  | e => match e.getAppFn.constName? >>= env.find? with
    | some info => resultType info.type == .sort .zero
    | none => false

private def carriesTypes (e : Expr) : Bool :=
  (e.find? fun t => match t with | .sort (.succ _) | .sort (.param _) => true | _ => false).isSome

/-- Application arguments count only in type positions. Numeric indices and
other mathematical values cannot turn their enclosing type into a carrier. -/
private partial def typeConstants (env : Environment) (e : Expr) : Array Name := Id.run do
  let e := resultType e
  if proposition env e then return #[]
  match e with
  | .lam _ _ body _ => return typeConstants env body
  | .letE _ type value body _ =>
      return typeConstants env type ++ typeConstants env value ++ typeConstants env body
  | .proj _ _ value => return value.getUsedConstants
  | .app .. =>
    let fn := e.getAppFn
    let mut names := typeConstants env fn
    if let some info := fn.constName? >>= env.find? then
      let mut signature := info.type
      for arg in e.getAppArgs do
        if let .forallE _ domain body _ := signature.consumeMData then
          if domain.isSort || carriesTypes domain then
            names := names ++ typeConstants env arg
          signature := body.instantiate1 arg
    return names
  | .const name _ => return #[name]
  | .mdata _ body => return typeConstants env body
  | _ => return #[]

/-- Inspect result-type syntax and type-producing constant bodies. Ordinary
value bodies and proposition proofs never propagate contract candidacy.
A projection of a stored type (such as packed.1) retains its carrier closure. -/
def scanContract (env : Environment) (e : Expr) (unrelated : NameSet := {})
    : Bool × NameSet := Id.run do
  let e := resultType e
  if proposition env e then return (false, unrelated)
  let mut pending := typeConstants env e
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if heads.contains name then return (true, unrelated)
    if seen.contains name || unrelated.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      let endpoint := resultType info.type
      if proposition env endpoint then continue
      unless endpoint.isSort || carriesTypes endpoint do continue
      -- Constants in a type expression may store types in products or return
      -- types through definitions. Inspect their syntax, never reduce it.
      if let some value := info.value? (allowOpaque := true) then
        pending := pending ++ typeConstants env value
      if let .inductInfo d := info then
        for ctor in d.ctors do
          if let some ctorInfo := env.find? ctor then
            let mut signature := ctorInfo.type
            repeat
              let .forallE _ domain body _ := signature.consumeMData | break
              pending := pending ++ typeConstants env domain
              signature := body
  return (false, seen.toArray.foldl (fun cache name => cache.insert name) unrelated)

def containsContract (env : Environment) (e : Expr) : Bool :=
  (scanContract env e).1

partial def termHead (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Term.paren then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.app then termHead stx[0]
  else if stx.isOfKind ``Parser.Term.explicit then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.explicitUniv then termHead stx[0]
  else stx

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
        let kinds := #[`macro, `term_elab, `builtin_macro, `builtin_term_elab]
        if ids.any kinds.contains then
          for id in ids do unless kinds.contains id do keys := keys.insert id
  return keys

private partial def containsIdentifier (stx : Syntax) (names : Array Name) : Bool :=
  (stx.isIdent && names.contains stx.getId) || stx.getArgs.any (containsIdentifier · names)

private def commandTextKind (command : Syntax) : String := command.getKind.toString.toLower

private def commandHasAttribute (command : Syntax) : Bool :=
  (command.find? (·.isOfKind ``Parser.Term.attributes)).isSome

private def onlyReducibleAttribute (command : Syntax) : Bool :=
  match command.find? (·.isOfKind ``Parser.Term.attributes) with
  | some attrs => attrs[1].getSepArgs.all fun attr =>
      let names := identifiers attr
      !names.isEmpty && names.all (· == `reducible)
  | none => false

private def existingLocalNotationOwner (owner : String) : Bool :=
  #["Reg.D5.S3.Quantum.Measurement.ExactConditionalPreparationCost",
    "Reg.D5.S1.Recurrence.Invariants.CloitreActualLeftPlateau",
    "Reg.D5.S1.Recurrence.Invariants.CloitreActualSpineCarry"].contains owner

private partial def containsQualifiedIdentifier (command : Syntax) (suffix : String) : Bool :=
  (command.isIdent && command.getId.toString.endsWith suffix) ||
    command.getArgs.any (containsQualifiedIdentifier · suffix)

private partial def containsAtom (command : Syntax) (value : String) : Bool :=
  (command.isAtom && command.getAtomVal == value) ||
    command.getArgs.any (containsAtom · value)

private def allowedRegRunCommand (command : Syntax) : Bool :=
  containsQualifiedIdentifier command "RootCatalogs.declare"

private def forbiddenRegAttribute (command : Syntax) : Option Name :=
  let names := #[`macro, `term_elab, `command_elab, `builtin, `builtin_macro,
    `builtin_term_elab, `builtin_command_elab]
  names.find? fun name => containsIdentifier command #[name]

/-- Reg source commands use an explicit, finite policy. Existing catalog and
snapshot declarations are retained by exact operation class; all other
repository-owned metaprogramming is rejected before any elaboration is used. -/
def auditRegCommands (owner : Name) (entries : Array Entry) : Except String Unit := do
  let ownerText := owner.toString
  for entry in entries do
    let command := entry.originCommand
    let kind := commandTextKind command
    if let some attrName := forbiddenRegAttribute command then
      throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{attrName}"
    if commandHasAttribute command && !onlyReducibleAttribute command then
      throw s!"contract.reg:metaprogramming_not_allowed:{owner}:attribute"
    if kind.contains "runcmd" || kind.contains "run_cmd" ||
        kind.contains "runmeta" || kind.contains "run_meta" ||
        kind.contains "runelab" || kind.contains "run_elab" then
      unless allowedRegRunCommand command do
        throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{command.getKind}"
    else if kind.contains "eval" || kind.contains "initialize" then
      throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{command.getKind}"
    else if kind.contains "macro" || kind.contains "syntax" ||
        kind.contains "elab" || kind.contains "notation" ||
        kind.contains "infix" || kind.contains "prefix" || kind.contains "postfix" then
      unless kind.contains "notation" && containsAtom command "local" &&
          existingLocalNotationOwner ownerText do
        throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{command.getKind}"
    else if kind.contains "attribute" then
      -- Ordinary instance attributes (including `local`/`scoped` blocks) are
      -- existing Reg infrastructure.  Meta attributes were rejected above.
      pure ()
    else if kind.contains "declaration" && commandHasAttribute command then
      unless onlyReducibleAttribute command do
        throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{command.getKind}"
  pure ()

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
      entries := entries.push ⟨command, none, start, stop, command⟩
    else
      for declaration in authorDeclarations do
        entries := entries.push ⟨declaration, declarationName ns declaration,
          declaration.getPos?.getD start, declaration.getTailPos?.getD stop, command⟩
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
