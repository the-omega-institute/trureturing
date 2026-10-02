import Lean
import LeanInformationAudit.Contract.RegPolicy

/-!
Reg command permissions are the exact ordinary kind table, the 84 complete
catalog syntax fingerprints, three complete local notation fingerprints, and
bare instance/reducible attributes. Unknown commands and wrapped inner commands
fail closed. The catalog call resolves uniquely to the fully qualified declare
constant. P3 deletes catalog and legacy registration/enrollment/seal permissions.

Every compiled declaration's result is inspected before candidacy. The four
listed mathematical carriers require a constant-backed constructor instance and
a selected field whose structural constant closure excludes all Contract heads.
Unknown instances and stored Contract fields receive named projection failures.
No source command, evaluator, whnf or isDefEq is invoked.
-/

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

private def projectionReturnsSort (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some info => (resultType info.type).isType
  | none => false

/-- Read a constructor field by kernel metadata, without reducing the term. -/
private def constructorField (env : Environment) (structureName : Name)
    (index : Nat) (value : Expr) : Option Expr := do
  let some (.ctorInfo info) := value.getAppFn.constName? >>= env.find? | none
  guard (info.induct == structureName)
  guard (value.getAppArgs.size == info.numParams + info.numFields)
  value.getAppArgs[info.numParams + index]?

/-- Only constant-backed constructor trees are carrier instances. Lambda
substitution applies the constant's literal telescope; it is not normalization.
Projection selection reads the same constructor tree recursively. -/
private def carrierValue (env : Environment) (value : Expr) : Option Expr :=
  let rec read (fuel : Nat) (seen : NameSet) (value : Expr) : Option Expr := do
    let fuel + 1 := fuel | none
    let value := value.consumeMData
    if let .proj structureName index parent := value then
      let parent ← read fuel seen parent
      read fuel seen (← constructorField env structureName index parent)
    else
      let .const name levels := value.getAppFn | none
      let info ← env.find? name
      if info.isCtor then return value
      if let some projection := env.getProjectionFnInfo? name then
        let args := value.getAppArgs
        let parent ← args[projection.numParams]?
        let parent ← read fuel seen parent
        let field ← constructorField env projection.ctorName.getPrefix projection.i parent
        read fuel seen (mkAppN field (args.extract (projection.numParams + 1) args.size))
      else
        guard (!seen.contains name)
        let .defnInfo definition := info | none
        let mut body := definition.value.instantiateLevelParams definition.levelParams levels
        for arg in value.getAppArgs do
          let .lam _ _ next _ := body.consumeMData | none
          body := next.instantiate1 arg
        read fuel (seen.insert name) body
  read 128 {} value

/-- A structural constant closure of the selected field. All types and bodies
are read as Expr trees; no evaluator, whnf or definitional equality is used. -/
private def fieldContainsContract (env : Environment) (field : Expr) : Bool := Id.run do
  let mut pending := field.getUsedConstants
  let mut seen : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if heads.contains name then return true
    if seen.contains name then continue
    seen := seen.insert name
    if let some info := env.find? name then
      pending := pending ++ info.type.getUsedConstants
      if let some body := info.value? (allowOpaque := true) then
        pending := pending ++ body.getUsedConstants
  return false

private def carrierIssue (env : Environment) (structureName : Name)
    (index : Nat) (value : Expr) : Option String := do
  let field := (getStructureFields env structureName)[index]?
  let diagnostic := s!"contract.discovery:result_type_projection:{structureName}:{field}"
  if !allowedTypeCarrierStructures.contains structureName then return diagnostic
  let some constructor := carrierValue env value
    | return diagnostic ++ ":carrier_unresolved"
  let some payload := constructorField env structureName index constructor
    | return diagnostic ++ ":carrier_unresolved"
  if payload.hasLooseBVars || payload.hasFVar || payload.hasMVar then
    return diagnostic ++ ":carrier_unresolved"
  if fieldContainsContract env payload then return diagnostic ++ ":contract_payload"
  none

private partial def resultTypeIssueAt (env : Environment) (e : Expr) : Option String :=
  let e := e.consumeMData
  match e with
  | .letE _ _ _ _ _ => some "contract.discovery:result_type_let"
  | .proj structureName index value =>
      match (getStructureFields env structureName)[index]? with
      | some field =>
          if projectionReturnsSort env (structureName ++ field) then
            carrierIssue env structureName index value
          else resultTypeIssueAt env value
      | none => some s!"contract.discovery:result_type_projection:{structureName}:{index}"
  | .app .. =>
      if let some name := e.getAppFn.constName? then
        if let some projection := env.getProjectionFnInfo? name then
          if projectionReturnsSort env name then
            match e.getAppArgs[projection.numParams]? with
            | some value => carrierIssue env projection.ctorName.getPrefix projection.i value
            | none => some s!"contract.discovery:result_type_projection:{name}:carrier_unresolved"
          else none
        else none
      else resultTypeIssueAt env e.getAppFn
  | .forallE _ _ body _ | .lam _ _ body _ => resultTypeIssueAt env body
  | _ => none

/-- Recognize proposition-valued heads from their compiled signatures, without
normalization or examining proofs. Proposition arguments are mathematical data. -/
partial def proposition (env : Environment) (e : Expr) : Bool :=
  match e.consumeMData with
  | .forallE _ _ body _ => proposition env body
  | .letE _ _ _ body _ => proposition env body
  | .sort .zero => true
  | e => match e.getAppFn.constName? >>= env.find? with
    | some info => resultType info.type == .sort .zero
    | none => false

private partial def hasTelescope (e : Expr) : Bool :=
  match e.consumeMData with
  | .forallE .. => true
  | .letE _ _ _ body _ => hasTelescope body
  | _ => false

/-- A telescoped mathematical function is not a stored-type result instance.
Its endpoint still passes through contract candidacy, which rejects contractual
functions and wrappers. Closed results receive the strict carrier check. -/
def resultTypeIssue (env : Environment) (e : Expr) : Option String :=
  if proposition env e || hasTelescope e then none else resultTypeIssueAt env e

private partial def containsAtomValue (stx : Syntax) (value : String) : Bool :=
  (stx.isAtom && stx.getAtomVal == value) || stx.getArgs.any (containsAtomValue · value)

partial def termHead (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Term.paren then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.app then termHead stx[0]
  else if stx.isOfKind ``Parser.Term.explicit then termHead stx[1]
  else if stx.isOfKind ``Parser.Term.explicitUniv then termHead stx[0]
  else stx

/-- Check the authored result-type syntax before elaboration zeta-reduces it. -/
def sourceResultTypeIssue (command : Syntax) : Option String :=
  if !command.isOfKind ``Parser.Command.declaration then none
  else
    let declaration := command[1]
    if !declaration.isOfKind ``Parser.Command.definition then none
    else
      let signature := declaration[2]
      let type := termHead signature[1][0][1]
      if containsAtomValue type "let" || containsAtomValue type "have" then
        some "contract.discovery:result_type_let"
      else none

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
  | .proj structureName index value =>
    if let some constructor := carrierValue env value then
      if let some field := constructorField env structureName index constructor then
        if fieldContainsContract env field then return heads
        return typeConstants env field
    return value.getUsedConstants
  | .app .. =>
    let fn := e.getAppFn
    if let some name := fn.constName? then
      if let some projection := env.getProjectionFnInfo? name then
        if let some value := e.getAppArgs[projection.numParams]? then
          if let some constructor := carrierValue env value then
            if let some field := constructorField env projection.ctorName.getPrefix projection.i constructor then
              if fieldContainsContract env field then return heads
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
  catalogTarget : Option Name := none

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

private def allowedRegRunCommand (owner : Name) (command : Syntax)
    (target : Option Name) : Bool :=
  command.getKind == `Lean.runCmd &&
    target == some `LeanInformationAudit.RootCatalogs.declare &&
    (RegPolicy.catalogCall command).isSome &&
    RegPolicy.catalogCommands.contains (owner, RegPolicy.fingerprint command)

/-- Complete ordinary command-kind table. Wrappers recurse into their commands;
no term subtree is mistaken for an authorized command. P3 removes the legacy
registration, enrollment and seal command kinds along with catalogCommands. -/
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

private partial def auditRegCommand (owner : Name) (command : Syntax)
    (target : Option Name) (allowPinned : Bool := true) : Except String Unit := do
  if let some attr := attributesIssue command then
    throw s!"contract.reg:metaprogramming_not_allowed:{owner}:attribute:{attr}"
  if command.getKind == `Lean.runCmd then
    unless allowPinned && allowedRegRunCommand owner command target do
      throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{command.getKind}"
  else if command.isOfKind ``Parser.Command.notation then
    unless allowPinned && RegPolicy.localNotations.contains (owner, RegPolicy.fingerprint command) do
      throw s!"contract.reg:metaprogramming_not_allowed:{owner}:notation_binding"
  else if command.isOfKind ``Parser.Command.in then
    auditRegCommand owner command[0] target false
    auditRegCommand owner command[2] target false
  else if command.isOfKind ``Parser.Command.mutual then
    for child in command[1].getArgs do auditRegCommand owner child target false
  else if command.isOfKind ``Parser.Command.set_option ||
      command.isOfKind ``Parser.Command.attribute then
    pure ()
  else unless ordinaryRegCommands.contains command.getKind do
    throw s!"contract.reg:metaprogramming_not_allowed:{owner}:{command.getKind}"

/-- Every command must have a finite permission. run_meta/run_elab have none.
Exact notation/catalog inputs can each occur only once in an audited module. -/
def auditRegCommands (owner : Name) (entries : Array Entry) : Except String Unit := do
  let mut catalogs : Nat := 0
  let mut notations : Nat := 0
  let mut seen : Array String.Pos.Raw := #[]
  for entry in entries do
    let pos := entry.originCommand.getPos?.getD entry.start
    if seen.contains pos then continue
    seen := seen.push pos
    auditRegCommand owner entry.originCommand entry.catalogTarget
    if entry.originCommand.getKind == `Lean.runCmd then
      catalogs := catalogs + 1
      if catalogs > 1 then
        throw s!"contract.reg:metaprogramming_not_allowed:{owner}:duplicate_catalog"
    if entry.originCommand.isOfKind ``Parser.Command.notation then
      notations := notations + 1
      if notations > 1 then
        throw s!"contract.reg:metaprogramming_not_allowed:{owner}:duplicate_notation"

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
    let catalogTarget := do
      let call ← RegPolicy.catalogCall command
      let [(name, [])] := ResolveName.resolveGlobalName parserEnv {} ns opens call[0].getId
        | none
      some name
    let authorDeclarations := declarations command
    if authorDeclarations.isEmpty then
      entries := entries.push ⟨command, none, start, stop, command, catalogTarget⟩
    else
      for declaration in authorDeclarations do
        entries := entries.push ⟨declaration, declarationName ns declaration,
          declaration.getPos?.getD start, declaration.getTailPos?.getD stop, command, catalogTarget⟩
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
