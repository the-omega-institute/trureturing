import LeanInformationAudit.Registry.Repository

namespace LeanInformationAudit.ArenaProvenance

open Lean Meta

/-- These annotations are compile-time inputs to the forwarding resolver only. -/
def construction : Name := `LeanInformationAudit.arenaConstruction
def unsupported : Name := `LeanInformationAudit.arenaSourceUnsupported

private def arenaType (type : Expr) : Bool :=
  #[`D5.S3.ConceptDynamics.InformationEscape.Arena,
    `D5.S3.ConceptDynamics.InformationEscape.PrimitiveLawArena,
    `D5.S3.ConceptDynamics.InformationEscape.CounterexampleRecord.WitnessArena].any
    type.isAppOf

/-- Source construction evidence emitted by registration compilation. These are
the compiler's values with construction annotations, not resolved ownership answers.
Ordinary module imports carry this evidence to the IO-free seal validator. -/
private initialize sourceEvidence : SimplePersistentEnvExtension (Name × Expr) (NameMap Expr) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun values (name, value) => values.insert name value
    addImportedFn := fun arrays => arrays.foldl
      (fun values rows => rows.foldl (fun values (name, value) => values.insert name value) values) {}
  }

private def reject (stx : Syntax) (value : Expr) : Expr :=
  mkMData (KVMap.empty.setString unsupported stx.getKind.toString) value

private partial def unwrap (stx : Syntax) : Syntax :=
  if stx.isOfKind ``Parser.Term.paren then unwrap stx[1]
  else if stx.isOfKind ``Parser.Term.typeAscription then unwrap stx[1]
  else stx

/-- Keep each source application as a separate argument frame. Lean elaborates a
parenthesized function before the outer call, inserting defaults at that boundary.
The Expr spine alone has erased these boundaries and cannot recover them. -/
private partial def application (input : Syntax) : Syntax × Array (Array Syntax) :=
  let stx := unwrap input
  if stx.isOfKind ``Parser.Term.app then
    let (fn, frames) := application stx[0]
    (fn, frames.push stx[1].getArgs)
  else (stx, if input.isOfKind ``Parser.Term.paren ||
      input.isOfKind ``Parser.Term.typeAscription then #[#[]] else #[])

private partial def binderCount (input : Syntax) : Nat := Id.run do
  let stx := unwrap input
  if stx.isIdent || stx.isOfKind ``Parser.Term.hole then 1
  else if stx.isOfKind ``Parser.Term.app then
    binderCount stx[0] + stx[1].getArgs.foldl (fun n b => n + binderCount b) 0
  else if stx.isOfKind ``Parser.Term.explicitBinder ||
      stx.isOfKind ``Parser.Term.implicitBinder ||
      stx.isOfKind ``Parser.Term.strictImplicitBinder then stx[1].getArgs.size
  else if stx.isOfKind ``Parser.Term.instBinder then 1
  else 0

private partial def lambdaCount (stx : Syntax) : Nat := Id.run do
  let stx := unwrap stx
  if stx.isOfKind ``Parser.Term.fun && stx[1].isOfKind ``Parser.Term.basicFun then
    return stx[1][0].getArgs.foldl (fun n b => n + binderCount b) 0 + lambdaCount stx[1][3]
  return 0

/-- Straight-line tactic spelling of a term. No tactics are executed during
recovery; all other tactic programs remain explicitly unsupported. -/
private def tacticTerm? (stx : Syntax) : MetaM (Option Syntax) := do
  unless stx.isOfKind ``Parser.Term.byTactic do return none
  let seq := stx[1][0]
  let nodes := if seq.isOfKind ``Parser.Tactic.tacticSeq1Indented then seq[0]
    else if seq.isOfKind ``Parser.Tactic.tacticSeqBracketed then seq[1] else Syntax.missing
  let tactics := nodes.getSepArgs
  if tactics.isEmpty then return none
  let `(tactic| exact $last) := tactics.back! | return none
  let mut body := last
  for tac in (tactics.pop).reverse do
    let tac := if let some original := Parser.Tactic.Doc.alternativeOfTactic (← getEnv) tac.getKind
      then Syntax.node tac.getHeadInfo original tac.getArgs else tac
    match tac with
    | `(tactic| let $c:letConfig $d:letDecl) =>
      body ← `(term| let $c:letConfig $d:letDecl; $body)
    | `(tactic| letI $c:letConfig $d:letDecl) =>
      body ← `(term| letI $c:letConfig $d:letDecl; $body)
    | _ => return none
  return some body.raw

/-- Lean's `Elab.App.findNamedArgDependsOn?` inserts an unsupplied explicit
argument when a later named binder depends on it. Inspect the original compiled
telescope, with prior compiled arguments substituted, and only this frame's
pending names. Default values do not count as type dependencies. -/
private def namedDependsOnCurrent (type : Expr) (named : List Syntax) : MetaM Bool := do
  if named.isEmpty || type.isArrow then return false
  forallTelescopeReducing type fun xs _ => do
    let some current := xs[0]? | return false
    let mut pending := named.map (·[1].getId)
    for x in xs[1:] do
      let decl ← x.fvarId!.getDecl
      if pending.contains decl.userName then
        if ← exprDependsOn decl.type.cleanupAnnotations current.fvarId! then return true
        -- A repeated binder name cannot make an already matched name dependent.
        pending := pending.filter (· != decl.userName)
    return false

/-- Reattach syntax only where its shape agrees with the compiled term. Unsupported
forms remain a deferred error on that term: a dead argument must not affect ownership.
No names are resolved from source; the compiler's constants and binders remain intact. -/
private partial def recover (stx : Syntax) (value : Expr) : MetaM Expr := do
  let stx := unwrap stx
  if let some term ← tacticTerm? stx then return ← recover term value
  if stx.isOfKind ``Parser.Term.structInst ||
      stx.isOfKind ``Parser.Term.structInstDefault ||
      stx.isOfKind ``Parser.Command.whereStructInst then
    let type ← whnfR (← inferType value)
    if arenaType type then
      return mkAnnotation construction value
    -- A function-valued literal still has unmatched elaborated binders (for
    -- example an implicit lambda inserted from the expected type). It cannot
    -- silently lose the construction merely because its type is not yet Arena.
    if type.isForall then return reject stx value
    return value
  if stx.isIdent then
    -- Expected-type implicit lambdas have no source binder. Align the identifier
    -- under the compiler's binders, still checking inserted arguments in its body.
    if let .lam _ _ _ bi := value then
      if !bi.isExplicit then return ← recoverLambdas 1 stx value
    -- Even a bare identifier can elaborate to an application (defaults and
    -- inferred arguments). No source subterm justifies those argument values.
    -- Mark each argument, not the application: only a live argument can fail.
    let fn := value.getAppFn
    unless fn.isConst || fn.isFVar || fn.isBVar do return reject stx value
    return mkAppN fn (value.getAppArgs.map (reject stx))
  if (stx.isOfKind ``termIfThenElse && value.isAppOf ``ite) ||
      (stx.isOfKind ``termDepIfThenElse && value.isAppOf ``dite) then return value
  if stx.isOfKind ``Parser.Term.fun && stx[1].isOfKind ``Parser.Term.basicFun then
    let count := stx[1][0].getArgs.foldl (fun n b => n + binderCount b) 0
    if count == 0 then return reject stx value
    return ← recoverLambdas count stx[1][3] value
  if stx.isOfKind ``Parser.Term.app then
    let (sourceFn, frames) := application stx
    let explicit := sourceFn.isOfKind ``Parser.Term.explicit
    -- Retain the supported-subset boundary for shadowed named binders.
    let names := (frames.toList.flatMap Array.toList).filterMap fun arg =>
      if arg.isOfKind ``Parser.Term.namedArgument then some arg[1].getId else none
    if names.eraseDups.length != names.length then return reject stx value
    let mut namedBinders : NameSet := {}
    let fn := value.getAppFn
    let mut result ← recover (if explicit then sourceFn[1] else sourceFn) fn
    let mut type ← inferType fn
    let compiledArgs := value.getAppArgs
    let mut index := 0
    for frameIndex in [:frames.size] do
      let frame := frames[frameIndex]!
      let mut args := frame.toList.filter (! ·.isOfKind ``Parser.Term.namedArgument)
      let mut named := frame.toList.filter (·.isOfKind ``Parser.Term.namedArgument)
      -- `@` belongs only to its own call, never to a subsequent outer call.
      let explicit := explicit && frameIndex == 0
      while index < compiledArgs.size do
        let .forallE name domain body bi ← whnf type | return reject stx value
        let nextNamed := named.find? (·[1].getId == name)
        -- An unsupplied ordinary explicit binder ends the frame unless Lean
        -- inferred it from a pending named binder in this same frame. Inserted
        -- arguments still have NO source evidence: the next frame's literal
        -- must never annotate an optParam inserted by this frame.
        if nextNamed.isNone then
          if bi.isExplicit || explicit then
            if args.isEmpty && (explicit ||
                (!domain.isOptParam && !domain.isAutoParam)) then
              unless ← namedDependsOnCurrent type named do break
          else if bi == .strictImplicit && args.isEmpty && named.isEmpty then break
        if frames.size > 1 && names.contains name then
          if namedBinders.contains name then return reject stx value
          namedBinders := namedBinders.insert name
        let arg := compiledArgs[index]!
        let mut annotated := reject stx arg
        if let some next := nextNamed then
          annotated ← recover next[3] arg
          named := named.filter (·[1].getId != name)
        else if bi.isExplicit || explicit then
          if let next :: rest := args then
            annotated ← recover next arg
            args := rest
        result := mkApp result annotated
        -- Always instantiate with the ORIGINAL compiled argument. An annotation
        -- is evidence only; it must not change the context used for alignment.
        type := body.instantiate1 arg
        index := index + 1
      if !args.isEmpty || !named.isEmpty then return reject stx value
    -- Expected-type elaboration can supply arguments beyond the last frame.
    -- Keep unsupported evidence on those actual arguments, allowing dead ones.
    return mkAppN result ((compiledArgs.extract index compiledArgs.size).map (reject stx))
  if stx.isOfKind ``Parser.Term.letI && stx[2][0].isOfKind ``Parser.Term.letIdDecl then
    -- Lean inlines letI. Its source type cannot be classified in the consumer's
    -- namespace/open context. A direct return aligns the RHS with the original
    -- compiled value; inferType in recover then uses the actual local context.
    -- An unused source name can be dropped: any inserted instance/default
    -- arguments are independently guarded above. Other uses lack an alignment.
    unless stx[1][0].getArgs.isEmpty do return reject stx value
    let decl := Elab.Term.mkLetIdDeclView stx[2][0]
    let body := unwrap stx[4]
    let name := decl.id.getId.eraseMacroScopes
    if decl.id.isIdent && body.isIdent && body.getId.eraseMacroScopes == name then
      unless decl.binders.isEmpty do return reject stx value
      return ← recover decl.value value
    if decl.id.isIdent && (body.find? fun node =>
        node.isIdent && node.getId.eraseMacroScopes == name).isSome then
      return reject stx value
    return ← recover body value
  if stx.isOfKind ``Parser.Term.let &&
      stx[2][0].isOfKind ``Parser.Term.letIdDecl then
    let .letE name type rhs body nondep := value | return reject stx value
    let decl := Elab.Term.mkLetIdDeclView stx[2][0]
    -- elabLetDeclAux wraps the RHS in one lambda per elaborated source binder.
    -- Recover under those binders, leaving any explicit RHS lambdas to `recover`.
    let counts := decl.binders.map binderCount
    let rhs ← if counts.any (· == 0) then pure (reject stx[2] rhs)
      else recoverLambdas (counts.foldl (· + ·) 0) decl.value rhs
    return ← withLetDecl name type rhs fun x => do
      let body ← recover stx[4] (body.instantiate1 x)
      return .letE name type rhs (body.abstract #[x]) nondep
  -- Projections and recursors are already stopping boundaries of the resolver.
  -- Their syntax cannot turn the stopped value into a forwarding alias.
  if value.isProj then return value
  return reject stx value
where
  recoverLambdas (count : Nat) (body : Syntax) (value : Expr) : MetaM Expr := do
    if count == 0 then return ← recover body value
    let .lam name type rest bi := value | return reject body value
    withLocalDecl name bi type fun x => do
      let rest ← recoverLambdas (count - 1) body (rest.instantiate1 x)
      return .lam name type (rest.abstract #[x]) bi

private partial def leadingLambdas : Expr → Nat
  | .lam _ _ body _ => 1 + leadingLambdas body
  | _ => 0

private def stopsAtCompiledHead (env : Environment) (term : Expr) : Bool :=
  match term with
  | .mdata _ body | .lam _ _ body _ => stopsAtCompiledHead env body
  -- Let-bound field/type values cannot affect a constructor-headed body. A
  -- bound-variable head is deliberately not followed: it may hide a field copy.
  | .letE _ _ _ body _ => stopsAtCompiledHead env body
  | .proj .. => true
  | value@(.app ..) =>
    match value.getAppFn with
    | .const name _ =>
      env.isProjectionFn name || isAuxRecursor env name ||
        match env.find? name with
        | some (.ctorInfo _) | some (.recInfo _) => true
        | _ => false
    | _ => false
  | _ => false

private partial def declarationBody? (stx : Syntax) : Option Syntax := do
  if stx.isOfKind ``Parser.Command.definition || stx.isOfKind ``Parser.Command.abbrev then
    let rhs := stx[3]
    if rhs.isOfKind ``Parser.Command.declValSimple then return rhs[1]
    if rhs.isOfKind ``Parser.Command.whereStructInst then return rhs
    none
  if stx.isOfKind ``Parser.Command.declaration then declarationBody? stx[1]
  else none

/-- Resolve a compiler-owned module through the repository's logical package paths.
The root is found at use time; neither paths nor source digests enter an olean. -/
def moduleSource (name : Name) : IO System.FilePath := do
  let path := name.toString.replace "." "/" ++ ".lean"
  if name.getRoot == `D5 || name.getRoot == `Reg then
    Repository.source path
  else if name.getRoot == `LeanInformationAudit then
    Repository.source ("tools/lean-inspector/" ++ path)
  else if name.getRoot == `LeanInformationAuditInterface then
    Repository.source ("tools/lean-inspector-interface/" ++ path)
  else
    findLean (← getSrcSearchPath) name

private def compiledProvenanceComplete (env : Environment) (info : DefinitionVal) : Bool :=
  stopsAtCompiledHead env info.value || !env.isImportedConst info.name ||
    (info.value.find? fun e => match e with
      | .mdata data _ => data.contains construction
      | _ => false).isSome

/-- Reconstitute Lean's parser extension from the owner's compiler import DAG.
All entries and parser implementations are already loaded. This neither imports
modules again nor executes initializers, and cannot inherit later Reg keywords. -/
private def ownerParserEnvironment (env : Environment) (owner : ModuleIdx) : IO Environment := do
  let mut pending := #[owner]
  let mut included : Std.HashSet ModuleIdx := {}
  while !pending.isEmpty do
    let idx := pending.back!
    pending := pending.pop
    if included.contains idx then continue
    included := included.insert idx
    for dependency in env.header.moduleData[idx]!.imports do
      if let some idx := env.getModuleIdx? dependency.module then
        pending := pending.push idx
  let entries := env.header.modules.mapIdx fun idx _ =>
    if included.contains idx then Parser.parserExtension.ext.getModuleEntries env idx
    else #[]
  let state ← (Parser.parserExtension.ext.addImportedFn entries).run { env, opts := {} }
  return Parser.parserExtension.ext.setState env state

/-- Sealing reads only compiler evidence. It never opens source or accepts an
unannotated eta-contracted value as a substitute for missing source evidence. -/
def compiledValue (info : DefinitionVal) : MetaM Expr := do
  let env ← getEnv
  if compiledProvenanceComplete env info then return info.value
  let some value := (sourceEvidence.getState env).find? info.name
    | throwError "IE-C003 ArenaSourceUnavailable declaration={info.name} reason=provenance"
  return value

/-- Recover the distinction erased by structure eta from the declaration's original
syntax. Imported Expr remains authoritative for all forwarding steps and names.
No source hashes, ownership cache, or freshness/release checks are stored. -/
def declarationValue (info : DefinitionVal) : MetaM Expr := do
  let env ← getEnv
  -- Locally elaborated declarations already carry the hook, including synthetic
  -- declarations without source ranges used by the bounded resolver tests. Retain
  -- that evidence when acquisition uses it: after an import, an unannotated local
  -- forwarding value no longer qualifies through the local-declaration branch.
  if compiledProvenanceComplete env info then
    if !env.isImportedConst info.name then
      modifyEnv fun env => sourceEvidence.addEntry env (info.name, info.value)
    return info.value
  if let some value := (sourceEvidence.getState env).find? info.name then return value
  let some idx := env.getModuleIdxFor? info.name
    | throwError "IE-C003 ArenaSourceUnavailable declaration={info.name} reason=owner"
  let owner := env.header.moduleNames[idx]!
  let some ranges ← findDeclarationRanges? info.name
    | throwError "IE-C003 ArenaSourceUnavailable declaration={info.name} reason=range"
  let source ← try IO.FS.readFile (← moduleSource owner)
    catch _ => throwError "IE-C003 ArenaSourceUnavailable declaration={info.name} \
      module={owner} reason=source"
  let map := FileMap.ofString source
  let excerpt := (Substring.Raw.mk source (map.ofPosition ranges.range.pos)
    (map.ofPosition ranges.range.endPos)).toString
  let parserEnv ← ownerParserEnvironment env idx
  let stx ← match Parser.runParserCategory parserEnv `command excerpt with
    | .ok stx => pure stx
    | .error error => throwError "IE-C003 ArenaSourceUnavailable declaration={info.name} \
        module={owner} reason=parse: {error}"
  let some body := declarationBody? stx
    | throwError "IE-C003 ArenaSourceUnsupported declaration={info.name} \
        module={owner} kind={stx.getKind}"
  let count := leadingLambdas info.value
  let sourceCount := lambdaCount body
  if count < sourceCount then
    throwError "IE-C003 ArenaSourceUnsupported declaration={info.name} reason=lambda_shape"
  let value ← withTheReader Core.Context
    (fun ctx => { ctx with currNamespace := (privateToUserName info.name).getPrefix }) <|
    recover.recoverLambdas (count - sourceCount) body info.value
  modifyEnv fun env => sourceEvidence.addEntry env (info.name, value)
  return value

end LeanInformationAudit.ArenaProvenance
