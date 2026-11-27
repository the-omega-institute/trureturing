import Lean
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.PublicDeclsExt
import Lean.Compiler.IR.CompilerM
import OmegaChecks.InitCompiler.RootNames
import OmegaChecks.InitCompiler.Layout
import OmegaChecks.InitCompiler.Proofs
import OmegaChecks.InitCompiler.CompilerMarkers

/-! Elaborate pinned Init declarations in strict prelude modules. -/

open Lean Parser Elab Command
namespace OmegaChecks.InitCompiler

private def omegaName (n : Name) := if RootNames.usesRoot n then n else `Omega ++ n

private def sourceGroup (src : Environment) (owner name : Name) : CoreM (Declaration × Array Name) := do
  let some (.inductInfo target) := src.find? name | throwError "{name} is not an official inductive"
  let mut types := []
  let mut ctors := #[]
  for n in target.all do
    let some idx := src.getModuleIdxFor? n | throwError "missing owner for {n}"
    unless src.header.moduleNames[idx]! == owner do throwError "{n} does not belong to {owner}"
    let some (.inductInfo i) := src.find? n | throwError "invalid inductive group"
    if i.isUnsafe || i.numNested != 0 then throwError "unsupported unsafe or nested inductive {n}"
    let fields ← i.ctors.mapM fun c => do
      let some (.ctorInfo val) := src.find? c | throwError "missing constructor {c}"
      return {name := omegaName c, type := ← ofExcept (translateProofTerm src val.type) : Constructor}
    ctors := ctors ++ fields.toArray.map (·.name)
    types := {name := omegaName n, type := ← ofExcept (translateProofTerm src i.type), ctors := fields} :: types
  return (.inductDecl target.levelParams target.numParams types.reverse false, ctors)

private def officialDeclaration (stx : Syntax) : CommandElabM (Environment × ConstantInfo) := do
  let moduleName ← getMainModule
  unless moduleName.getRoot == `OmegaInit do throwError "expected an OmegaInit module"
  let owner := moduleName.replacePrefix `OmegaInit `Init
  let src ← officialEnvironment owner
  let name := stx.getId
  if isPrivateName name || name.hasMacroScopes then
    throwErrorAt stx "expected a public declaration"
  let some idx := src.getModuleIdxFor? name | throwErrorAt stx "unknown upstream declaration"
  unless src.header.moduleNames[idx]! == owner do throwErrorAt stx "expected a declaration from {owner}"
  let some info := src.find? name | throwErrorAt stx "missing upstream declaration"
  if name.isInternalOrNum then
    let some parent := src.find? name.getPrefix | throwErrorAt stx "missing the enclosing official definition"
    let some body := parent.value? (allowOpaque := true) | throwErrorAt stx "missing the enclosing official body"
    unless body.getUsedConstants.contains name do throwErrorAt stx "expected an official implementation dependency"
  if info.isAxiom || info.isUnsafe || info.isPartial then throwErrorAt stx "inadmissible declaration"
  return (src, info)

@[command_parser, builtin_command_parser] def portProof := leading_parser
  "port_proof " >> ident >> optional (" using " >> ident) >> optional " by_reflexivity"

@[builtin_command_elab portProof] def elabPortProof : CommandElab := fun stx => do
  let (src, info) ← officialDeclaration stx[1]
  let type ← ofExcept (translateProofTerm src info.type)
  let target := {info.toConstantVal with name := omegaName info.name, type}
  let levels := target.levelParams.map Level.param
  let implementation ← if stx[2].isNone then pure none
    else some <$> liftTermElabM (realizeGlobalConstNoOverloadWithInfo stx[2][1])
  liftCoreM <| withExporting do
    unless ← Meta.MetaM.run' (Meta.isProp target.type) do throwError "expected a proof interface"
    if !stx[3].isNone then
      if implementation.isSome then throwError "specify only one proof implementation"
      let some term := elementaryProof? (← getEnv) type | throwError "no reflexivity or assumption proof"
      Lean.addDecl (.thmDecl {target with value := term, all := [target.name]})
    else if let some proof := implementation then
      Lean.addDecl (.thmDecl {target with value := mkConst proof levels, all := [target.name]})
    else
      match info with
      | .thmInfo proof =>
        Lean.addDecl (.thmDecl {target with value := ← ofExcept (translateProofTerm src proof.value), all := [target.name]})
      | .defnInfo proof =>
        let definition := {proof with
          toConstantVal := target
          value := ← ofExcept (translateProofTerm src proof.value)
          all := proof.all.map omegaName}
        Lean.addDecl (.defnDecl definition) (forceExpose := proof.hints == .abbrev)
        setReducibilityStatus target.name (getReducibilityStatusCore src info.name)
      | _ => throwError "this proof needs a constructive implementation"
    if isProtected src info.name then modifyEnv (addProtected · target.name)

@[command_parser, builtin_command_parser] def portCompilerMarkers := leading_parser "port_compiler_markers"

@[builtin_command_elab portCompilerMarkers] def elabPortCompilerMarkers : CommandElab := fun _ => do
  unless (← getMainModule) == `OmegaInit.Prelude do throwError "expected OmegaInit.Prelude"
  for name in OmegaChecks.InitPort.CompilerMarkers.names do
    let .opaqueInfo marker := OmegaChecks.InitPort.CompilerMarkers.declaration name | unreachable!
    let .ok checked := (← getEnv).addDeclCore 0 1000 (.opaqueDecl marker) none
      | throwError "kernel rejected native compiler marker {name}"
    setEnv checked

@[command_parser, builtin_command_parser] def portDefinition := leading_parser
  "port_definition " >> ident >> optional " with_native_code"

@[builtin_command_elab portDefinition] def elabPortDefinition : CommandElab := fun stx => do
  let (src, .defnInfo defn) ← officialDeclaration stx[1] | throwError "expected a safe definition"
  liftCoreM <| withExporting do
    let value ← ofExcept (translateProofTerm src defn.value)
    let type ← ofExcept (translateProofTerm src defn.type)
    let name := omegaName defn.name
    Lean.addDecl (.defnDecl {defn with name, type, value, all := defn.all.map omegaName}) (forceExpose := true)
    if isAuxRecursor src defn.name then modifyEnv (markAuxRecursor · name)
    -- When code generation is optional, the compiler records unsupported definitions as
    -- noncomputable. Explicit native callers require a successful compilation.
    withOptions (fun opts => Elab.async.set opts false) do
      Lean.compileDecls #[name] (logErrors := !stx[2].isNone)
    setReducibilityStatus name (getReducibilityStatusCore src defn.name)
    if isProtected src defn.name then modifyEnv (addProtected · name)

@[command_parser, builtin_command_parser] def portInductive := leading_parser "port_inductive " >> ident

@[builtin_command_elab portInductive] def elabPortInductive : CommandElab := fun stx => do
  let (src, info) ← officialDeclaration stx[1]
  let name := info.name
  let owner := (← getMainModule).replacePrefix `OmegaInit `Init
  liftCoreM <| withExporting do
    let (decl, ctors) ← sourceGroup src owner name
    let .inductDecl _ _ types _ := decl | unreachable!
    Lean.addDecl decl
    compilerLayouts (types.toArray.map (·.name)) ctors
    for typ in types do
      Meta.MetaM.run' <| mkCasesOn typ.name
      Meta.MetaM.run' <| mkRecOn typ.name
    let some idx := src.getModuleIdx? owner | throwError "missing owner {owner}"
    for cls in classExtension.getModuleEntries src idx do
      if types.any (·.name == omegaName cls.name) then
        -- Use the registration from the owning module, including its out parameters.
        modifyEnv fun env => classExtension.addEntry env {cls with name := omegaName cls.name}


/-- Bootstrap proof-valued records with the pinned projection-based eliminators even
before the root PUnit used by Lean's ordinary structure elaborator is available. -/
@[command_parser, builtin_command_parser] def portPropRecord := leading_parser "port_prop_record " >> ident

@[builtin_command_elab portPropRecord] def elabPortPropRecord : CommandElab := fun stx => do
  let id : Ident := ⟨stx[1]⟩
  let (src, ci) ← officialDeclaration id
  let some info := getStructureInfo? src ci.name | throwErrorAt id "expected an official record"
  unless info.parentInfo.isEmpty && ci.type.getForallBody.isProp do
    throwErrorAt id "expected a proof-valued record with no parent"
  elabCommand (← `(command| port_inductive $id:ident))
  let mut fields := #[]
  for field in info.fieldNames do
    let some entry := getFieldInfo? src ci.name field | throwErrorAt id "missing field {field}"
    let some proj := src.getProjectionFnInfo? entry.projFn | throwErrorAt id "missing projection {field}"
    let projection := mkIdentFrom id entry.projFn
    elabCommand (← `(command| port_proof $projection:ident))
    let strictName := omegaName entry.projFn
    modifyEnv fun env => addProjectionFnInfo env strictName (omegaName proj.ctorName)
      proj.numParams proj.i proj.fromClass
    fields := fields.push {entry with projFn := strictName}
  modifyEnv fun env => registerStructure env {structName := omegaName ci.name, fields}

/-- Elaborate a pinned record and compile its projections in dependency order. -/
@[command_parser, builtin_command_parser] def portNativeRecords := leading_parser "port_native_records " >> sepBy1 ident ","

@[builtin_command_elab portNativeRecords] def elabPortNativeRecords : CommandElab := fun stx => do
  for id in stx[1].getSepArgs do
    let (src, ci) ← officialDeclaration id
    let some record := getStructureInfo? src ci.name | throwErrorAt id "expected an official record"
    let type := mkIdentFrom id ci.name
    elabCommand (← `(command| port_inductive $type:ident))
    for field in record.fieldNames do
      let some projection := getFieldInfo? src ci.name field | throwErrorAt id "missing projection {field}"
      let name := mkIdentFrom id projection.projFn
      elabCommand (← `(command| port_definition $name:ident with_native_code))

/-- Compile the pinned constructor index and typed elimination functions of each inductive. -/
@[command_parser, builtin_command_parser] def portConstructorEliminators := leading_parser
  "port_constructor_eliminators " >> sepBy1 ident ","

@[builtin_command_elab portConstructorEliminators] def elabPortConstructorEliminators : CommandElab := fun stx => do
  for id in stx[1].getSepArgs do
    let (_, .inductInfo info) ← officialDeclaration id | throwErrorAt id "expected an official inductive"
    let ctorIdx := mkIdentFrom id (mkCtorIdxName info.name)
    let elimType := mkIdentFrom id (info.name ++ `ctorElimType)
    let ctorElim := mkIdentFrom id (mkCtorElimName info.name)
    elabCommand (← `(command| port_definition $ctorIdx:ident with_native_code))
    elabCommand (← `(command| port_definition $elimType:ident))
    elabCommand (← `(command| port_definition $ctorElim:ident with_native_code))
    for ctor in info.ctors do
      let elim := mkIdentFrom id (ctor ++ `elim)
      elabCommand (← `(command| port_definition $elim:ident with_native_code))

/-- Verify each constructor equation for an unindexed structural argument. Later arguments must
be independent of that parameter, so replacing it preserves their local types. -/
private def checkConstructorEquations (name : Name) (levelParams : List Name) (type body : Expr)
    (structural : Nat) : MetaM Unit := do
  let levels := levelParams.map Level.param
  Meta.forallTelescope type fun args _ => do
    let some arg := args[structural]? | throwError "missing structural argument"
    let family ← Meta.whnf (← Meta.inferType arg)
    let .const indName us := family.getAppFn | throwError "expected an inductive parameter"
    let .inductInfo ind ← getConstInfo indName | throwError "expected an inductive parameter"
    unless ind.numIndices == 0 && family.getAppNumArgs == ind.numParams && !ind.ctors.isEmpty do
      throwError "expected a nonempty unindexed inductive family"
    for next in args[structural+1:] do
      if (← Meta.inferType next).containsFVar arg.fvarId! then throwError "dependent later argument"
    for ctorName in ind.ctors do
      let ctor := mkAppN (mkConst ctorName us) family.getAppArgs
      Meta.forallTelescope (← Meta.inferType ctor) fun fields _ => do
        let inputs := args.set! structural (mkAppN ctor fields)
        let actual := mkAppN (mkConst name levels) inputs
        let expected := mkAppN body inputs
        unless Kernel.isDefEqGuarded (← getEnv) (← getLCtx) actual expected do
          throwError "recursive equation does not match {name} at {ctorName}"

@[command_parser, builtin_command_parser] def portStructuralCode := leading_parser
  "port_structural_code " >> ident >> " on_arg " >> numLit

open Compiler.LCNF in
@[builtin_command_elab portStructuralCode] def elabPortStructuralCode : CommandElab := fun stx => do
  let (src, info) ← officialDeclaration stx[1]
  let name := omegaName info.name
  let equationName := Compiler.mkUnsafeRecName info.name
  let some (.defnInfo recFn) := src.find? equationName | throwError "missing recursive equations"
  unless recFn.safety == .partial && recFn.all == [equationName] do throwError "expected a single recursive definition"
  liftCoreM <| withExporting do
    let value ← ofExcept (translateProofTerm src recFn.value)
    for dep in value.getUsedConstants do
      unless dep == omegaName equationName || (← getEnv).contains dep do throwError "missing equation dependency {dep}"
    let body := value.replace fun e => if e.isConstOf (omegaName equationName) then some (.const name e.constLevels!) else none
    let tmp := {recFn with
      name := omegaName equationName
      all := [omegaName equationName]
      safety := .safe
      type := ← ofExcept (translateProofTerm src recFn.type)
      value := body}
    let some pos := stx[3].isNatLit? | throwErrorAt stx[3] "expected a structural argument position"
    if pos == 0 then throwErrorAt stx[3] "argument positions start at one"
    Meta.MetaM.run' <| checkConstructorEquations name tmp.levelParams tmp.type body (pos - 1)
    -- Lean uses this reserved name for executable recursive equations. The safe one-step
    -- definition can call the already checked total function. Its environment is disposable.
    let compiled ← withoutModifyingEnv do
      modifyEnv (noncomputableExt.modifyState · (·.erase name))
      Lean.addDecl (.defnDecl tmp) (forceExpose := true)
      withOptions (fun o => (Elab.async.set o false).setBool `compiler.postponeCompile false) do
        Lean.compileDecls #[name] (logErrors := true)
      return ← getEnv
    let original ← getEnv
    -- Reattach generated code in backend order, including recursive workers and lifted closures.
    let names := (declOrderExt.getState compiled).1.reverse.toArray.filter fun n =>
      !(declOrderExt.getState original).2.contains n

    unless names.contains name do throwError "no recursive code generated"
    modifyEnv fun env => PersistentEnvExtension.modifyState noncomputableExt env fun (entries, marked) =>
      (entries.filter (· != name), marked.erase name)
    for n in names do
      if let some decl := baseExt.getState compiled |>.find? n then modifyEnv (saveBaseDeclCore · decl)
      if let some decl := monoExt.getState compiled |>.find? n then modifyEnv (saveMonoDeclCore · decl)
      if let some decl := impureExt.getState compiled |>.find? n then modifyEnv (saveImpureDeclCore · decl)
      if let some ir := IR.declMapExt.getState compiled |>.find? n then modifyEnv (IR.declMapExt.addEntry · ir)
      if isDeclPublic compiled n then modifyEnv (setDeclPublic · n)
      modifyEnv (recordFinalImpureDecl · n)
end OmegaChecks.InitCompiler
