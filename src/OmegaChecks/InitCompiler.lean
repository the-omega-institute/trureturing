import Lean
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.PublicDeclsExt
import Lean.Compiler.IR.CompilerM
import OmegaChecks.InitCompiler.RootNames
import OmegaChecks.InitCompiler.StructuralEquations
import OmegaChecks.InitCompiler.NaturalBootstrap
import OmegaChecks.InitCompiler.Layout
import OmegaChecks.InitCompiler.Proofs
import OmegaChecks.InitCompiler.CompilerMarkers

/-! Elaborate pinned Init declarations in strict prelude modules. -/

open Lean Parser Elab Command
namespace OmegaChecks.InitCompiler

@[command_parser, builtin_command_parser] def physicalNaturals := leading_parser "port_kernel_naturals"
@[builtin_command_elab physicalNaturals] def elabPhysicalNaturals : CommandElab := fun _ => installNaturalBootstrap

open Compiler.LCNF in
private def installCompiledCode (compiled : Environment) (name : Name) : CoreM Unit := do
  let original ← getEnv
  -- Reattach generated code in backend order, including recursive workers and lifted closures.
  let names := (declOrderExt.getState compiled).1.reverse.toArray.filter fun n =>
    !(declOrderExt.getState original).2.contains n

  unless names.contains name do throwError m!"no executable code generated for {name}"
  modifyEnv fun env => PersistentEnvExtension.modifyState noncomputableExt env fun (entries, marked) =>
    (entries.filter (· != name), marked.erase name)
  for n in names do
    if let some decl := baseExt.getState compiled |>.find? n then modifyEnv (saveBaseDeclCore · decl)
    if let some decl := monoExt.getState compiled |>.find? n then modifyEnv (saveMonoDeclCore · decl)
    if let some decl := impureExt.getState compiled |>.find? n then modifyEnv (saveImpureDeclCore · decl)
    if let some ir := IR.declMapExt.getState compiled |>.find? n then modifyEnv (IR.declMapExt.addEntry · ir)
    if isDeclPublic compiled n then modifyEnv (setDeclPublic · n)
    modifyEnv (recordFinalImpureDecl · n)

@[command_parser, builtin_command_parser] def quotientInterfaces := leading_parser "port_quotient_interfaces"
@[builtin_command_elab quotientInterfaces] def elabQuotientInterfaces : CommandElab := fun _ => do
  unless (← getMainModule) == `OmegaInit.Prelude do throwError "expected OmegaInit.Prelude"
  let pinned ← officialEnvironment `Init.Prelude
  liftCoreM <| withExporting do
    for name in RootNames.quotientPrimitives do
      let wrapper := RootNames.quotientInterface (← getConstInfo name)
      Lean.addDecl (.defnDecl wrapper) (forceExpose := true)
      unless name == `Quot.mk || name == `Quot.lift do continue
      let compiled ← withoutModifyingEnv do
        -- Lean's compiler erases this internal inverse when it lowers Quot.lift.
        -- Only the resulting executable code is exported from the temporary environment.
        let some (.axiomInfo inverse) := pinned.find? `Quot.lcInv
          | throwError "missing pinned quotient compiler primitive"
        unless inverse.isUnsafe do throwError "unexpected quotient compiler primitive"
        Lean.addDecl (.axiomDecl inverse)
        withOptions (fun o => (Elab.async.set o false).setBool `compiler.postponeCompile false) do
          Lean.compileDecls #[wrapper.name] (logErrors := true)
        return ← getEnv
      installCompiledCode compiled wrapper.name

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

/-- The equation compiler can place a generated proof under the original function even when
a nested worker consumes it. Follow only its own implementation declarations. -/
private partial def referencesHelper (src : Environment) (root target : Name) (pending : List Name)
    (visited : NameSet := {}) : Bool :=
  match pending with
  | [] => false
  | name :: rest => Id.run do
    if name == target then return true
    if visited.contains name then return referencesHelper src root target rest visited
    let used := (src.find? name >>= (·.value? (allowOpaque := true))).map (·.getUsedConstants)
    let localNames := (used.getD #[]).toList.filter root.isPrefixOf
    return referencesHelper src root target (localNames ++ rest) (visited.insert name)

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
    let parent := name.getPrefix
    let structureName := parent.getPrefix
    let field := parent.replacePrefix structureName .anonymous
    let fieldDefault := (getStructureInfo? src structureName).isSome &&
      (getStructureFieldsFlattened src structureName false).contains field &&
      getEffectiveDefaultFnForField? src structureName field == some name
    let flatCtor := (getStructureInfo? src structureName).isSome &&
      mkFlatCtorOfStructCtorName (getStructureCtor src structureName).name == name
    unless fieldDefault || flatCtor || ((src.find? parent).isSome && referencesHelper src parent name [parent]) do
      throwErrorAt stx "expected an official implementation dependency"
  if info.isAxiom || info.isUnsafe || info.isPartial then throwErrorAt stx "inadmissible declaration"
  return (src, info)

@[command_parser, builtin_command_parser] def portProof := leading_parser
  "port_proof " >> ident >> optional (" using " >> ident) >> optional (" by_reflexivity" <|> " by_finite_cases")

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
      let term ← if stx[3][0].getAtomVal == "by_finite_cases" then do
        let some body ← finiteProof? src info.type | throwError "no finite case proof for {info.name}"
        ofExcept (translateProofTerm src body)
      else do
        let some body := elementaryProof? (← getEnv) type | throwError "no reflexivity or assumption proof"
        pure body
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

/-- Use a checked constructive implementation of an official theorem or definition. -/
@[command_parser, builtin_command_parser] def portAlternativeProof := leading_parser
  ("port_alternative_proof " <|> "port_alternative_definition ") >> ident >> " from " >> ident

@[builtin_command_elab portAlternativeProof] def elabPortAlternativeProof : CommandElab := fun stx => do
  let (src, info) ← officialDeclaration stx[1]
  let scope := `OmegaChecks.InitPort.Alternatives
  let owner := stx[3].getId
  let isProof := stx[0].getAtomVal == "port_alternative_proof"
  unless scope.isPrefixOf owner && info.isTheorem == isProof do throwError "unexpected alternative kind or module"
  let model ← importModules #[{module := owner}] {} (level := .private)
  let name := scope ++ info.name
  let some alt := model.find? name | throwError "missing constructive implementation {name}"
  unless alt.isTheorem == isProof && !alt.isUnsafe && !alt.isPartial &&
      model.getModuleIdxFor? name == model.getModuleIdx? owner do throwError "unexpected implementation {name}"
  let value ← match alt with
    | .thmInfo th => pure th.value
    | .defnInfo d => pure d.value
    | _ => throwError "expected a definition or theorem body for {name}"
  let localHelper := fun n => isPrivateName n && (model.getModuleIdxFor? n).any fun i =>
    scope.isPrefixOf model.header.moduleNames[i]!
  let body ← (Meta.deltaExpand value localHelper (allowOpaque := true)).toIO'
    {fileName := "<constructive implementation>", fileMap := default} {env := model}
  let params := (collectLevelParams {} alt.type).params.toList
  let levels := (collectLevelParams {} info.type).params.toList.map Level.param
  unless params.length == levels.length do throwError "different universe binders"
  liftCoreM do
    let type ← ofExcept (translateProofTerm src info.type)
    let value ← ofExcept (translateProofTerm src (body.instantiateLevelParams params levels))
    let target := omegaName info.name
    if isProof then
      withExporting <| Lean.addDecl (.thmDecl {info.toConstantVal with name := target, type, value, all := [target]})
    else
      let .defnInfo original := info | throwError "expected a safe definition"
      withoutExporting <| Lean.addDecl (.defnDecl {original with name := target, type, value, all := [target]})
      setReducibilityStatus target .irreducible
      withExporting <| withOptions (fun o => Elab.async.set o false) do
        Lean.compileDecls #[target] (logErrors := true)
    if isProtected src info.name then modifyEnv (addProtected · target)

@[command_parser, builtin_command_parser] def portCompilerMarkers := leading_parser "port_compiler_markers"

@[builtin_command_elab portCompilerMarkers] def elabPortCompilerMarkers : CommandElab := fun _ => do
  unless (← getMainModule) == `OmegaInit.Prelude do throwError "expected OmegaInit.Prelude"
  for name in OmegaChecks.InitPort.CompilerMarkers.names do
    let .opaqueInfo marker := OmegaChecks.InitPort.CompilerMarkers.declaration name | unreachable!
    let .ok checked := (← getEnv).addDeclCore 0 1000 (.opaqueDecl marker) none
      | throwError "kernel rejected native compiler marker {name}"
    setEnv checked

/-- The strict seed keeps ByteArray.data in field zero and owns capacity and linearity. -/
private def installByteExtern (src : Environment) (name : Name) : CoreM Unit := do
  let spec : Option (String × String × Array (IR.IRType × Bool) × IR.IRType) := match name with
    | `ByteArray.mk => some ("lean_byte_array_mk", "omega_byte_array_mk", #[(.object, false)], .object)
    | `ByteArray.emptyWithCapacity => some ("lean_mk_empty_byte_array", "omega_byte_array_empty", #[(.tobject, true)], .object)
    | `ByteArray.push => some ("lean_byte_array_push", "omega_byte_array_push", #[(.object, false), (.uint8, false)], .object)
    | _ => none
  let some (target, symbol, args, result) := spec | return
  let some (.extern _ ps ret ⟨[.standard `all upstream]⟩) := IR.findEnvDecl src name
    | throwError "missing pinned native primitive {name}"
  unless upstream == target && ps.map (fun p => (p.ty, p.borrow)) == args && ret == result do
    throwError "incompatible pinned native primitive {name}"
  let n := omegaName name
  modifyEnv fun env => externAttr.ext.addEntry (asyncDecl := n) env (n, ⟨[.standard `all symbol]⟩)

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
    if isSparseCasesOn src defn.name then modifyEnv (markSparseCasesOn · name)
    installByteExtern src defn.name
    -- Unfold before compiling arguments, so untaken branches of the pinned ite stay lazy.
    if Compiler.hasMacroInlineAttribute src defn.name then
      setEnv (← ofExcept (Compiler.setInlineAttribute (← getEnv) name .macroInline))
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
    for exported in types.toArray.map (·.name) ++ ctors do
      if isProtected src (exported.replacePrefix `Omega .anonymous) then
        modifyEnv (addProtected · exported)
    compilerLayouts (types.toArray.map (·.name)) ctors
    if name == `ByteArray then
      installByteExtern src `ByteArray.mk
      Lean.compileDecls #[`Omega.ByteArray.mk] (logErrors := true)
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
    let mut fields := #[]
    for field in record.fieldNames do
      let some projection := getFieldInfo? src ci.name field | throwErrorAt id "missing projection {field}"
      let name := mkIdentFrom id projection.projFn
      if (src.find? projection.projFn).any (·.isTheorem) then
        elabCommand (← `(command| port_proof $name:ident))
      else
        elabCommand (← `(command| port_definition $name:ident with_native_code))
      let some info := src.getProjectionFnInfo? projection.projFn | throwErrorAt id "missing projection info {field}"
      modifyEnv fun env => addProjectionFnInfo env (omegaName projection.projFn) (omegaName info.ctorName)
        info.numParams info.i info.fromClass
      fields := fields.push {projection with
        projFn := omegaName projection.projFn
        subobject? := projection.subobject?.map omegaName}
    let parents := record.parentInfo.map fun parent =>
      {parent with structName := omegaName parent.structName, projFn := omegaName parent.projFn}
    modifyEnv fun env => registerStructure env {structName := omegaName ci.name, fields}
    setStructureParents (omegaName ci.name) parents
    for field in getStructureFieldsFlattened src ci.name false do
      if let some defaultFn := getEffectiveDefaultFnForField? src ci.name field then
        unless (← getEnv).contains (omegaName defaultFn) do
          let name := mkIdentFrom id defaultFn
          elabCommand (← `(command| port_definition $name:ident with_native_code))
    let flatCtor := mkFlatCtorOfStructCtorName (getStructureCtor src ci.name).name
    if src.contains flatCtor then
      let name := mkIdentFrom id flatCtor
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

@[command_parser, builtin_command_parser] def portStructuralCode := leading_parser
  "port_structural_code " >> optional "private " >> ident >> " on_arg " >> numLit

open Compiler.LCNF in
@[builtin_command_elab portStructuralCode] def elabPortStructuralCode : CommandElab := fun stx => do
  let (src, info, name) ← if stx[1].isNone then do
    let (src, info) ← officialDeclaration stx[2]
    pure (src, info, omegaName info.name)
  else do
    let owner ← getMainModule
    unless owner.getRoot == `OmegaInit do throwError "expected an OmegaInit module"
    let pinned := owner.replacePrefix `OmegaInit `Init
    let src ← officialEnvironment pinned
    let helper := stx[2].getId
    let some (.defnInfo d) := src.find? (mkPrivateNameCore pinned helper)
      | throwErrorAt stx[2] "missing private upstream definition"
    unless d.safety == .safe do throwErrorAt stx[2] "expected a total private definition"
    let name := mkPrivateNameCore owner (omegaName helper)
    liftCoreM <| withoutExporting do
      let type ← ofExcept (translateProofTerm src d.type)
      let value ← ofExcept (translateProofTerm src d.value)
      Lean.addDecl (.defnDecl {d with name, type, value, all := [name]})
    pure (src, .defnInfo d, name)
  let equationName := Compiler.mkUnsafeRecName info.name
  let some (.defnInfo recFn) := src.find? equationName | throwError "missing recursive equations"
  unless recFn.safety == .partial && recFn.all == [equationName] do throwError "expected a single recursive definition"
  liftCoreM <| withExporting (isExporting := !isPrivateName name) do
    let body ← ofExcept (translateRecursiveBody src recFn name)
    for dep in body.getUsedConstants do
      unless (← getEnv).contains dep do throwError "missing equation dependency {dep}"
    let tmp := {recFn with
      name := Compiler.mkUnsafeRecName name
      all := [Compiler.mkUnsafeRecName name]
      safety := .safe
      type := ← ofExcept (translateProofTerm src recFn.type)
      value := body}
    let some pos := stx[4].isNatLit? | throwErrorAt stx[4] "expected a structural argument position"
    if pos == 0 then throwErrorAt stx[4] "argument positions start at one"
    Meta.MetaM.run' <| checkConstructorEquations name tmp.levelParams tmp.type body (pos - 1)
    -- Lean uses this reserved name for executable recursive equations. The safe one-step
    -- definition can call the already checked total function. Its environment is disposable.
    let compiled ← withoutModifyingEnv do
      modifyEnv (noncomputableExt.modifyState · (·.erase name))
      Lean.addDecl (.defnDecl tmp) (forceExpose := true)
      withOptions (fun o => (Elab.async.set o false).setBool `compiler.postponeCompile false) do
        Lean.compileDecls #[name] (logErrors := true)
      return ← getEnv
    installCompiledCode compiled name
end OmegaChecks.InitCompiler
