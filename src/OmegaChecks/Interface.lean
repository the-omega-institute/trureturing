import Lean
import OmegaChecks.FieldMethods

/-! Compare compiled public interfaces in independent Lean environments. -/

open Lean

namespace OmegaChecks.Interface

private def official (n : Name) : Name :=
  n.replacePrefix `Omega Name.anonymous

private partial def translate (rename : Name → Name) (e : Expr) : Expr := Id.run do
  -- Replace constants and kernel projections, including their target expressions.
  return e.replace fun
    | .const n us => some (.const (rename n) us)
    | .proj n i target => if rename n != n then some (.proj (rename n) i (translate rename target)) else none
    | _ => none

private def same (env : Environment) (lhs rhs : Expr) : Bool :=
  Kernel.isDefEqGuarded env {} lhs rhs

private def lookup (env : Environment) (name : Name) : IO ConstantInfo := do
  let some info := env.find? name | throw <| IO.userError s!"missing interface declaration {name}"
  return info

private def ownerOf (env : Environment) (name : Name) : IO Name := do
  let some owner := env.getModuleIdxFor? name | throw <| IO.userError s!"missing owner for {name}"
  return env.header.modules[owner]!.module

/-- Independent official modules can emit the same name. The importer's owner
index and its active term can come from different copies. Read the stored entry. -/
def declaredIn (env : Environment) (name owner : Name) : Bool := Id.run do
  let some expected := env.getModuleIdx? owner | return false
  let some info := env.find? name | return false
  let some entry := env.header.moduleData[expected]!.constants.find? (·.name == name) | return false
  if let .thmInfo a := entry then
    let .thmInfo b := info | return false
    -- Structural equality includes binder names and annotations. The kernel identifies
    -- proofs of the same proposition, including distinct compiler-generated proofs.
    return a.levelParams == b.levelParams && a.type.equal b.type
  unless entry == info && entry.type.equal info.type do return false
  if let .recInfo a := entry then
    let .recInfo b := info | return false
    return (a.rules.zip b.rules).all fun (x, y) => x.rhs.equal y.rhs
  return (entry.value? (allowOpaque := true)).map ExprStructEq.mk ==
    (info.value? (allowOpaque := true)).map ExprStructEq.mk

/-- Kernel conversion ignores elaborator binder visibility and named-argument labels. -/
private partial def compatibleBinders (env : Environment) (ctx : LocalContext) (depth : Nat)
    (src dst : Expr) : Bool := Id.run do
  let .ok a := Kernel.whnf env ctx src | return false
  let .ok b := Kernel.whnf env ctx dst | return false
  match a, b with
  | .forallE s sd sb si, .forallE t td tb ti =>
    if si != ti || (!s.isAnonymous && !s.hasMacroScopes && s != t) then return false
    if !compatibleBinders env ctx depth sd td then return false
    let id : FVarId := ⟨.num `_interface depth⟩
    let ctx := ctx.mkLocalDecl id t td ti
    return compatibleBinders env ctx (depth+1)
      (sb.instantiate1 (.fvar id)) (tb.instantiate1 (.fvar id))
  | .forallE .., _ | _, .forallE .. => return false
  | _, _ => return true

private def requireSame (env : Environment) (name : Name) (label : String) (lhs rhs : Expr) : IO Unit := do
  if let .error _ := Kernel.check env {} lhs then
    throw <| IO.userError s!"ill-typed translated {label} for {name}"
  unless same env lhs rhs do
    throw <| IO.userError s!"{label} mismatch for {name}"

private def certificateName (officialName : Name) : Name :=
  `OmegaChecks.Interface.Equations ++ officialName

/-- Check an all-input equation against the actual translated code and the official constant. -/
private def checkEquation (env : Environment) (src dst : ConstantInfo) (body : Expr) : IO Unit := do
  let certName := certificateName dst.name
  let some cert := env.find? certName | throw <| IO.userError s!"missing computation correspondence for {src.name}"
  unless cert.isTheorem && (`OmegaChecks.Interface.Equations).isPrefixOf (← ownerOf env certName) do
    throw <| IO.userError s!"invalid computation certificate {certName}"
  let levels := dst.levelParams.map Level.param
  let expected : MetaM Expr := Meta.forallTelescope dst.type fun xs _ => do
    let equation ← Meta.mkEq (mkAppN body xs) (mkAppN (.const dst.name levels) xs)
    Meta.mkForallFVars xs equation
  let expected ← expected.run' |>.toIO' {fileName := "<interface>", fileMap := default} {env}
  unless cert.numLevelParams == dst.numLevelParams do
    throw <| IO.userError s!"certificate universe arity mismatch for {src.name}"
  requireSame env src.name "certificate statement" expected (cert.type.instantiateLevelParams cert.levelParams levels)
  let axioms ← (collectAxioms certName : CoreM _).toIO' {fileName := "<interface>", fileMap := default} {env}
  for ax in axioms do
    unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
      throw <| IO.userError s!"inadmissible axiom {ax} in {certName}"

private def compare (reference : Environment) (rename : Name → Name) (src dst : ConstantInfo)
    (foundation : Option (Environment × Environment) := none) :
    IO (Array Name) := do
  let liftTerm := fun (e : Expr) =>
    translate rename (e.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param))
  unless src.numLevelParams == dst.numLevelParams &&
      compatibleBinders reference {} 0 (liftTerm src.type) dst.type do
    throw <| IO.userError s!"public binder mismatch for {src.name}"
  requireSame reference src.name "interface type" (liftTerm src.type) dst.type
  let mut deps := src.type.getUsedConstants
  match src, dst with
  | .thmInfo _, _ =>
    -- The official proof can be a constructor or projection. Kernel proof irrelevance
    -- identifies inhabitants once both declaration types are the same proposition.
    unless (Kernel.check reference {} dst.type).toOption.any (same reference (.sort .zero)) do
      throw <| IO.userError s!"official declaration is not a proof for {src.name}"
  | .defnInfo x, .defnInfo y =>
    unless x.safety == y.safety do
      throw <| IO.userError s!"definition safety mismatch for {src.name}"
    if x.safety != .safe then
      -- A partial or unsafe implementation may refer to itself. Compare the compiled
      -- bodies directly, since Kernel.check checks expressions in the safe fragment.
      unless same reference (liftTerm x.value) y.value do
        throw <| IO.userError s!"partial or unsafe definition body mismatch for {src.name}"
      return deps ++ x.value.getUsedConstants
    deps := deps ++ x.value.getUsedConstants
    compareDefinitionBody
  | .defnInfo _, _ | .opaqueInfo _, _ =>
    compareDefinitionBody
    deps := deps ++ (src.value! (allowOpaque := true)).getUsedConstants
  | .inductInfo x, .inductInfo y =>
    unless x.numParams == y.numParams && x.numIndices == y.numIndices &&
        x.numNested == y.numNested && x.all.map rename == y.all &&
        x.ctors.map rename == y.ctors do
      throw <| IO.userError s!"inductive shape mismatch for {src.name}"
    deps := deps ++ x.all.toArray ++ x.ctors.toArray ++ #[x.name ++ `rec]
  | .ctorInfo x, .ctorInfo y =>
    unless rename x.induct == y.induct && x.cidx == y.cidx && x.numFields == y.numFields &&
        x.numParams == y.numParams do
      throw <| IO.userError s!"constructor mismatch for {src.name}"
    deps := deps.push x.induct
  | .recInfo x, .recInfo y =>
    unless x.all.map rename == y.all && x.numParams == y.numParams && x.numIndices == y.numIndices &&
        x.numMotives == y.numMotives && x.numMinors == y.numMinors && x.k == y.k &&
        x.rules.length == y.rules.length do
      throw <| IO.userError s!"recursor mismatch for {src.name}"
    for (a,b) in x.rules.zip y.rules do
      unless rename a.ctor == b.ctor && a.nfields == b.nfields do
        throw <| IO.userError s!"recursor case mismatch for {src.name}"
      requireSame reference src.name "recursor reduction" (liftTerm a.rhs) b.rhs
      deps := deps ++ a.rhs.getUsedConstants ++ #[a.ctor]
  | _, _ => throw <| IO.userError s!"unsupported or different declaration kind for {src.name}"
  return deps
where
  compareDefinitionBody : IO Unit := do
    let value := src.value! (allowOpaque := true)
    let body := translate rename (value.instantiateLevelParams src.levelParams (dst.levelParams.map Level.param))
    if let .error _ := Kernel.check reference {} body then
      throw <| IO.userError s!"ill-typed translated definition for {src.name}"
    let target := mkConst dst.name (dst.levelParams.map Level.param)
    let mut hidden := false
    if let some (_, publicStrict) := foundation then
      let exposed ← lookup publicStrict src.name
      hidden := exposed.isAxiom || exposed matches .opaqueInfo _
    -- The kernel cannot unfold an opaque constant. For opaque consumer declarations,
    -- compare the stored bodies directly and leave their dependencies in the audit.
    let identicalOpaqueConsumer := foundation.isNone && (src matches .opaqueInfo _) &&
      (dst matches .opaqueInfo _) && (dst.value? (allowOpaque := true)).any body.equal
    if !identicalOpaqueConsumer && !same reference body target then
      unless hidden do
        throw <| IO.userError s!"computed definition mismatch for {src.name}"
      checkEquation reference src dst body
    -- Legacy importers load the private olean, including bodies convertible in the kernel.
    if let some (strict, _) := foundation then
      if src matches .defnInfo _ then
        if hidden && getReducibilityStatusCore strict src.name != .irreducible then
          throw <| IO.userError s!"legacy importer can unfold the hidden implementation of {src.name}"

/-- Compare every binding and every strict foundation dependency exposed by its interface. -/
def check (strict publicStrict reference : Environment) (bindings : Array (Name × Name)) : IO Unit := do
  let mut pending := bindings
  let mut seen : NameSet := {}
  while let some (name, owner) := pending.back? do
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      let dst := official name
      unless declaredIn reference dst owner do
        throw <| IO.userError s!"upstream module mismatch for {name}"
      let deps ← compare reference official (← lookup strict name) (← lookup reference dst)
        (some (strict, publicStrict))
      for dep in deps do
        let owner ← ownerOf strict dep
        let target := match owner.getRoot with
          | `OmegaInit => owner.replacePrefix `OmegaInit `Init
          | `OmegaMathlib => owner.replacePrefix `OmegaMathlib `Mathlib
          | _ => Name.anonymous
        if target.isAnonymous || dep.getRoot != `Omega then
          throw <| IO.userError s!"dependency outside the standard interface: {name} uses {dep} in {owner}"
        pending := pending.push (dep, target)
  let roots := NameSet.ofList (bindings.toList.map Prod.fst)
  IO.println s!"Verified the mathematical interfaces of {roots.size} roots and {seen.size} distinct declarations in their closure."

private def publicName (name : Name) : Bool :=
  !isPrivateName name && !name.isInternalOrNum && !name.hasMacroScopes

private def consumerExports (env : Environment) (modules : Array Name) : Array Name := Id.run do
  let mut names := #[]
  for owner in env.header.modules, data in env.header.moduleData do
    if modules.contains owner.module then
      for name in data.constNames do
        if publicName name then names := names.push name
  return names

private def consumerAliases (env : Environment) (owner : Name) : IO (Array AliasEntry) := do
  let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"missing consumer module {owner}"
  return (aliasExtension.getModuleEntries env idx).filter fun (name, _) => publicName name

/-- Restore imported name resolution from the isolated environment's compiled alias entries. -/
private def withImportedAliases (env : Environment) : Environment := Id.run do
  let mut aliases : AliasState := {}
  for idx in [:env.header.modules.size] do
    aliases := (aliasExtension.getModuleEntries env idx).foldl addAliasEntry aliases
  return aliasExtension.setState env aliases.switch

private def checkConsumerAliases (strict reference : Environment) (rename : Name → Name)
    (modules : Array Name) : IO (Array Name) := do
  let mut targets := #[]
  let sourceEnv := withImportedAliases strict
  let targetEnv := withImportedAliases reference
  for owner in modules do
    OmegaChecks.FieldMethods.check sourceEnv targetEnv owner rename
    let source ← consumerAliases strict owner
    let actual ← consumerAliases reference owner
    let expected := source.map fun (alias, target) => (alias, rename target)
    for (alias, target) in expected do
      unless actual.contains (alias, target) do
        throw <| IO.userError s!"missing consumer alias {alias} for {target} in official {owner}"
    for (alias, target) in actual do
      unless expected.contains (alias, target) do
        throw <| IO.userError s!"additional official-side consumer alias {alias} for {target} in {owner}"
    for (alias, target) in source do
      -- A declaration in an imported module can shadow an otherwise identical alias.
      let resolve := fun env => ResolveName.resolveGlobalName env {} .anonymous [] alias
      unless (resolve sourceEnv).map (fun (n, fields) => (rename n, fields)) == resolve targetEnv do
        throw <| IO.userError s!"consumer alias resolves differently: {alias} in {owner}"
      targets := targets.push target
  return targets

/-- Check compiler provenance for the standard prelude's additional inductive constructions.
An explicitly declared constant has its own source range, including one named like a generator. -/
private def derivedConsumerExport (expected : NameSet) (name : Name) : CoreM Bool := do
  let env ← getEnv
  let parent := name.getPrefix
  unless env.getModuleIdxFor? name == env.getModuleIdxFor? parent do return false
  if (← findDeclarationRangesCore? name).isSome then return false
  let some info := env.find? name | return false
  let some parentInfo := env.find? parent | return false
  if isBRecOnRecursor env parent && expected.contains parent.getPrefix then
    let go := parent ++ `go
    if name == go then
      return parentInfo.value?.any (fun body => body.getUsedConstants.contains go)
    return name == parent ++ `eq && info.isTheorem && info.type.getUsedConstants.contains parent &&
      info.type.getUsedConstants.contains go
  unless expected.contains parent do return false
  let family := match parentInfo with
    | .inductInfo i => i.name
    | .ctorInfo c => c.induct
    | _ => Name.anonymous
  if family.isAnonymous || (← findDeclarationRangesCore? family).isNone then return false
  if isAuxRecursor env name || isNoConfusion env name then return true
  if let .ctorInfo _ := parentInfo then
    return info.isTheorem && info.type.getUsedConstants.contains parent &&
      [Meta.mkInjectiveTheoremNameFor parent, Meta.mkInjectiveEqTheoremNameFor parent,
        Meta.mkSizeOfSpecLemmaName parent].contains name
  if let .inductInfo i := parentInfo then
    -- The SizeOf generator names its functions by the corresponding kernel recursor.
    -- The compiled constructor application ties even a private instance to its generated function.
    let bodyUses := fun (constant : ConstantInfo) dep =>
      constant.value?.any fun body => body.getUsedConstants.contains dep
    let instName := parent ++ `_sizeOf_inst
    if let some (.defnInfo inst) := env.find? instName then
      if inst.hints == .abbrev && inst.type.getUsedConstants.contains parent &&
          inst.type.getUsedConstants.contains `SizeOf && inst.value.getUsedConstants.contains `SizeOf.mk then
        let base := i.all.head! ++ `_sizeOf
        for (family, index) in i.all.zipIdx do
          let fn := base.appendIndexAfter (index + 1)
          if let some (.defnInfo fnInfo) := env.find? fn then
            if fnInfo.hints == .abbrev && inst.value.getUsedConstants.contains fn &&
                bodyUses (.defnInfo fnInfo) (mkRecName family) && (name == instName || name == fn) &&
                (← findDeclarationRangesCore? instName).isNone && (← findDeclarationRangesCore? fn).isNone then
              return true
    if name == mkCtorIdxName family then
      return (info.value?.any (fun body => body.getUsedConstants.contains (mkCasesOnName family))) ||
        (i.ctors.length == 1 && info.type.getUsedConstants.contains family &&
          info.type.getUsedConstants.contains `Nat)
  -- These auxiliary types occur in the types of the registered eliminators.
  for eliminator in [mkCtorElimName family, family ++ `noConfusion] do
    if isAuxRecursor env eliminator || isNoConfusion env eliminator then
      if (env.find? eliminator).any (fun elim => elim.type.getUsedConstants.contains name) then
        return true
  return false

/-- Compare the regenerated proof and every local helper it uses. -/
private def sameEquationProof (reference replay : Environment) (owner name : Name) : Bool := Id.run do
  let mut pending := [name]
  let mut seen : NameSet := {}
  while let n :: rest := pending do
    pending := rest
    unless seen.contains n do
      seen := seen.insert n
      let some idx := replay.getModuleIdxFor? n | return false
      if replay.header.moduleNames[idx]! != owner then
        if n == name then return false
        continue
      let some actualIdx := reference.getModuleIdxFor? n | return false
      if reference.header.moduleNames[actualIdx]! != owner then return false
      let some actual := reference.find? n | return false
      let some expected := replay.find? n | return false
      let (body, original) ← match actual, expected with
        | .thmInfo a, .thmInfo b => pure (a.value, b.value)
        | .defnInfo a, .defnInfo b =>
          if a.safety != b.safety then return false
          pure (a.value, b.value)
        | _, _ => return false
      if body != original || actual.type != expected.type || actual.levelParams != expected.levelParams then return false
      pending := (original.getUsedConstants ++ expected.type.getUsedConstants).toList ++ pending
  return true

/-- Recreate the upstream equations in a clean module of the same name. Lean uses the
consumer's module name in private helpers belonging to the generated proof term. -/
private def replayUpstreamEquations (reference : Environment) (names : Array Name) : IO NameSet := do
  -- The isolated import does not initialize extension state. Read the owning
  -- module's compiled matcher entries rather than inferring provenance from spelling.
  let isMatcher := fun parent =>
    (reference.getModuleIdxFor? parent).any fun idx =>
      (Meta.Match.Extension.extension.getModuleEntries reference idx).any (·.name == parent)
  let mut groups : NameMap (Array (Name × Name × Name)) := {}
  for name in names do
    let parent? := (Meta.declFromEqLikeName reference name).map Prod.fst <|> do
      let parent ← privateToUserName? name.getPrefix
      if isMatcher parent then some parent else none
    let some parent := parent? | continue
    let upstream ← ownerOf reference parent
    unless [`Init, `Std, `Mathlib, `OmegaInit, `OmegaMathlib].contains upstream.getRoot do continue
    let range ← (findDeclarationRangesCore? name : CoreM _).toIO'
      {fileName := "<consumer>", fileMap := default} {env := reference}
    if range.isSome then continue
    let owner ← ownerOf reference name
    groups := groups.insert owner ((groups.getD owner #[]).push (name, parent, upstream))
  let searchPath ← searchPathRef.get
  let mut matched : NameSet := {}
  for (owner, candidates) in groups do
    let parents := NameSet.ofList (candidates.toList.map (·.2.1))
    let upstream := NameSet.ofList (candidates.toList.map (·.2.2))
    let imports := upstream.toList.map fun n =>
      if [`OmegaInit, `OmegaMathlib].contains n.getRoot then s!"import all {n}" else s!"import {n}"
    let calls := parents.toList.flatMap fun parent =>
      if isMatcher parent then
        [s!"  discard <| Lean.Meta.Match.getEquationsForImpl `{parent}"]
      else
        [s!"  discard <| Lean.Meta.getEqnsFor? `{parent}",
         s!"  discard <| Lean.Meta.getUnfoldEqnFor? `{parent} (nonRec := true)"]
    let source := String.intercalate "\n"
      (["module", "import Lean", "public meta import Lean.Meta.Match.MatchEqs"] ++ imports ++
        ["public section", "run_meta do"] ++ calls)
    let results ← IO.FS.withTempDir fun dir => do
      let base := modToFilePath dir owner "lean"
      IO.FS.createDirAll base.parent.get!
      IO.FS.writeFile base source
      let result ← IO.Process.output {
        cmd := ((← findSysroot) / "bin" / "lean").toString
        args := #["-R", dir.toString, "-o", (base.withExtension "olean").toString, base.toString]
        env := #[("LEAN_PATH", some searchPath.toString)]}
      unless result.exitCode == 0 do
        throw <| IO.userError s!"upstream equation replay failed: {result.stdout}{result.stderr}"
      searchPathRef.set (dir :: searchPath)
      let replay ← try importModules #[{module := owner}] {} finally searchPathRef.set searchPath
      return candidates.filterMap fun (name, _, _) =>
        if sameEquationProof reference replay owner name then some name else none
    for name in results do matched := matched.insert name
  return matched

/-- Canonical name spelling used by the frozen dependency Inspector. -/
private def frozenNameKey : Name → String
  | .anonymous => "n0"
  | .str parent value => s!"ns({frozenNameKey parent},{value.utf8ByteSize}:{value})"
  | .num parent value => s!"nn({frozenNameKey parent},{value})"

structure FrozenInventory where
  moduleName : String
  paired : Array String
  officialOnly : Array String
  strictOnly : Array String
  deriving FromJson

/-- Resolve the exact frozen inventory from the compiled module, including private declarations. -/
private def frozenRoots (env : Environment) (modules : Array Name)
    (inventory : Array FrozenInventory) (keys : FrozenInventory → Array String) : IO (Array Name) := do
  let mut roots := #[]
  for entry in inventory do
    let moduleName := entry.moduleName
    let owner := moduleName.toName
    unless modules.contains owner do
      throw <| IO.userError s!"frozen inventory outside consumer comparison: {moduleName}"
    let some idx := env.getModuleIdx? owner
      | throw <| IO.userError s!"missing frozen consumer module: {moduleName}"
    let mut byKey : Std.HashMap String Name := {}
    for name in env.header.moduleData[idx]!.constNames do
      byKey := byKey.insert (frozenNameKey name) name
    for key in keys entry do
      let some name := byKey[key]?
        | throw <| IO.userError s!"frozen declaration missing from compiled comparison: {moduleName}:{key}"
      roots := roots.push name
  return roots

private def checkDerived (env : Environment) (matched : NameSet) (names : Array Name)
    (other : Option Environment := none) : IO (Array Name) := do
  let mut generated := #[]
  let mut unexpected := #[]
  for name in names do
    if other.any (·.contains name) then
      throw <| IO.userError s!"one-sided declaration has an opposite compiled counterpart: {name}"
    let isDerived ← (derivedConsumerExport matched name).toIO'
      {fileName := "<consumer>", fileMap := default} {env}
    if isDerived then generated := generated.push name else unexpected := unexpected.push name
  let equations ← replayUpstreamEquations env unexpected
  generated := generated ++ unexpected.filter equations.contains
  unexpected := unexpected.filter (!equations.contains ·)
  unless unexpected.isEmpty do
    let side := if other.isSome then "one-sided frozen declaration" else "additional official-side consumer export"
    throw <| IO.userError <| String.intercalate "\n"
      (unexpected.toList.map fun name => s!"{side} {name}")
  return generated

private def sharedConsumerNames (env other : Environment) (modules : Array Name) : NameSet := Id.run do
  let mut shared : NameSet := {}
  for owner in env.header.modules, data in env.header.moduleData do
    if modules.contains owner.module then
      for name in data.constNames do
        if (other.getModuleIdxFor? name).any (fun i => other.header.moduleNames[i]! == owner.module) then
          shared := shared.insert name
  return shared

/-- Check both export sets and their mathematical content after isolated downstream builds.
The frozen inventory requires correspondence for every included shared declaration and
compiler provenance for every one-sided declaration. -/
def checkConsumers (strict publicStrict reference : Environment) (modules : Array Name)
    (strictSearchPath : System.SearchPath) (inventory : Array FrozenInventory := #[]) : IO (Array (String × String)) := do
  let rename := fun (name : Name) => Id.run do
    let some idx := strict.getModuleIdxFor? name | return name
    let owner := strict.header.modules[idx]!.module
    if owner.getRoot == `OmegaInit || owner.getRoot == `OmegaMathlib then return official name
    return name
  let officialOnly ← frozenRoots reference modules inventory (·.officialOnly)
  let strictOnly ← frozenRoots strict modules inventory (·.strictOnly)
  unless strictOnly.isEmpty do
    let officialSearchPath ← searchPathRef.get
    searchPathRef.set strictSearchPath
    try
      discard <| checkDerived strict (sharedConsumerNames strict reference modules) strictOnly (some reference)
    finally searchPathRef.set officialSearchPath
  let mut pending := (consumerExports strict modules).filter fun name => !strictOnly.contains name
  let expected := NameSet.ofList (pending.toList.map rename)
  pending := pending ++ (← frozenRoots strict modules inventory (·.paired))
  -- Equal references to a private helper do not establish that its implementations agree.
  let mut seen : NameSet := {}
  let mut basis := #[]
  for target in ← checkConsumerAliases strict reference rename modules do
    let owner ← ownerOf strict target
    match owner.getRoot with
    | `OmegaInit => basis := basis.push (target, owner.replacePrefix `OmegaInit `Init)
    | `OmegaMathlib => basis := basis.push (target, owner.replacePrefix `OmegaMathlib `Mathlib)
    | _ =>
      if modules.contains owner then pending := pending.push target
      else if owner.getRoot == `OmegaMath || owner.getRoot == `D5 then
        throw <| IO.userError s!"project alias target missing from isolated consumer check: {owner}"
  while let some name := pending.back? do
    pending := pending.pop
    unless seen.contains name do
      seen := seen.insert name
      let owner ← ownerOf strict name
      let dst := rename name
      unless (← ownerOf reference dst) == owner do
        throw <| IO.userError s!"consumer declaration has different owner: {name}"
      let deps ← compare reference rename (← lookup strict name) (← lookup reference dst)
      for dep in deps do
        let depOwner ← ownerOf strict dep
        match depOwner.getRoot with
        | `OmegaInit => basis := basis.push (dep, depOwner.replacePrefix `OmegaInit `Init)
        | `OmegaMathlib => basis := basis.push (dep, depOwner.replacePrefix `OmegaMathlib `Mathlib)
        | _ =>
          if modules.contains depOwner then pending := pending.push dep
          else if depOwner.getRoot == `OmegaMath || depOwner.getRoot == `D5 then
            throw <| IO.userError s!"project dependency missing from isolated consumer check: {depOwner}"
  check strict publicStrict reference basis
  let mut generated ← checkDerived reference expected <|
    (consumerExports reference modules).filter fun name => !expected.contains name && !officialOnly.contains name
  unless officialOnly.isEmpty do
    generated := generated ++ (← checkDerived reference (sharedConsumerNames reference strict modules)
      officialOnly (some strict))
  unless generated.isEmpty do
    IO.println s!"Additional declarations generated by the official compiler ({generated.size}): {generated.qsort Name.quickLt}"

  IO.println s!"Compared {expected.size} public consumer declarations and {seen.size} declarations in their closure."
  return ← officialOnly.mapM fun name => do
    return ((← ownerOf reference name).toString, frozenNameKey name)

end OmegaChecks.Interface
