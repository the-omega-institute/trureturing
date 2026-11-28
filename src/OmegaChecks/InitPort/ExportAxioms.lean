module
meta import OmegaChecks.InitCompiler.RootNames
import Lean
import Lean.Replay
import all OmegaChecks.InitCompiler.NaturalBootstrap
import all OmegaChecks.InitCompiler.CompilerMarkers
import all OmegaChecks.InitPort.NativeQuot
import OmegaChecks.InitPort.UnsafeRuntime
meta import OmegaChecks.InitPort.UnsafeRuntime
import all Lean.Util.CollectAxioms

open Lean

/-- Recompute the pinned compiler's axiom entries on the unsealed, replayed terms.
Its writer sorts entries using the same name order as its import-time binary search. -/
private def compilerAxiomEntries (full : Environment) :
    IO (Name × NameMap EnvExtensionEntry) := do
  OmegaChecks.InitPort.NativeQuot.checkSupport full
  for (n, ci) in full.constants.toList do
    if (ci.isUnsafe && !OmegaChecks.InitPort.UnsafeRuntime.isOriginal ci true) || ci.isPartial || ci.isAxiom then
      throw <| IO.userError s!"inadmissible strict declaration {n}"
  let checked ← OmegaChecks.InitPort.UnsafeRuntime.replay full.constants.map₁
  let env := Environment.ofKernelEnv checked
  let data ← mkModuleData env
  let some (ext, entries) := data.entries.find? (fun e => privateToUserName e.1 == `Lean.exportedAxiomsExt)
    | throw <| IO.userError "compiler failed to export axiom information"
  let names := data.constNames.qsort Name.quickLt
  unless names.size == entries.size && names.size == full.constants.map₁.size do
    throw <| IO.userError "incomplete compiler axiom information after replay"
  let mut byName := {}
  for name in names, entry in entries do byName := byName.insert name entry
  return (ext, byName)

/-- The combined environment selects one term for repeated names. Check each physical
copy against the selected interface, including a different proof of the same theorem. -/
private def checkCopies (dir : System.FilePath) (full : Environment) : IO Unit := do
  let mut seen : NameSet := {}
  let mut repeated : NameSet := {}
  for data in full.header.moduleData do
    for n in data.constNames do
      if seen.contains n then repeated := repeated.insert n
      seen := seen.insert n
  for owner in full.header.moduleNames, data in full.header.moduleData do
    unless data.constNames.any repeated.contains do continue
    let path := modToFilePath dir owner "olean"
    let parts ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
    let localTerms := (parts.map (·.1))[2]!.constants
    let mut differentProof := false
    for copy in localTerms do
      unless repeated.contains copy.name do continue
      let some selected := full.find? copy.name | throw <| IO.userError s!"missing active copy of {copy.name}"
      let error := IO.userError s!"incompatible duplicate definition {owner}/{copy.name}"
      unless copy.levelParams == selected.levelParams && copy.type.equal selected.type do throw error
      if let .thmInfo thm := copy then
        let .thmInfo active := selected | throw error
        unless thm.value.equal active.value do differentProof := true
      else
        unless copy == selected do throw error
        unless (copy.value? (allowOpaque := true)).map ExprStructEq.mk ==
          (selected.value? (allowOpaque := true)).map ExprStructEq.mk do throw error
        if let .recInfo a := copy then
          let .recInfo b := selected | throw error
          unless (a.rules.zip b.rules).all (fun (x, y) => x.rhs.equal y.rhs) do throw error
    if differentProof then
      -- Check the actual proof using only terms available to this module, with all
      -- its own copies selected. Replay rejects cyclic/self-supporting alternatives.
      let env ← importModules #[{module := owner}] {} (level := .private)
      let terms := localTerms.foldl (fun states c => states.insert c.name c) env.constants.map₁
      discard <| OmegaChecks.InitPort.UnsafeRuntime.replay terms

private def writeModule (lib : System.FilePath) (name ext : Name)
    (byName : NameMap EnvExtensionEntry) : IO Unit := do
  let path := modToFilePath lib name "olean"
  let paths := #[path, path.addExtension "server", path.addExtension "private"]
  let old ← readModuleDataParts paths
  let exported := (old.map (·.1))[0]!.constNames.qsort Name.quickLt
  let axioms ← exported.mapM fun n => do
    let some entry := byName.find? n | throw <| IO.userError s!"missing compiler axiom entry for {n}"
    return entry
  let mut parts := #[]
  for (data, _) in old, file in paths do
    let rest := data.entries.filter (·.1 != ext)
    let entries := if axioms.isEmpty then rest else rest.push (ext, axioms)
    parts := parts.push (file, {data with entries})
  saveModuleDataParts name parts

/-- Both count functions expose their defining equations to ordinary imports.
Check reflexivity at free inputs, as required by callers that use the kernel reduction. -/
private def checkCountEquations (env : Environment) : IO Unit := do
  for name in [`Omega.List.countP.eq_1, `Omega.Array.countP.eq_1] do
    let some ci := env.find? name | continue
    let rec refl : Expr → Option Expr
      | .forallE n d b bi => return .lam n d (← refl b) bi
      | prop => do
        let .const `Eq levels := prop.getAppFn | none
        let #[α, left, _] := prop.getAppArgs | none
        return mkApp2 (mkConst `Eq.refl levels) α left
    let some proof := refl ci.type | throw <| IO.userError s!"unexpected equation type for {name}"
    let .ok inferred := Kernel.check env {} proof | throw <| IO.userError s!"invalid reflexivity term for {name}"
    unless Kernel.isDefEqGuarded env {} inferred ci.type do
      throw <| IO.userError s!"ordinary imports lost definitional reduction for {name}"

/-- Smart unfolding stops at the selected alternative, including a recursive call on an unknown name. -/
private def checkSmartUnfolding (env : Environment) : IO Unit := do
  let name := `Omega.Lean.Name.hasMacroScopes
  unless env.contains (Meta.mkSmartUnfoldingNameFor name) do return
  let check : MetaM Unit := do
    let call := mkApp (mkConst name)
    let empty := call (mkConst `Omega.Lean.Name.anonymous)
    let negative := mkConst `Bool.false
    unless (← Meta.unfoldDefinition? empty true) == some negative && Kernel.isDefEqGuarded env {} empty negative do
      throwError "unexpected smart unfolding of the anonymous name"
    Meta.withLocalDeclD `p (mkConst `Omega.Lean.Name) fun p => do
      let num := call (mkApp2 (mkConst `Omega.Lean.Name.num) p (mkRawNatLit 0))
      let recursive := call p
      let left ← Meta.mkLambdaFVars #[p] num
      let right ← Meta.mkLambdaFVars #[p] recursive
      unless (← Meta.unfoldDefinition? num true) == some recursive && Kernel.isDefEqGuarded env {} left right do
        throwError "smart unfolding lost the recursive name projection"
      unless (← Meta.unfoldDefinition? recursive true).isNone do
        throwError "smart unfolding selected an alternative on a free name"
  check.run' |>.toIO' {fileName := "<ordinary import>", fileMap := default} {env}

/-- Ordinary imports consult the public axiom extension when bodies are sealed.
Read the persisted exported module level and ask the same API as `#print axioms`. -/
private def checkPublic (imports : Array Import) : IO Unit := do
  unsafe enableInitializersExecution
  let env ← importModules imports {} (loadExts := true) (level := .exported)
  OmegaChecks.InitPort.NativeQuot.checkSupport env .exported
  checkCountEquations env
  checkSmartUnfolding env
  let check : CoreM Nat := do
    for mod in env.header.modules, data in env.header.moduleData, i in [:env.header.modules.size] do
      let entries := exportedAxiomsExt.getModuleEntries env i
      for n in data.constNames do
        let some (_, axioms) := entries.binSearch (n, #[]) (fun a b => Name.quickLt a.1 b.1)
          | throwError "missing public axiom entry for {mod.module}/{n}"
        unless axioms.isEmpty do throwError "nonempty public axiom entry for {mod.module}/{n}: {axioms}"
    let mut count := 0
    for (n, _) in env.constants.toList do
      let axs ← collectAxioms n
      unless axs.isEmpty do throwError "ordinary import attributes axioms {axs} to {n}"
      count := count + 1
    return count
  let count ← check.toIO' {fileName := "<ordinary import>", fileMap := default} {env}
  IO.println s!"Verified zero axiom dependencies for {count} declarations under ordinary imports."

public def main (args : List String) : IO Unit := do
  let checkOnly := args.head? == some "--check"
  let dir :: names := (if checkOnly then args.drop 1 else args) | throw <| IO.userError "expected compiled library and module roots"
  if names.isEmpty then throw <| IO.userError "expected at least one module"
  let imports := names.toArray.map fun n => {module := n.toName : Import}
  searchPathRef.set [dir]
  let full ← importModules imports {} (level := .private)
  let (ext, byName) ← compilerAxiomEntries full
  checkCopies dir full
  unless checkOnly do
    for i in imports do writeModule dir i.module ext byName
  checkPublic imports
