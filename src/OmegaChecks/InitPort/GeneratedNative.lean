module
import all Lean.Environment
import all Lean.OriginalConstKind
import Lean.Compiler.LCNF.ToDecl
import Lean.Compiler.LCNF.Main
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.EmitC
import Lean.Compiler.ImplementedByAttr
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.Translation
import OmegaChecks.InitPort.Translation

/-! Compile an existing strict owner directly from its checked kernel definitions. -/

open Lean Compiler LCNF OmegaChecks.InitPort.NativeState

namespace GeneratedNative

private partial def dependencies (env : Environment) (localNames : NameSet) (n : Name) :
    StateM NameSet (Array Name) := do
  if !(localNames.contains n) || (← get).contains n then return #[]
  modify (·.insert n)
  let some ci := env.find? n | return #[]
  let some body := ci.value? | return #[]
  let mut prior := #[]
  for dep in ci.type.getUsedConstants ++ body.getUsedConstants do
    prior := prior ++ (← dependencies env localNames dep)
  return prior.push n

/-- A constructor can contain another inductive from the same owner. Defer its layout
until the compiler has installed the referenced representation. -/
private partial def compileLayoutsInOrder (groups : Array InductiveVal) : CoreM Unit := do
  let mut deferred := #[]
  let mut reasons := #[]
  for group in groups do
    let before ← Core.saveState
    try
      (← compileDeclsRef.get) group.all.toArray {}
      for name in group.all do
        unless (monoTypeExt.find? (← getEnv) name).isSome do throwError "no compiled layout for {name}"
    catch ex =>
      before.restore
      deferred := deferred.push group
      reasons := reasons.push (group.name, ← ex.toMessageData.toString)
  if deferred.isEmpty then return
  if deferred.size < groups.size then compileLayoutsInOrder deferred
  else for (name, reason) in reasons do IO.println s!"missing layout {name}: {reason}"

/-- Recover the pinned name, including private declarations in their lexical owner. -/
private def originalName (n : Name) : Name := Id.run do
  if let some user := privateToUserName? n then
    if let some lexical := privatePrefix? n then
      if (`_private.OmegaInit).isPrefixOf lexical && isPrivatePrefix lexical then
        return lexical.replacePrefix `_private.OmegaInit `_private.Init ++ user.replacePrefix `Omega .anonymous
  return n.replacePrefix `Omega .anonymous

/-- Use the published strict calling conventions of runtime operands before boxing higher-order calls. -/
private def missingRuntimeDependency (source : Environment) (n : Name) : CoreM Bool := do
  let some body := (← getEnv).find? n >>= (·.value?) | return false
  let mut missing : NameSet := {}
  let env ← getEnv
  for dep in body.getUsedConstants do
    -- Constructor applications lower directly using the owning inductive's strict layout.
    if let some (.ctorInfo ctor) := env.find? dep then
      if (monoTypeExt.find? env ctor.induct).isSome then continue
    let original := originalName dep
    if (isExtern source original || (getImplementedBy? source original).isSome ||
        (getSigCore? source impureSigExt original).isSome) &&
        (← getImpureSignature? dep).isNone then
      missing := missing.insert dep
  if missing.isEmpty then return false
  -- The compiler has erased proof arguments and types in the executable let-values.
  let before ← Core.saveState
  try
    let decl ← CompilerM.run (toDecl n)
    let visit : StateM Bool Unit := decl.value.forCodeM fun (root : Code .pure) => root.forM fun (code : Code .pure) => do
      if let .let binding _ := code then
        if let .const dep .. := binding.value then
          if missing.contains dep then modify fun _ => true
    return (visit.run false).2
  catch _ =>
    return true
  finally
    before.restore

private def compileOwner (source : Environment) (groups : Array InductiveVal) (order : Array Name) : CoreM Unit := do
  compileLayoutsInOrder groups
  for n in order do
    if ← missingRuntimeDependency source n then continue
    let before ← Core.saveState
    try
      modifyEnv fun env => privateConstKindsExt.insert env n .defn
      (← compileDeclsRef.get) #[n] {}
      -- Type aliases and proof-only definitions have no executable declaration.
      unless (← CompilerM.run (getLocalDeclAt? n .impure)).isSome do before.restore
    catch _ =>
      before.restore

/-- Use ordinary module initialization so closed functions and imported modules are ready before calls. -/
private def emitOwner (env : Environment) (owner : Name) (imports : Array Import)
    (ctx : Core.Context) (out : System.FilePath) : IO Unit := do
  let kernel := env.toKernelEnv
  let cenv := Environment.ofKernelEnv {kernel with header.imports := imports, header.isModule := true}
  let cenv := (externAttr.ext.setState cenv (externAttr.ext.getState env)).setModulePackage env.getModulePackage?
  IO.FS.createDirAll out.parent.get!
  IO.FS.writeFile out (← (emitC owner).toIO' ctx {env := cenv})

private unsafe def install (source publicSource : Environment) (lib out : System.FilePath) (owner : Name)
    (onlyLayouts mixed : Bool) : IO Unit := do
  let env ← importModules #[{module := owner, importAll := true}] {}
  let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"unknown owner {owner}"
  let path := modToFilePath lib owner "olean"
  let raw ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
  let parts := raw.map (·.1)
  let part := parts[2]!
  let oldNative := NameSet.ofList ((impureSigExt.getModuleEntries env idx).map (·.name)).toList
  let onlyLayouts := onlyLayouts || (!mixed && !oldNative.isEmpty)
  let mut groups := #[]
  let mut locals := #[]
  let mut candidates := #[]
  -- These eager word cardinalities require 65,536 through 2^64 successor cells
  -- when a detached seed uses a separately defined unary Nat.
  let unaryNat := (env.find? `Omega.Nat).any (· matches .inductInfo _)
  let largeWordSizes := [`UInt16.size, `UInt32.size, `UInt64.size, `USize.size]
  for ci in part.constants do
    match ci with
    | .inductInfo i =>
      if i.all.head? != some i.name then continue
      let mut family := #[]
      let mut hasLayout := false
      let mut missing := false
      for name in i.all do
        let some (.inductInfo member) := env.find? name | throw <| IO.userError s!"missing inductive {name}"
        family := family ++ #[name] ++ member.ctors.toArray
        if (monoTypeExt.find? env name).isSome then hasLayout := true else missing := true
      if missing && hasLayout then throw <| IO.userError s!"partially compiled mutual inductive {i.name}"
      if missing then
        groups := groups.push i
        locals := locals ++ family
    | .defnInfo d =>
      if onlyLayouts || oldNative.contains d.name || ci.isUnsafe || ci.isPartial then continue
      let upstream := originalName d.name
      if unaryNat && largeWordSizes.contains upstream then continue
      if isExtern source upstream || (getImplementedBy? source upstream).isSome then continue
      candidates := candidates.push d.name
    | _ => continue
  if onlyLayouts && groups.isEmpty then return
  let localNames := NameSet.ofList candidates.toList
  let order : Array Name := Id.run <|
    (candidates.foldlM (fun acc n => return acc ++ (← dependencies env localNames n)) #[]).run' {}
  let mut context ← localEnv env owner (locals ++ candidates)
  -- Compiler tags stored under the imported module index need local entries while compiling.
  for n in locals ++ candidates do
    if isAuxRecursor env n then context := markAuxRecursor context n
    if isSparseCasesOn env n then context := markSparseCasesOn context n
    if isNoConfusion env n then context := markNoConfusion context n (getNoConfusionInfo env n)
    if let some proj := env.getProjectionFnInfo? n then
      context := addProjectionFnInfo context n proj.ctorName proj.numParams proj.i proj.fromClass
  let ctx : Core.Context := {fileName := "<generated native Init>", fileMap := default, options := Elab.async.set {} false}
  let (_, st) ← (compileOwner source groups order).toIO ctx {env := context}
  if onlyLayouts then
    writeCode lib owner st.env layouts
  else
    for n in (declOrderExt.getState st.env).1 do
      if oldNative.contains n then throw <| IO.userError s!"native symbol collision at {n}"
    emitOwner st.env owner part.imports ctx (modToFilePath out owner "c")
    writeCode lib owner st.env (layouts ++ codeExtensions ++ #[privateConstKindsExt.name])
    let fresh ← importModules #[{module := owner}] {} (level := .exported)
    let actual := NameSet.ofList ((impureSigExt.getModuleEntries fresh (fresh.getModuleIdx? owner).get!).map (·.name)).toList
    let originalOwner := owner.replacePrefix `OmegaInit `Init
    let some originalIdx := publicSource.getModuleIdx? originalOwner | throw <| IO.userError s!"no official owner {originalOwner}"
    let published := NameSet.ofList ((impureSigExt.getModuleEntries publicSource originalIdx).map (·.name)).toList
    let publicSigs := publicSource.header.moduleData[originalIdx]!.constants.filter fun ci =>
      !ci.name.isInternalOrNum && !isPrivateName ci.name && published.contains ci.name &&
      (source.find? ci.name).any fun full => full.hasValue (allowOpaque := true) && !full.isUnsafe && !full.isPartial
    let covered := publicSigs.filter fun ci => actual.contains (InitKernelPort.portName ci.name)
    IO.println s!"{owner}: {covered.size}/{publicSigs.size} public executable signatures"
    let missing := publicSigs.filterMap fun ci =>
      if actual.contains (InitKernelPort.portName ci.name) then none else some ci.name
    if !missing.isEmpty then IO.println s!"{owner}: missing public executable signatures: {missing}"

/-- A detached seed may supply only Lean's compiled modules. Execute the ordinary consumer
using the saved IR under the same Boolean representation used by its C entry points. -/
private unsafe def checkControl (lib dir : System.FilePath) : IO Unit := do
  searchPathRef.set [lib, dir]
  let env ← importModules #[{module := `GeneratedControlConsumer, importAll := true}] {} (level := .private)
  let some (.inductInfo b) := env.find? `Bool | throw <| IO.userError "missing Boolean type"
  unless b.numParams == 0 && b.ctors == [`Bool.false, `Bool.true] do
    throw <| IO.userError "unexpected Boolean representation"
  let ty := mkConst `Bool
  let arity := .forallE `x ty (.forallE `y ty ty .default) .default
  for (name, expected) in [(`exceptResult, or), (`optionResult, and), (`stateResult, and)] do
    unless (env.find? name).any (·.type == arity) do throw <| IO.userError s!"unexpected type for {name}"
    let fn ← IO.ofExcept <| env.evalConst (Bool → Bool → Bool) {} name
    for x in [false, true] do
      for y in [false, true] do
        unless fn x y == expected x y do throw <| IO.userError s!"incorrect {name} {x} {y}"

end GeneratedNative

public unsafe def main (args : List String) : IO Unit := do
  if let ["--check-control", lib, dir] := args then
    return ← GeneratedNative.checkControl lib dir
  let lib :: out :: requests := args | throw <| IO.userError "expected library, C output and ordered owners"
  let modules := requests.toArray.map fun s => ((s.dropPrefix "layouts=").dropPrefix "mixed=").toString.toName
  let official := modules.map fun n => {module := n.replacePrefix `OmegaInit `Init : Import}
  let published ← importModules official {} (level := .exported)
  let src ← importModules official {}
  searchPathRef.set [lib]
  for name in modules, s in requests do
    GeneratedNative.install src published lib out name (s.startsWith "layouts=") (s.startsWith "mixed=")
    (← IO.getStdout).flush
