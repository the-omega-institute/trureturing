module
import all Lean.Environment
import Lean.Compiler.LCNF.Main
import Lean.Compiler.LCNF.PhaseExt
import Lean.Compiler.LCNF.EmitC
import Lean.Compiler.ImplementedByAttr
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.NativeState

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

private def compileOwner (groups : Array InductiveVal) (order : Array Name) : CoreM Unit := do
  for group in groups do
    (← compileDeclsRef.get) group.all.toArray {}
  for n in order do
    let before ← Core.saveState
    try
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
    (onlyLayouts : Bool) : IO Unit := do
  let env ← importModules #[{module := owner, importAll := true}] {}
  let some idx := env.getModuleIdx? owner | throw <| IO.userError s!"unknown owner {owner}"
  let path := modToFilePath lib owner "olean"
  let raw ← readModuleDataParts #[path, path.addExtension "server", path.addExtension "private"]
  let parts := raw.map (·.1)
  let part := parts[2]!
  let oldNative := NameSet.ofList ((impureSigExt.getModuleEntries env idx).map (·.name)).toList
  if !onlyLayouts && !oldNative.isEmpty then
    throw <| IO.userError s!"{owner} already has native symbols and its own initializer"
  let mut groups := #[]
  let mut locals := #[]
  let mut candidates := #[]
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
      if onlyLayouts || ci.isUnsafe || ci.isPartial then continue
      let upstream := d.name.replacePrefix `Omega .anonymous
      if isExtern source upstream || (getImplementedBy? source upstream).isSome then continue
      candidates := candidates.push d.name
    | _ => continue
  if onlyLayouts && groups.isEmpty then return
  let localNames := NameSet.ofList candidates.toList
  let order : Array Name := Id.run <|
    (candidates.foldlM (fun acc n => return acc ++ (← dependencies env localNames n)) #[]).run' {}
  let context ← localEnv env owner (locals ++ candidates)
  let ctx : Core.Context := {fileName := "<generated native Init>", fileMap := default, options := Elab.async.set {} false}
  let (_, st) ← (compileOwner groups order).toIO ctx {env := context}
  for group in groups do
    for name in group.all do
      unless (monoTypeExt.find? st.env name).isSome do
        throw <| IO.userError s!"compiler produced no layout for {name}"
  if onlyLayouts then
    writeCode lib owner st.env layouts
  else
    for n in (declOrderExt.getState st.env).1 do
      if oldNative.contains n then throw <| IO.userError s!"native symbol collision at {n}"
    emitOwner st.env owner part.imports ctx (modToFilePath out owner "c")
    writeCode lib owner st.env (layouts ++ codeExtensions)
    let fresh ← importModules #[{module := owner}] {} (level := .exported)
    let actual := NameSet.ofList ((impureSigExt.getModuleEntries fresh (fresh.getModuleIdx? owner).get!).map (·.name)).toList
    let originalOwner := owner.replacePrefix `OmegaInit `Init
    let some originalIdx := publicSource.getModuleIdx? originalOwner | throw <| IO.userError s!"no official owner {originalOwner}"
    let published := NameSet.ofList ((impureSigExt.getModuleEntries publicSource originalIdx).map (·.name)).toList
    let publicSigs := publicSource.header.moduleData[originalIdx]!.constants.filter fun ci =>
      !ci.name.isInternalOrNum && !isPrivateName ci.name && published.contains ci.name &&
      (source.find? ci.name).any fun full => full.hasValue (allowOpaque := true) && !full.isUnsafe && !full.isPartial
    let covered := publicSigs.filter fun ci => actual.contains (`Omega ++ ci.name)
    IO.println s!"{owner}: {covered.size}/{publicSigs.size} public executable signatures"
    let missing := publicSigs.filterMap fun ci =>
      if actual.contains (`Omega ++ ci.name) then none else some ci.name
    if !missing.isEmpty then IO.println s!"{owner}: missing public executable signatures: {missing}"


end GeneratedNative

public unsafe def main (args : List String) : IO Unit := do
  let lib :: out :: requests := args | throw <| IO.userError "expected library, C output and ordered owners"
  let modules := requests.toArray.map fun s => (s.dropPrefix "layouts=").toString.toName
  let official := modules.map fun n => {module := n.replacePrefix `OmegaInit `Init : Import}
  let published ← importModules official {} (level := .exported)
  let src ← importModules official {}
  searchPathRef.set [lib]
  for name in modules, s in requests do
    GeneratedNative.install src published lib out name (s.startsWith "layouts=")
