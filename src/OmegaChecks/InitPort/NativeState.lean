module
import all Lean.Environment
public import Lean
import Lean.Compiler.LCNF.EmitC
import all Lean.Compiler.LCNF.MonoTypes
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF

namespace OmegaChecks.InitPort.NativeState

public def layouts : Array Name :=
  #[trivialStructureInfoExt.name, impureTrivialStructureInfoExt.name, impureTypeExt.name,
    monoTypeExt.name, ctorLayoutExt.name]

public def codeExtensions : Array Name :=
  #[externAttr.ext.name, baseExt.name, monoExt.name, impureSigExt.name, IR.declMapExt.name]

/-- Lean stores entries in its native code and layout extensions sorted by declaration name. -/
private unsafe def entryName (ext : Name) (entry : EnvExtensionEntry) : Name :=
  if ext == IR.declMapExt.name then (unsafeCast entry : IR.Decl).name
  else if ext == baseExt.name || ext == monoExt.name then (unsafeCast entry : Decl .pure).name
  else if ext == impureSigExt.name then (unsafeCast entry : Signature .impure).name
  else (unsafeCast entry : Name × Unit).1

private unsafe def merge (old fresh : ModuleData) (selected : Array Name) : IO ModuleData := do
  let mut entries := old.entries
  for (ext, values) in fresh.entries do
    unless selected.contains ext do continue
    let mut replacements : NameMap EnvExtensionEntry := {}
    if let some (_, existing) := entries.find? (·.1 == ext) then
      for v in existing do replacements := replacements.insert (entryName ext v) v
    for v in values do replacements := replacements.insert (entryName ext v) v
    entries := (entries.filter (·.1 != ext)).push (ext, (replacements.toArray.qsort (fun a b => a.1.quickLt b.1)).map Prod.snd)
  let extras := (old.extraConstNames ++ fresh.extraConstNames).foldl (init := #[]) fun ns n =>
    if ns.contains n then ns else ns.push n
  return {old with entries, extraConstNames := extras}

/-- Recompile existing kernel objects as local definitions in their actual owner. Only the
compiler metadata is written back. The original constants and import edges stay in their files. -/
public def localEnv (env : Environment) (mod : Name) (names : Array Name) : IO Environment := do
  let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"missing native owner {mod}"
  let mut kenv := env.toKernelEnv
  for n in names do
    unless env.getModuleIdxFor? n == some idx do throw <| IO.userError s!"wrong native owner of {n}"
    kenv := {kenv with const2ModIdx := kenv.const2ModIdx.erase n}
  return (Environment.ofKernelEnv kenv).setMainModule mod |>.setModulePackage (env.getModulePackageByIdx? idx)

public unsafe def writeCode (lib : System.FilePath) (mod : Name) (compiled : Environment)
    (selected : Array Name) : IO Unit := do
  let path := modToFilePath lib mod "olean"
  let paths := #[path, path.addExtension "server", path.addExtension "private"]
  let levels := #[OLeanLevel.exported, .server, .private]
  let old ← readModuleDataParts paths
  let mut parts := #[]
  for (previous, _) in old, file in paths, level in levels do
    parts := parts.push (file, ← merge previous (← mkModuleData compiled level) selected)
  saveModuleDataParts mod parts
  let ir := path.withExtension "ir"
  let sig := ir.addExtension "sig"
  let old ← readModuleDataParts #[sig, ir]
  let news := #[← mkModuleData compiled .exported, Lean.mkIRData compiled]
  let mut irParts := #[]
  for (previous, _) in old, file in #[sig, ir], fresh in news do
    irParts := irParts.push (file, ← merge previous fresh selected)
  saveModuleDataParts (mod ++ `ir) irParts

public def compile (env : Environment) (work : CoreM Unit) : IO Environment := do
  let ctx : Core.Context := { fileName := "<strict runtime ABI>", fileMap := default, options := Elab.async.set {} false }
  let (_, s) ← work.toIO ctx {env}
  return s.env

public def compileLayouts (env : Environment) (name : Name) : IO Environment := do
  let some (.inductInfo ind) := env.find? name | throw <| IO.userError s!"missing inductive {name}"
  let idx := (env.getModuleIdxFor? name).get!
  let contextEnv ← localEnv env env.header.moduleNames[idx]! (#[name] ++ ind.ctors.toArray)
  compile contextEnv do (← compileDeclsRef.get) #[name] {}

public def verify (env : Environment) (n : Name) (args : Array (IR.IRType × Bool))
    (ret : IR.IRType) (symbol : String) : IO Unit := do
  let some (.extern _ params result symbolData) := IR.findEnvDecl env n
    | throw <| IO.userError s!"missing compiled extern {n}"
  unless params.map (fun p => (p.ty, p.borrow)) == args && result == ret &&
    symbolData == ⟨[.standard `all symbol]⟩ do throw <| IO.userError s!"native ABI mismatch for {n}"

/-- Both pure and effectful task scheduling convert strict unary priorities to the runtime ABI. -/
public def checkPriorityLayout (env : Environment) : IO Unit := do
  for (n, tag, fields) in #[(`Omega.Nat.zero, 0, 0), (`Omega.Nat.succ, 1, 1)] do
    let some d := ctorLayoutExt.find? env n | throw <| IO.userError s!"missing native priority layout {n}"
    unless d.ctorInfo.cidx == tag && d.ctorInfo.size == fields && d.ctorInfo.usize == 0 &&
        d.ctorInfo.ssize == 0 && d.fieldInfo.size == fields do throw <| IO.userError s!"incorrect priority layout {n}"
  let some succ := ctorLayoutExt.find? env `Omega.Nat.succ | throw <| IO.userError "missing successor"
  let #[.object 0 _] := succ.fieldInfo | throw <| IO.userError "incorrect priority predecessor"

/-- The native state adapters construct ST.Out with the result followed by the strict world. -/
public unsafe def installStateLayout (lib : System.FilePath) (env : Environment) : IO Unit := do
  let state ← compileLayouts env `Omega.ST.Out
  let some pair := ctorLayoutExt.find? state `Omega.ST.Out.mk | throw <| IO.userError "missing ST.Out layout"
  let #[.object 0 _, .object 1 _] := pair.fieldInfo | throw <| IO.userError "ST.Out must retain value and world"
  unless pair.ctorInfo.cidx == 0 && pair.ctorInfo.size == 2 && pair.ctorInfo.usize == 0 && pair.ctorInfo.ssize == 0 do
    throw <| IO.userError "ST.Out result disagrees with the native state adapter"
  writeCode lib `OmegaInit.System.ST state layouts

/-- The emitted module contains the compiled entry points and has no imported initializers. -/
public def emitBridge (compiled : Environment) (owner : Name) (runtime : Option System.FilePath)
    (output : System.FilePath) : IO Unit := do
  let env := Environment.ofKernelEnv {compiled.toKernelEnv with header.imports := #[], header.isModule := true}
  -- C emission consults the attribute state for calls made inside boxed wrappers.
  let env := (externAttr.ext.setState env (externAttr.ext.getState compiled)).setModulePackage compiled.getModulePackage?
  let c ← (emitC owner).toIO' {fileName := "<strict runtime entry points>", fileMap := default} {env}
  let source ← match runtime with
    | some file => pure <| c ++ "\n" ++ (← IO.FS.readFile file)
    | none => pure c
  IO.FS.writeFile output source

end OmegaChecks.InitPort.NativeState
