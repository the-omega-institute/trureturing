module
import all Lean.Environment
import Lean
import Lean.Compiler.LCNF.EmitC
import all Lean.Compiler.LCNF.MonoTypes
import all Lean.Compiler.LCNF.ToImpureType

open Lean Compiler.LCNF

namespace PromiseNative

private def owner := `OmegaInit.System.Promise
private def allocation := `Omega.IO.Promise.new
private def resolution := `Omega.IO.Promise.resolve
private def allocationSymbol := "omega_io_promise_new"
private def resolutionSymbol := "omega_io_promise_resolve"
private def resolved := `Omega.IO.Promise.isResolved
private def resolvedSymbol := "omega_io_promise_is_resolved"

private def layouts : Array Name :=
  #[trivialStructureInfoExt.name, impureTrivialStructureInfoExt.name, impureTypeExt.name,
    monoTypeExt.name, ctorLayoutExt.name]

private def codeExtensions : Array Name :=
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
private def localEnv (env : Environment) (mod : Name) (names : Array Name) : IO Environment := do
  let some idx := env.getModuleIdx? mod | throw <| IO.userError s!"missing native owner {mod}"
  let mut kenv := env.toKernelEnv
  for n in names do
    unless env.getModuleIdxFor? n == some idx do throw <| IO.userError s!"wrong native owner of {n}"
    kenv := {kenv with const2ModIdx := kenv.const2ModIdx.erase n}
  return (Environment.ofKernelEnv kenv).setMainModule mod

private unsafe def writeCode (lib : System.FilePath) (mod : Name) (compiled : Environment)
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

private def compile (env : Environment) (work : CoreM Unit) : IO Environment := do
  let ctx : Core.Context := { fileName := "<strict promise ABI>", fileMap := default, options := Elab.async.set {} false }
  let (_, s) ← work.toIO ctx {env}
  return s.env

private def compileLayouts (env : Environment) (name : Name) : IO Environment := do
  let some (.inductInfo ind) := env.find? name | throw <| IO.userError s!"missing inductive {name}"
  let idx := (env.getModuleIdxFor? name).get!
  let contextEnv ← localEnv env env.header.moduleNames[idx]! (#[name] ++ ind.ctors.toArray)
  compile contextEnv do (← compileDeclsRef.get) #[name] {}

private def verify (env : Environment) (n : Name) (args : Array (IR.IRType × Bool))
    (ret : IR.IRType) (symbol : String) : IO Unit := do
  let some (.extern _ params result symbolData) := IR.findEnvDecl env n
    | throw <| IO.userError s!"missing compiled extern {n}"
  unless params.map (fun p => (p.ty, p.borrow)) == args && result == ret &&
    symbolData == ⟨[.standard `all symbol]⟩ do throw <| IO.userError s!"native ABI mismatch for {n}"

public unsafe def install (lib output : System.FilePath) : IO Unit := do
  let original ← importModules #[{module := `Init.System.Promise}] {}
  verify original `IO.Promise.new #[(.erased, false), (.erased, false), (.void, false)] .tobject "lean_io_promise_new"
  verify original `IO.Promise.resolve #[(.erased, false), (.tobject, false), (.tobject, true), (.void, false)]
    .tagged "lean_io_promise_resolve"
  let some (.fdecl _ params .uint8 _ _) := IR.findEnvDecl original `IO.Promise.isResolved
    | throw <| IO.userError "missing native Promise.isResolved"
  unless params.map (fun p => (p.ty, p.borrow)) == #[(.erased, false), (.tobject, true), (.void, false)] do
    throw <| IO.userError "unexpected pinned Promise.isResolved signature"
  let some (.fdecl _ borrowed .uint8 _ _) := IR.findEnvDecl original `IO.Promise.isResolved._redArg
    | throw <| IO.userError "missing reduced Promise.isResolved"
  unless borrowed.map (fun p => (p.ty, p.borrow)) == #[(.tobject, true), (.void, false)] do
    throw <| IO.userError "unexpected borrowing in the runtime poll entry"
  searchPathRef.set [lib]
  let imports := #[{module := owner : Import}]
  let env ← importModules imports {}
  unless [allocation, resolution, resolved].any env.contains do return
  let state ← compileLayouts env `Omega.ST.Out
  let some pair := ctorLayoutExt.find? state `Omega.ST.Out.mk | throw <| IO.userError "missing ST.Out layout"
  let #[.object 0 _, .object 1 _] := pair.fieldInfo | throw <| IO.userError "ST.Out must retain value and world"
  unless pair.ctorInfo.cidx == 0 && pair.ctorInfo.size == 2 && pair.ctorInfo.usize == 0 && pair.ctorInfo.ssize == 0 do
    throw <| IO.userError "ST.Out result disagrees with the native state adapter"
  writeCode lib `OmegaInit.System.ST state layouts
  let env ← importModules imports {}
  let some (.inductInfo prom) := env.find? `Omega.IO.Promise | throw <| IO.userError "missing promise type"
  let mut names := #[prom.name] ++ prom.ctors.toArray
  for n in #[allocation, resolution, resolved] do
    if env.contains n then names := names.push n
  let contextEnv ← localEnv env owner names
  let compiled ← compile contextEnv do
    (← compileDeclsRef.get) #[prom.name] {}
    for (n, symbol) in #[ (allocation, allocationSymbol), (resolution, resolutionSymbol), (resolved, resolvedSymbol)] do
      unless (← getEnv).contains n do continue
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := n) e (n, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[n] {}
  let some (some handle) := impureTrivialStructureInfoExt.find? compiled prom.name
    | throw <| IO.userError "native promise handle must be an unboxed field"
  unless handle.numParams == 1 && handle.fieldIdx == 0 && prom.ctors == [handle.ctorName] do
    throw <| IO.userError "unexpected native promise representation"
  if compiled.contains allocation then
    verify compiled allocation #[(.erased, false), (.erased, false), (.tobject, false)] .object allocationSymbol
  if compiled.contains resolution then
    verify compiled resolution #[(.erased, false), (.tobject, false), (.tobject, true), (.tobject, false)]
      .object resolutionSymbol
  if compiled.contains resolved then
    verify compiled resolved #[(.erased, false), (.tobject, false), (.tobject, false)] .object resolvedSymbol
  writeCode lib owner compiled (layouts ++ codeExtensions)
  -- The bridge contains only extern calls and boxed entry points. Its object has no imported initializers.
  let codeEnv := Environment.ofKernelEnv {compiled.toKernelEnv with header.imports := #[], header.isModule := true}
  let c ← (emitC owner).toIO' {fileName := "<promise entry points>", fileMap := default} {env := codeEnv}
  let runtime ← IO.FS.readFile (System.FilePath.mk "src/OmegaChecks/InitPort/promise_runtime.c")
  IO.FS.writeFile output (c ++ "\n" ++ runtime)

end PromiseNative

public unsafe def main (args : List String) : IO Unit := do
  let [lib, output] := args | throw <| IO.userError "expected strict library and native C output"
  PromiseNative.install lib output
