module
import all Lean.Environment
public import Lean
import OmegaChecks.InitCompiler.Layout
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

private unsafe def merge (old fresh : ModuleData) (selected : Array Name) (computable : NameSet) : IO ModuleData := do
  let mut entries := old.entries.map fun (ext, values) =>
    if ext == noncomputableExt.name then
      (ext, values.filter fun entry => !computable.contains (unsafeCast entry : Name))
    else (ext, values)
  for (ext, values) in fresh.entries do
    unless selected.contains ext do continue
    let mut replacements : NameMap EnvExtensionEntry := {}
    if let some (_, existing) := entries.find? (·.1 == ext) then
      for v in existing do replacements := replacements.insert (entryName ext v) v
    for v in values do replacements := replacements.insert (entryName ext v) v
    entries := (entries.filter (·.1 != ext)).push (ext, (replacements.toArray.qsort (fun a b => a.1.quickLt b.1)).map Prod.snd)
  -- Lean resolves private functions in imported optimizer code through the IR name-to-module index.
  let kernelNames := NameSet.ofList old.constNames.toList
  let mut extras := NameSet.ofList (old.extraConstNames ++ fresh.extraConstNames).toList
  for (ext, values) in entries do
    if ext == baseExt.name || ext == monoExt.name || ext == impureSigExt.name || ext == IR.declMapExt.name then
      for entry in values do
        let name := entryName ext entry
        if !kernelNames.contains name then extras := extras.insert name
  return {old with entries, extraConstNames := extras.toArray.qsort Name.quickLt}

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
    (selected : Array Name) (computable : NameSet := {}) : IO Unit := do
  let path := modToFilePath lib mod "olean"
  let paths := #[path, path.addExtension "server", path.addExtension "private"]
  let levels := #[OLeanLevel.exported, .server, .private]
  let old ← readModuleDataParts paths
  let mut parts := #[]
  for (previous, _) in old, file in paths, level in levels do
    parts := parts.push (file, ← merge previous (← mkModuleData compiled level) selected computable)
  saveModuleDataParts mod parts
  let ir := path.withExtension "ir"
  let sig := ir.addExtension "sig"
  let old ← readModuleDataParts #[sig, ir]
  let news := #[← mkModuleData compiled .exported, Lean.mkIRData compiled]
  let mut irParts := #[]
  for (previous, _) in old, file in #[sig, ir], fresh in news do
    irParts := irParts.push (file, ← merge previous fresh selected computable)
  saveModuleDataParts (mod ++ `ir) irParts

public def compile (env : Environment) (work : CoreM Unit) : IO Environment := do
  let ctx : Core.Context := { fileName := "<strict runtime ABI>", fileMap := default, options := Elab.async.set {} false }
  let (_, s) ← work.toIO ctx {env}
  return s.env

public def compileLayouts (env : Environment) (name : Name) : IO Environment := do
  let some (.inductInfo ind) := env.find? name | throw <| IO.userError s!"missing inductive {name}"
  let idx := (env.getModuleIdxFor? name).get!
  let contextEnv ← localEnv env env.header.moduleNames[idx]! (#[name] ++ ind.ctors.toArray)
  compile contextEnv do
    if name == `Omega.String then OmegaChecks.InitCompiler.prepareStringLayout
    (← compileDeclsRef.get) #[name] {}
    if name == `Omega.String then OmegaChecks.InitCompiler.finishStringLayout

public def verify (env : Environment) (n : Name) (args : Array (IR.IRType × Bool))
    (ret : IR.IRType) (symbol : String) : IO Unit := do
  let some (.extern _ params result symbolData) := IR.findEnvDecl env n
    | throw <| IO.userError s!"missing compiled extern {n}"
  unless params.map (fun p => (p.ty, p.borrow)) == args && result == ret &&
    symbolData == ⟨[.standard `all symbol]⟩ do throw <| IO.userError s!"native ABI mismatch for {n}"

/-- The task and sharing adapters pass runtime Nat values without conversion. -/
public def checkNativeNat (env : Environment) : IO Unit := do
  let some (.inductInfo nat) := env.find? `Nat | throw <| IO.userError "missing native Nat"
  unless nat.ctors == [`Nat.zero, `Nat.succ] && env.getModuleIdxFor? `Nat == env.getModuleIdx? `OmegaInit.Prelude do
    throw <| IO.userError "expected the kernel Nat from the strict Prelude"

/-- The compiler erases these single-field records to their first field. -/
public def checkErasedField (env : Environment) (record : Name) : IO Unit := do
  let some (some field) := impureTrivialStructureInfoExt.find? env record
    | throw <| IO.userError s!"missing erased representation of {record}"
  unless field.fieldIdx == 0 do throw <| IO.userError s!"unexpected erased field of {record}"

/-- The strict ByteArray carries a list of bounded natural bytes at the native boundary. -/
public def checkStrictBytes (env : Environment) : IO Unit := do
  checkNativeNat env
  for n in [`Omega.Fin, `Omega.BitVec, `Omega.UInt8, `Omega.Array] do
    checkErasedField env n
  let some l := ctorLayoutExt.find? env `Omega.ByteArray.mk | throw <| IO.userError "missing byte array storage"
  unless ((impureTrivialStructureInfoExt.find? env `Omega.ByteArray) matches some none) &&
      l.ctorInfo.cidx == 0 && l.ctorInfo.size == 1 && l.ctorInfo.usize == 2 && l.ctorInfo.ssize == 1 &&
      (l.fieldInfo matches #[.object 0 _]) do throw <| IO.userError "expected the boxed ByteArray seed"
  let some nil := ctorLayoutExt.find? env `Omega.List.nil | throw <| IO.userError "missing byte list nil"
  unless nil.ctorInfo.cidx == 0 && nil.ctorInfo.size == 0 && nil.ctorInfo.usize == 0 &&
      nil.ctorInfo.ssize == 0 && nil.fieldInfo.isEmpty do throw <| IO.userError "incorrect byte list nil"
  let some cons := ctorLayoutExt.find? env `Omega.List.cons | throw <| IO.userError "missing byte list cons"
  let #[.object 0 _, .object 1 _] := cons.fieldInfo | throw <| IO.userError "incorrect byte list fields"
  unless cons.ctorInfo.cidx == 1 && cons.ctorInfo.size == 2 && cons.ctorInfo.usize == 0 &&
      cons.ctorInfo.ssize == 0 do throw <| IO.userError "incorrect byte list tag or size"

/-- Matching host layouts for the interpreter tests that call strict code by name. -/
public structure BytesRepr where
  data : List Nat
  size : USize
  capacity : USize
  mark : UInt8 := 0

public def BytesRepr.ofList (xs : List Nat) : BytesRepr :=
  ⟨xs, xs.length.toUSize, xs.length.toUSize, 0⟩

public structure StringRepr where
  bytes : BytesRepr
  mark : UInt8 := 0

public instance : BEq StringRepr where
  beq a b := a.bytes.data == b.bytes.data

public def StringRepr.encode (s : String) : StringRepr := ⟨.ofList (s.toUTF8.data.toList.map UInt8.toNat), 0⟩

/-- Each string owns a distinct record whose first field is its UTF-8 byte array. -/
public def checkStrictString (env : Environment) : IO Unit := do
  checkStrictBytes env
  unless (impureTrivialStructureInfoExt.find? env `Omega.String) matches some none do
    throw <| IO.userError "String must preserve its runtime identity"
  let some ctor := ctorLayoutExt.find? env `Omega.String.ofByteArray | throw <| IO.userError "missing string constructor"
  unless ctor.ctorInfo.cidx == 0 && ctor.ctorInfo.size == 1 && ctor.ctorInfo.usize == 0 &&
      ctor.ctorInfo.ssize == 1 && (ctor.fieldInfo matches #[.object 0 _, .erased]) do
    throw <| IO.userError "unexpected strict String layout"

/-- The native state adapters construct ST.Out with the result followed by the strict world. -/
public unsafe def installStateLayout (lib : System.FilePath) (env : Environment) : IO Unit := do
  let state ← compileLayouts env `Omega.ST.Out
  let some pair := ctorLayoutExt.find? state `Omega.ST.Out.mk | throw <| IO.userError "missing ST.Out layout"
  let #[.object 0 _, .object 1 _] := pair.fieldInfo | throw <| IO.userError "ST.Out must retain value and world"
  unless pair.ctorInfo.cidx == 0 && pair.ctorInfo.size == 2 && pair.ctorInfo.usize == 0 && pair.ctorInfo.ssize == 0 do
    throw <| IO.userError "ST.Out result disagrees with the native state adapter"
  writeCode lib `OmegaInit.System.ST state layouts

/-- Emit the compiled entry points with their native initialization dependencies. -/
public def emitBridge (compiled : Environment) (owner : Name) (runtime : Option System.FilePath)
    (output : System.FilePath) (imports : Array Import := #[]) : IO Unit := do
  let env := Environment.ofKernelEnv {compiled.toKernelEnv with header.imports := imports, header.isModule := true}
  -- C emission consults the attribute state for calls made inside boxed wrappers.
  let env := (externAttr.ext.setState env (externAttr.ext.getState compiled)).setModulePackage compiled.getModulePackage?
  let c ← (emitC owner).toIO' {fileName := "<strict runtime entry points>", fileMap := default} {env}
  let source ← match runtime with
    | some file => pure <| c ++ "\n" ++ (← IO.FS.readFile file)
    | none => pure c
  IO.FS.writeFile output source

end OmegaChecks.InitPort.NativeState
