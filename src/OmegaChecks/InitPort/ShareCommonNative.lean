module
import all Lean.Environment
import all Lean.OriginalConstKind
import all Lean.Compiler.LCNF.ToImpureType
import all Lean.Compiler.LCNF.MonoTypes
import Lean.Compiler.LCNF.EmitC
import OmegaChecks.InitPort.NativeState
meta import OmegaChecks.InitPort.NativeState
import OmegaChecks.InitPort.LogicalHandle
meta import OmegaChecks.InitPort.LogicalHandle

open Lean OmegaChecks.InitPort

/-- Bind the opaque state allocator to its pinned implementation and keep the same sharing operation. -/
public unsafe def main (args : List String) : IO Unit := do
  let (interpreter, args) := if args.head? == some "--interpreter" then (true, args.drop 1) else (false, args)
  let [lib, output] := args | throw <| IO.userError "expected strict library and C output"
  let api := LogicalHandle.shareState
  let official ← importModules #[{module := api.owner}] {}
  let factory := LogicalHandle.shareFactory
  for (handle, expected, input) in [(api, `ShareCommon.mkStateImpl, IR.IRType.tobject),
      (factory, `ShareCommon.StateFactory.mkImpl, .object)] do
    let some impl := Compiler.getImplementedBy? official handle.allocator | throw <| IO.userError s!"missing implementation of {handle.allocator}"
    let some (.fdecl _ params .tobject _ _) := IR.findEnvDecl official impl | throw <| IO.userError s!"missing native implementation {impl}"
    unless impl == expected && params.map (fun a => (a.ty, a.borrow)) == #[(input, false)] &&
        impl.mangle (pre := "l_") == handle.nativeAllocator do
      throw <| IO.userError s!"unexpected native ABI for {handle.allocator}"
  let share := `ShareCommon.State.shareCommon
  let shareSymbol := "lean_state_sharecommon"
  let shareArgs := #[(IR.IRType.erased, false), (.tobject, true), (.tobject, false), (.tobject, false)]
  NativeState.verify official share shareArgs .object shareSymbol
  let eq := `ShareCommon.Object.eq
  let hash := `ShareCommon.Object.hash
  let borrowed := (IR.IRType.tobject, true)
  NativeState.verify official eq #[borrowed, borrowed] .uint8 "lean_sharecommon_eq"
  NativeState.verify official hash #[borrowed] .uint64 "lean_sharecommon_hash"
  searchPathRef.set [lib]
  let env ← importModules #[{module := api.privateOwner, importAll := true}] {}
  let entries : List (Name × String × Array (IR.IRType × Bool) × IR.IRType) := [
    (api.allocator, api.nativeAllocator, #[(.tobject, false)], .tobject),
    (factory.allocator, "omega_share_common_factory_mk", #[(.object, false)], .tobject),
    (share, shareSymbol, shareArgs, .object),
    (eq, "lean_sharecommon_eq", #[borrowed, borrowed], .uint8),
    (hash, "omega_share_common_object_hash", #[borrowed], .tobject)]
  let roots := entries.filter fun (n, _) => env.contains (`Omega ++ n)
  if roots.isEmpty then return
  if env.contains (`Omega ++ eq) || env.contains (`Omega ++ hash) then
    for (e, name) in [(official, `NonScalar), (env, `Omega.NonScalar)] do
      NativeState.checkErasedField e name
    if env.contains (`Omega ++ hash) then
      NativeState.checkNativeNat env
      for name in [`Omega.UInt64, `Omega.BitVec, `Omega.Fin] do
        NativeState.checkErasedField env name
  if !interpreter && env.contains (`Omega ++ factory.allocator) then
    for name in [`Omega.BEq, `Omega.Hashable] do
      if (Compiler.LCNF.monoTypeExt.find? env name).isNone then
        let built ← NativeState.compileLayouts env name
        NativeState.writeCode lib env.header.moduleNames[(env.getModuleIdxFor? name).get!]! built NativeState.layouts
    let env ← importModules #[{module := api.privateOwner, importAll := true}] {}
    NativeState.checkNativeNat env
    for (n, ctor) in [(`Omega.UInt64, `ofBitVec), (`Omega.BitVec, `ofFin), (`Omega.Fin, `mk),
        (`Omega.Hashable, `mk), (`Omega.BEq, `mk)] do
      let some (some info) := Compiler.LCNF.impureTrivialStructureInfoExt.find? env n
        | throw <| IO.userError s!"{n} must erase to its data field"
      unless info.ctorName == n ++ ctor && info.fieldIdx == 0 do
        throw <| IO.userError s!"unexpected erased representation for {n}"
    let builder := `Omega.ShareCommon.StateFactoryBuilder
    let built ← NativeState.compileLayouts env builder
    let some layout := Compiler.LCNF.ctorLayoutExt.find? built (builder ++ `mk) | throw <| IO.userError "missing strict factory builder layout"
    let some upstream := Compiler.LCNF.ctorLayoutExt.find? official `ShareCommon.StateFactoryBuilder.mk | throw <| IO.userError "missing official factory builder layout"
    for info in [layout, upstream] do
      let #[.erased, .object 0 _, .object 1 _, .object 2 _, .erased,
          .object 3 _, .object 4 _, .object 5 _] := info.fieldInfo
        | throw <| IO.userError "factory callbacks differ from the native field order"
      unless info.ctorInfo.cidx == 0 && info.ctorInfo.size == 6 && info.ctorInfo.usize == 0 && info.ctorInfo.ssize == 0 do
        throw <| IO.userError "factory builder differs from the six-callback native layout"
    NativeState.writeCode lib api.privateOwner built NativeState.layouts
  let env ← importModules #[{module := api.privateOwner, importAll := true}] {}
  let wrappers := [`ShareCommon.instInhabitedState, `ShareCommonT.run, `ShareCommonM.run].map (`Omega ++ ·)
  let wrappers := if interpreter then [] else wrappers.filter env.contains
  let names := roots.map (fun (n, _) => `Omega ++ n) ++ wrappers
  let ctx ← NativeState.localEnv env api.privateOwner names.toArray
  let compiled ← NativeState.compile ctx do
    for (n, symbol, _, _) in roots do
      let strict := `Omega ++ n
      modifyEnv fun e => externAttr.ext.addEntry (asyncDecl := strict) e (strict, ⟨[.standard `all symbol]⟩)
      (← compileDeclsRef.get) #[strict] {}
    for strict in wrappers do
      modifyEnv fun e => privateConstKindsExt.insert e strict .defn
      (← compileDeclsRef.get) #[strict] {}
  for (n, symbol, args, result) in roots do
    NativeState.verify compiled (`Omega ++ n) args result symbol
  let runtime := "src/OmegaChecks/InitPort/share_common_runtime.c"
  if interpreter then
    NativeState.emitBridge compiled `StrictShareCommonInterpreter runtime output
  else
    NativeState.writeCode lib api.privateOwner compiled (NativeState.codeExtensions ++ #[privateConstKindsExt.name])
    NativeState.emitBridge compiled api.privateOwner runtime output #[{module := `OmegaInit.Control.State}]
